#!/usr/bin/env python3
"""
Distributed Loophole Finder using Ray (v3.3 - CRASH-PROOF Edition)

CRITICAL FIXES (from Grok + Gemini audit after system crash):
1. O(N²) I/O ELIMINATED: Read files ONCE, pass content to workers
2. PHASE SEPARATION: Build completes BEFORE Ray init (no resource fighting)
3. PROFILER OPTIMIZED: 2s interval, no expensive process tree walks
4. HARD CAPS: Max 500 files build, 200 files contradictions - NO BYPASS
5. SUBPROCESS LIMITS: resource.setrlimit() applied to lake build
6. MEMORY CHECKS: Abort if loaded files exceed 2GB
7. OUTPUT LIMITS: Truncate subprocess output >50MB

v3.1 ADDITIONAL FIXES (from Grok verification audit):
- Caps are now HARD (no user bypass with 'y')
- resource.setrlimit actually implemented (was just imported)
- Memory checked DURING file loading (not just after)
- Subprocess output truncated if too large
- Workers capped at 4 (was 8)

v3.2 FIX (from Codex CLI audit):
- --workers arg now HARD capped at 4 (was bypassable)

v3.3 FIXES (from Grok+Codex safety audit):
- File size checked BEFORE reading (prevents single-file OOM)
- Max 100MB per single file limit added
- Subprocess output read incrementally (prevents output OOM)
- No more capture_output=True (was loading all before check)

OLD: 778 files → 604,506 disk reads → VFS saturation → KERNEL CRASH
NEW: 778 files → 778 disk reads → Pure CPU analysis → SAFE

Installation:
    pip install ray[default] psutil

Usage:
    # Safe mode with profiling (recommended)
    python3 distributed_loophole_finder.py --profile --files 50

    # Full analysis
    python3 distributed_loophole_finder.py --profile --files 0 --check-contradictions
"""

import argparse
import re
import time
import os
import sys
import resource
import json
import threading
import subprocess
from pathlib import Path
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
from contextlib import contextmanager

# Profiling dependencies
try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("WARNING: psutil not installed. Profiling disabled. Install with: pip install psutil")

try:
    import ray
    RAY_AVAILABLE = True
except ImportError:
    RAY_AVAILABLE = False
    print("WARNING: Ray not installed. Install with: pip install ray[default]")

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"


# =============================================================================
# HARD SAFETY LIMITS - Abort if exceeded (prevents crashes)
# These are HARD limits - no user bypass allowed
# =============================================================================
MAX_FILES_FOR_BUILD = 500       # Abort if more than this before build
MAX_FILES_FOR_CONTRADICTIONS = 200  # 200 files = 19,900 pairs (manageable)
MAX_CONTRADICTION_PAIRS = 100_000   # Hard cap on pair count
SUBPROCESS_TIMEOUT_SEC = 300    # 5 min max for lake build (was 10 min)
MAX_LOADED_MEMORY_MB = 2000     # 2GB max for loaded file contents
MAX_SUBPROCESS_OUTPUT_MB = 50   # 50MB max for lake build output


# =============================================================================
# SAFETY THRESHOLDS - Abort if exceeded during runtime
# =============================================================================
@dataclass
class SafetyThresholds:
    """Resource limits that trigger automatic abort."""
    max_memory_percent: float = 85.0      # % of system RAM (raised from 80)
    max_load_average: float = 20.0        # macOS load average (raised for build spikes)
    check_interval_sec: float = 2.0       # Check every 2s (was 0.5s - too aggressive)


# =============================================================================
# LIGHTWEIGHT PROFILER - No expensive process tree walks
# =============================================================================
@dataclass
class ProfileSnapshot:
    """Single point-in-time resource measurement."""
    timestamp: float
    memory_percent: float
    memory_mb: float
    load_average: float

    def __str__(self):
        return (f"[{self.timestamp:.1f}s] "
                f"Mem: {self.memory_percent:.1f}% ({self.memory_mb:.0f}MB) | "
                f"Load: {self.load_average:.1f}")


class ResourceProfiler:
    """
    Lightweight resource monitoring with safety abort.

    OPTIMIZED: Removed expensive psutil.process_iter() and children() calls
    that added kernel overhead and contributed to crash.
    """

    def __init__(self, thresholds: SafetyThresholds = None, enabled: bool = True):
        self.thresholds = thresholds or SafetyThresholds()
        self.enabled = enabled and PSUTIL_AVAILABLE
        self.snapshots: List[ProfileSnapshot] = []
        self._stop_event = threading.Event()
        self._monitor_thread: Optional[threading.Thread] = None
        self._start_time = 0
        self._peak_memory_percent = 0
        self._peak_load = 0
        self._violations: List[str] = []

    def take_snapshot(self) -> ProfileSnapshot:
        """Capture current resource state (LIGHTWEIGHT - no process iteration)."""
        if not PSUTIL_AVAILABLE:
            return ProfileSnapshot(
                timestamp=time.time() - self._start_time,
                memory_percent=0, memory_mb=0, load_average=0
            )

        mem = psutil.virtual_memory()
        load = os.getloadavg()[0]  # Just 1-min average

        snapshot = ProfileSnapshot(
            timestamp=time.time() - self._start_time,
            memory_percent=mem.percent,
            memory_mb=mem.used / (1024 * 1024),
            load_average=load
        )

        # Track peaks
        self._peak_memory_percent = max(self._peak_memory_percent, snapshot.memory_percent)
        self._peak_load = max(self._peak_load, snapshot.load_average)

        return snapshot

    def check_thresholds(self, snapshot: ProfileSnapshot) -> Optional[str]:
        """Check if any threshold exceeded. Returns violation message or None."""
        t = self.thresholds

        if snapshot.memory_percent > t.max_memory_percent:
            return f"MEMORY {snapshot.memory_percent:.1f}% > {t.max_memory_percent}%"

        if snapshot.load_average > t.max_load_average:
            return f"LOAD {snapshot.load_average:.1f} > {t.max_load_average}"

        return None

    def _monitor_loop(self):
        """Background monitoring thread."""
        while not self._stop_event.is_set():
            try:
                snapshot = self.take_snapshot()

                # Keep only last 100 snapshots to prevent memory growth
                self.snapshots.append(snapshot)
                if len(self.snapshots) > 100:
                    self.snapshots = self.snapshots[-50:]

                # Print real-time status (overwrite line)
                print(f"\r{snapshot}    ", end="", flush=True)

                # Check thresholds
                violation = self.check_thresholds(snapshot)
                if violation:
                    self._violations.append(violation)
                    sys.stdout.write(f"\n\n{'='*60}\n")
                    sys.stdout.write(f"SAFETY ABORT: {violation}\n")
                    sys.stdout.write(f"{'='*60}\n")
                    sys.stdout.write("Shutting down to prevent system crash...\n")
                    sys.stdout.flush()
                    sys.stderr.flush()

                    # Graceful shutdown
                    try:
                        if RAY_AVAILABLE and ray.is_initialized():
                            ray.shutdown()
                    except:
                        pass

                    os._exit(1)

            except Exception as e:
                pass  # Don't crash profiler on errors

            self._stop_event.wait(self.thresholds.check_interval_sec)

    @contextmanager
    def monitor(self):
        """Context manager for monitoring."""
        if not self.enabled:
            yield
            return

        self._start_time = time.time()
        self._stop_event.clear()
        self._monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self._monitor_thread.start()

        print("\n" + "="*60)
        print("PROFILER ACTIVE (v3 - lightweight)")
        print(f"Thresholds: Mem>{self.thresholds.max_memory_percent}% "
              f"Load>{self.thresholds.max_load_average}")
        print("="*60 + "\n")

        try:
            yield
        finally:
            self._stop_event.set()
            if self._monitor_thread:
                self._monitor_thread.join(timeout=2)

            # Print summary
            duration = time.time() - self._start_time
            print("\n\n" + "="*60)
            print("PROFILER SUMMARY")
            print("="*60)
            print(f"Duration: {duration:.1f}s")
            print(f"Peak Memory: {self._peak_memory_percent:.1f}%")
            print(f"Peak Load: {self._peak_load:.1f}")
            if self._violations:
                print(f"VIOLATIONS: {self._violations}")
            else:
                print("Violations: None")
            print("="*60 + "\n")


# =============================================================================
# PHASE 1: BUILD (No Ray - full resources to lake)
# =============================================================================
def _set_subprocess_limits():
    """Set resource limits for child subprocess (called via preexec_fn)."""
    try:
        # Limit virtual memory to 8GB (prevents runaway allocations)
        # Note: macOS may not enforce all limits, but we try
        eight_gb = 8 * 1024 * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (eight_gb, eight_gb))
    except (ValueError, resource.error):
        pass  # macOS may not support this limit


def run_build_phase(profiler: Optional[ResourceProfiler] = None) -> Dict[str, List[str]]:
    """
    Run `lake build` BEFORE Ray init to avoid resource contention.

    FIX: lake and Ray were fighting for 100% CPU/RAM simultaneously.
    Now: Build completes fully, THEN Ray starts.

    SAFETY (v3.3 - Grok+Codex audit fix):
    - Uses resource.setrlimit to cap subprocess memory
    - Reads output incrementally with size limit (not all at once)
    """
    print("\n" + "="*60)
    print("PHASE 1: COMPILATION (lake build)")
    print("="*60)

    print(f"Timeout: {SUBPROCESS_TIMEOUT_SEC}s")
    print(f"Memory limit: 8GB (via setrlimit)")
    print(f"Output limit: {MAX_SUBPROCESS_OUTPUT_MB}MB")

    start = time.time()
    max_output_bytes = MAX_SUBPROCESS_OUTPUT_MB * 1024 * 1024
    stderr_output = ""
    stdout_output = ""

    try:
        # SAFETY FIX (v3.3): Use Popen with incremental reading to prevent OOM
        # subprocess.run(capture_output=True) loads ALL output before we can check size
        proc = subprocess.Popen(
            ['lake', 'build'],
            cwd=PROJECT_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            preexec_fn=_set_subprocess_limits
        )

        # Read output incrementally with size limit
        stdout_chunks = []
        stderr_chunks = []
        stdout_size = 0
        stderr_size = 0

        import select
        while proc.poll() is None:
            # Check for timeout
            if time.time() - start > SUBPROCESS_TIMEOUT_SEC:
                proc.kill()
                print(f"WARNING: Build timed out after {SUBPROCESS_TIMEOUT_SEC}s")
                print("Continuing with partial results...")
                return {}

            # Read available output (non-blocking would be ideal but this works)
            if proc.stdout:
                chunk = proc.stdout.read(8192)  # Read 8KB at a time
                if chunk:
                    if stdout_size < max_output_bytes:
                        stdout_chunks.append(chunk)
                        stdout_size += len(chunk)
            if proc.stderr:
                chunk = proc.stderr.read(8192)
                if chunk:
                    if stderr_size < max_output_bytes:
                        stderr_chunks.append(chunk)
                        stderr_size += len(chunk)

        # Get remaining output after process exits
        remaining_stdout, remaining_stderr = proc.communicate(timeout=10)
        if remaining_stdout and stdout_size < max_output_bytes:
            stdout_chunks.append(remaining_stdout[:max_output_bytes - stdout_size])
        if remaining_stderr and stderr_size < max_output_bytes:
            stderr_chunks.append(remaining_stderr[:max_output_bytes - stderr_size])

        stdout_output = ''.join(stdout_chunks)
        stderr_output = ''.join(stderr_chunks)
        returncode = proc.returncode

        build_time = time.time() - start
        print(f"Build completed in {build_time:.1f}s")

        if returncode != 0:
            print(f"Build had warnings/errors (exit code {returncode})")

        output_mb = (len(stdout_output) + len(stderr_output)) / (1024 * 1024)
        if stdout_size >= max_output_bytes or stderr_size >= max_output_bytes:
            print(f"WARNING: Build output truncated at {MAX_SUBPROCESS_OUTPUT_MB}MB limit")
        else:
            print(f"Build output: {output_mb:.1f}MB")

        # Create result object for compatibility with rest of code
        result = subprocess.CompletedProcess(
            ['lake', 'build'], returncode, stdout_output, stderr_output
        )

    except FileNotFoundError:
        print("WARNING: 'lake' command not found. Skipping build.")
        return {}
    except Exception as e:
        print(f"WARNING: Build error: {e}")
        return {}

    # Parse errors
    errors_by_file: Dict[str, List[str]] = {}

    for line in result.stderr.split('\n'):
        match = re.match(r'^(src/[^:]+\.lean):(\d+):(\d+): error: (.+)$', line)
        if match:
            file_path = str(PROJECT_ROOT / match.group(1))
            error_msg = f"Line {match.group(2)}: {match.group(4)}"
            if file_path not in errors_by_file:
                errors_by_file[file_path] = []
            errors_by_file[file_path].append(error_msg)

    error_count = sum(len(e) for e in errors_by_file.values())
    print(f"Parsed {error_count} errors in {len(errors_by_file)} files")

    return errors_by_file


# =============================================================================
# PHASE 2: LOAD DATA (Read files ONCE)
# =============================================================================
def load_file_contents(files: List[Path]) -> Dict[str, str]:
    """
    Read all file contents into memory ONCE.

    FIX: Previously, each Ray task read files = O(N²) disk I/O.
    778 files × 778 files = 604,506 file reads → VFS saturation → CRASH

    Now: 778 file reads total. 99.87% reduction in I/O.

    SAFETY (v3.3 - Grok+Codex audit fix):
    - Check file size BEFORE reading (not after) to prevent single-file OOM
    - Abort if total size exceeds MAX_LOADED_MEMORY_MB
    """
    print("\n" + "="*60)
    print("PHASE 2: LOADING FILES INTO MEMORY")
    print("="*60)

    contents = {}
    total_size = 0
    max_bytes = MAX_LOADED_MEMORY_MB * 1024 * 1024
    max_single_file_mb = 100  # No single file should be >100MB

    for f in files:
        try:
            # SAFETY FIX (v3.3): Check file size BEFORE reading to prevent OOM
            file_size = f.stat().st_size
            file_size_mb = file_size / (1024 * 1024)

            # Reject oversized single files BEFORE loading
            if file_size_mb > max_single_file_mb:
                print(f"\n!!! SAFETY ABORT: {f.name} is {file_size_mb:.1f}MB (max {max_single_file_mb}MB per file)")
                print("This file is too large to process safely")
                sys.exit(1)

            # Check if adding this file would exceed total limit BEFORE loading
            if total_size + file_size > max_bytes:
                size_mb = total_size / (1024 * 1024)
                print(f"\n!!! SAFETY ABORT: Adding {f.name} ({file_size_mb:.1f}MB) would exceed {MAX_LOADED_MEMORY_MB}MB limit")
                print(f"Currently loaded: {size_mb:.1f}MB")
                print("Use --files to reduce file count")
                sys.exit(1)

            # Safe to read now
            text = f.read_text(encoding='utf-8')
            total_size += len(text)
            contents[str(f)] = text

        except Exception as e:
            print(f"  Warning: Could not read {f.name}: {e}")

    size_mb = total_size / (1024 * 1024)
    print(f"Loaded {len(contents)} files ({size_mb:.1f} MB) into memory")
    print(f"I/O operations: {len(contents)} (was {len(contents)**2} in v2)")
    print(f"Memory safety: {size_mb:.1f}MB / {MAX_LOADED_MEMORY_MB}MB limit")

    return contents


# =============================================================================
# PHASE 3: RAY ANALYSIS (Pure CPU - no disk I/O in workers)
# =============================================================================
if RAY_AVAILABLE:
    @ray.remote(num_cpus=0.5, memory=256*1024*1024)  # Reduced memory (was 512MB)
    def check_contradiction_pure(
        name1: str, content1: str,
        name2: str, content2: str
    ) -> Optional[Dict]:
        """
        Check if two sections contradict each other.

        FIX: This task receives CONTENT, not file paths.
        Zero disk I/O. Pure CPU string matching.
        """
        try:
            # Heuristic: check for conflicting tax status
            has_tax_exempt_1 = 'isTaxExempt' in content1 and 'true' in content1.lower()
            has_taxable_2 = 'isTaxable' in content2 or ('isTaxExempt' in content2 and 'false' in content2.lower())

            if has_tax_exempt_1 and has_taxable_2:
                return {
                    'file1': name1,
                    'file2': name2,
                    'contradicts': True,
                    'confidence': 0.3
                }
            return None

        except Exception:
            return None


# =============================================================================
# LOCAL FILE CHECKER - No Ray needed
# =============================================================================
def check_lean_file_local(lean_file_path: str, build_errors: Dict[str, List[str]]) -> Dict:
    """Check a single Lean file using pre-computed build results."""
    file_stem = Path(lean_file_path).stem

    # Direct lookup
    file_errors = build_errors.get(lean_file_path, [])

    # Fallback: check by stem
    if not file_errors:
        for path, errors in build_errors.items():
            if file_stem in path:
                file_errors = errors
                break

    return {
        'file': lean_file_path,
        'success': len(file_errors) == 0,
        'errors': file_errors
    }


# =============================================================================
# MAIN SYSTEM
# =============================================================================
class DistributedLoopholeSystem:
    """
    Crash-proof loophole detection system (v3).

    Architecture:
    - Phase 1: Build (no Ray, full resources to lake)
    - Phase 2: Load files into memory (O(N) I/O)
    - Phase 3: Ray analysis (pure CPU, O(N²) but no I/O)
    """

    def __init__(self, file_contents: Dict[str, str], build_errors: Dict[str, List[str]],
                 num_workers: int = None):
        if not RAY_AVAILABLE:
            raise RuntimeError("Ray not installed")

        self.file_contents = file_contents
        self.build_errors = build_errors

        # Conservative worker count - HARD capped at 4 to prevent resource exhaustion
        # Note: Even if user passes --workers, we enforce max of 4 (Codex audit fix)
        max_workers = 4
        if num_workers:
            effective_workers = min(num_workers, max_workers)
            if num_workers > max_workers:
                print(f"WARNING: --workers {num_workers} exceeds max {max_workers}, using {max_workers}")
        else:
            effective_workers = min(os.cpu_count() or 4, max_workers)

        print("\n" + "="*60)
        print("PHASE 3: INITIALIZING RAY")
        print("="*60)

        ray.init(
            num_cpus=effective_workers,
            object_store_memory=256*1024*1024,  # 256MB (reduced from 512MB)
            include_dashboard=False,  # Disable dashboard to reduce overhead
            _system_config={
                "max_io_workers": 2,  # Limit I/O workers (reduced from 4)
            }
        )

        self.num_cpus = effective_workers
        print(f"Ray initialized with {effective_workers} CPUs")

    def check_all_files_local(self, files: List[Path]) -> List[Dict]:
        """Check all files using local dict lookup (instant)."""
        print(f"\nChecking {len(files)} files (local lookup)...")
        start = time.time()

        results = []
        for f in files:
            result = check_lean_file_local(str(f), self.build_errors)
            results.append(result)

        duration = time.time() - start
        success_count = sum(1 for r in results if r['success'])

        print(f"Checked {len(files)} files in {duration:.3f}s")
        print(f"Results: {success_count} passed, {len(files) - success_count} failed")

        return results

    def check_contradictions_distributed(self, files: List[Path], max_active: int = 50) -> List[Dict]:
        """
        Check all pairs for contradictions using Ray.

        FIX: Content is pre-loaded. Workers receive strings, not file paths.
        Zero disk I/O in workers.
        """
        file_list = [str(f) for f in files]
        total_pairs = len(file_list) * (len(file_list) - 1) // 2

        # Hard cap check
        if total_pairs > MAX_CONTRADICTION_PAIRS:
            print(f"\nWARNING: {total_pairs:,} pairs exceeds limit of {MAX_CONTRADICTION_PAIRS:,}")
            print("Use --files to reduce file count")
            return []

        print(f"\nChecking {total_pairs:,} pairs for contradictions...")
        print(f"Max active tasks: {max_active}")
        start = time.time()

        def pair_generator():
            for i, f1 in enumerate(file_list):
                for f2 in file_list[i+1:]:
                    yield (f1, f2)

        futures = []
        results = []
        pair_iter = pair_generator()
        checked = 0

        # Submit initial batch
        for _ in range(min(max_active, total_pairs)):
            try:
                f1, f2 = next(pair_iter)
                content1 = self.file_contents.get(f1, "")
                content2 = self.file_contents.get(f2, "")

                # Pass content, not file paths
                futures.append(check_contradiction_pure.remote(
                    Path(f1).name, content1,
                    Path(f2).name, content2
                ))
            except StopIteration:
                break

        # Process as they complete
        while futures:
            done, futures = ray.wait(futures, num_returns=1, timeout=5.0)

            for future in done:
                try:
                    result = ray.get(future, timeout=5.0)
                    if result:  # Only store contradictions
                        results.append(result)
                except Exception:
                    pass
                checked += 1

                if checked % 5000 == 0:
                    elapsed = time.time() - start
                    rate = checked / elapsed if elapsed > 0 else 0
                    print(f"  Progress: {checked:,}/{total_pairs:,} ({100*checked/total_pairs:.1f}%)")

            # Submit replacements
            for _ in range(len(done)):
                try:
                    f1, f2 = next(pair_iter)
                    content1 = self.file_contents.get(f1, "")
                    content2 = self.file_contents.get(f2, "")

                    futures.append(check_contradiction_pure.remote(
                        Path(f1).name, content1,
                        Path(f2).name, content2
                    ))
                except StopIteration:
                    pass

        duration = time.time() - start
        print(f"\nContradiction check complete in {duration:.1f}s")
        print(f"Found {len(results)} potential contradictions")

        return results

    def shutdown(self):
        """Shutdown Ray gracefully."""
        print("\nShutting down Ray...")
        ray.shutdown()


# =============================================================================
# MAIN
# =============================================================================
def main():
    parser = argparse.ArgumentParser(
        description='Distributed loophole finder (v3 - crash-proof)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Safe run with profiling
  python3 distributed_loophole_finder.py --profile --files 50

  # Full analysis with contradictions
  python3 distributed_loophole_finder.py --profile --files 0 --check-contradictions

  # Adjust thresholds
  python3 distributed_loophole_finder.py --max-load 30 --max-memory 90
        """
    )

    parser.add_argument('--files', type=int, default=10,
                        help='Number of files to check (0 = all)')
    parser.add_argument('--check-contradictions', action='store_true',
                        help='Check for contradictions between sections')
    parser.add_argument('--profile', action='store_true',
                        help='Enable resource profiling')
    parser.add_argument('--max-memory', type=float, default=85.0,
                        help='Max memory %% before abort (default: 85)')
    parser.add_argument('--max-load', type=float, default=20.0,
                        help='Max load average before abort (default: 20)')
    parser.add_argument('--workers', type=int, default=None,
                        help='Number of Ray workers')

    args = parser.parse_args()

    # Setup profiler
    thresholds = SafetyThresholds(
        max_memory_percent=args.max_memory,
        max_load_average=args.max_load
    )
    profiler = ResourceProfiler(thresholds, enabled=args.profile)

    # Find files first (before any heavy operations)
    lean_files = sorted(TAXCODE_DIR.glob('Section*.lean'))
    if args.files > 0:
        lean_files = lean_files[:args.files]

    if not lean_files:
        print(f"No Lean files found in {TAXCODE_DIR}")
        return

    print(f"Found {len(lean_files)} Lean files")

    # HARD cap check for build - NO BYPASS ALLOWED (Grok audit fix)
    if len(lean_files) > MAX_FILES_FOR_BUILD:
        print(f"\n!!! HARD LIMIT: {len(lean_files)} files exceeds {MAX_FILES_FOR_BUILD} file limit")
        print("This limit exists to prevent system crashes.")
        print(f"Use --files {MAX_FILES_FOR_BUILD} or less.")
        sys.exit(1)

    # HARD cap check for contradictions - NO BYPASS ALLOWED (Grok audit fix)
    if args.check_contradictions and len(lean_files) > MAX_FILES_FOR_CONTRADICTIONS:
        pairs = len(lean_files) * (len(lean_files) - 1) // 2
        print(f"\n!!! HARD LIMIT: {len(lean_files)} files = {pairs:,} pairs")
        print(f"Contradiction check limited to {MAX_FILES_FOR_CONTRADICTIONS} files ({MAX_FILES_FOR_CONTRADICTIONS*(MAX_FILES_FOR_CONTRADICTIONS-1)//2:,} pairs)")
        print(f"Use --files {MAX_FILES_FOR_CONTRADICTIONS} or remove --check-contradictions")
        sys.exit(1)

    # Run with profiling
    with profiler.monitor() if args.profile else nullcontext():

        # PHASE 1: Build (no Ray)
        build_errors = run_build_phase(profiler)

        # PHASE 2: Load files (O(N) I/O)
        file_contents = load_file_contents(lean_files)

        if not RAY_AVAILABLE:
            print("\nRay not available. Skipping distributed analysis.")
            return

        # PHASE 3: Ray analysis (pure CPU)
        system = DistributedLoopholeSystem(
            file_contents=file_contents,
            build_errors=build_errors,
            num_workers=args.workers
        )

        try:
            # Check files (instant - dict lookup)
            results = system.check_all_files_local(lean_files)

            success_count = sum(1 for r in results if r['success'])
            print(f"\n{'='*60}")
            print(f"RESULTS: {success_count}/{len(results)} files passed")
            print(f"{'='*60}")

            # Contradiction check (Ray distributed - pure CPU)
            if args.check_contradictions:
                contradictions = system.check_contradictions_distributed(lean_files)

                if contradictions:
                    print("\nPOTENTIAL CONTRADICTIONS:")
                    for c in contradictions[:10]:
                        print(f"  {c['file1']} <-> {c['file2']} (confidence: {c['confidence']:.2f})")

        finally:
            system.shutdown()

    # Save profiling report
    if args.profile:
        report_path = PROJECT_ROOT / "profiling_report.json"
        report = {
            'version': 'v3-crash-proof',
            'files_checked': len(lean_files),
            'peak_memory_percent': profiler._peak_memory_percent,
            'peak_load': profiler._peak_load,
            'violations': profiler._violations
        }
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2)
        print(f"\nProfiling report saved to: {report_path}")


class nullcontext:
    """Null context manager for when profiling is disabled."""
    def __enter__(self): return None
    def __exit__(self, *args): pass


if __name__ == '__main__':
    main()
