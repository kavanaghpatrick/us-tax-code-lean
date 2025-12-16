#!/usr/bin/env python3
"""
Parallel Lean Proof Checker - Prototype

⚠️ DEPRECATED: Use simple_lean_checker.py instead (FIX #60)

KNOWN ISSUE #60 - Race Condition:
  This implementation has a critical race condition where multiple workers
  run `lake build` simultaneously, fighting over the .lake/build directory.
  Result: SLOWER than sequential due to lock contention!

  Lake itself is already parallel (uses multiple threads).
  Running 8 workers × lake's threads = 64+ threads fighting for locks.

RECOMMENDATION:
  Use simple_lean_checker.py which calls `lake build` ONCE and lets
  lake handle parallelism internally (no race conditions, faster).

This file is kept for reference only.

Usage:
    python3 parallel_lean_checker.py [--workers 8]
"""

import argparse
import subprocess
import time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from typing import List, Tuple
import json

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"


@dataclass
class CheckResult:
    """Result of checking a Lean file"""
    file: Path
    success: bool
    errors: List[str]
    warnings: List[str]
    duration: float


def check_lean_file(lean_file: Path) -> CheckResult:
    """
    Check a single Lean file for errors.

    This runs `lake build` on the specific file and captures errors.

    FIX #65: Streams output to temp file to prevent OOM on large outputs.
    """
    start = time.time()
    import tempfile

    try:
        # FIX #65: Stream stdout/stderr to temp files to prevent OOM
        with tempfile.NamedTemporaryFile(mode='w+', delete=False) as stdout_file, \
             tempfile.NamedTemporaryFile(mode='w+', delete=False) as stderr_file:

            # Run lake build on specific file
            result = subprocess.run(
                ['lake', 'build', lean_file.stem],
                cwd=PROJECT_ROOT,
                stdout=stdout_file,
                stderr=stderr_file,
                text=True,
                timeout=60
            )

            # Read stderr (limited to 1MB to prevent OOM)
            stderr_file.seek(0)
            MAX_OUTPUT_SIZE = 1024 * 1024  # 1MB
            stderr_content = stderr_file.read(MAX_OUTPUT_SIZE)

            # Clean up temp files
            Path(stdout_file.name).unlink(missing_ok=True)
            Path(stderr_file.name).unlink(missing_ok=True)

        errors = []
        warnings = []

        # Parse output for errors and warnings
        for line in stderr_content.split('\n'):
            if 'error:' in line.lower():
                errors.append(line.strip())
            elif 'warning:' in line.lower():
                warnings.append(line.strip())

        success = result.returncode == 0 and len(errors) == 0

        duration = time.time() - start

        return CheckResult(
            file=lean_file,
            success=success,
            errors=errors,
            warnings=warnings,
            duration=duration
        )

    except subprocess.TimeoutExpired:
        duration = time.time() - start
        return CheckResult(
            file=lean_file,
            success=False,
            errors=['Timeout after 60 seconds'],
            warnings=[],
            duration=duration
        )
    except Exception as e:
        duration = time.time() - start
        return CheckResult(
            file=lean_file,
            success=False,
            errors=[str(e)],
            warnings=[],
            duration=duration
        )


def check_files_sequential(files: List[Path]) -> List[CheckResult]:
    """Check files one at a time (baseline)"""
    print(f"Checking {len(files)} files sequentially...")
    start = time.time()

    results = []
    for i, file in enumerate(files, 1):
        print(f"  [{i}/{len(files)}] {file.stem}...", end='', flush=True)
        result = check_lean_file(file)
        status = "✓" if result.success else "✗"
        print(f" {status} ({result.duration:.1f}s)")
        results.append(result)

    total_time = time.time() - start
    print(f"\nSequential time: {total_time:.1f}s")

    return results


def check_files_parallel(files: List[Path], num_workers: int) -> List[CheckResult]:
    """Check files in parallel using multiprocessing"""
    print(f"Checking {len(files)} files in parallel ({num_workers} workers)...")
    start = time.time()

    results = []

    with ProcessPoolExecutor(max_workers=num_workers) as executor:
        # Submit all files
        future_to_file = {
            executor.submit(check_lean_file, file): file
            for file in files
        }

        # Collect results as they complete
        completed = 0
        for future in as_completed(future_to_file):
            file = future_to_file[future]
            result = future.result()
            results.append(result)

            completed += 1
            status = "✓" if result.success else "✗"
            print(f"  [{completed}/{len(files)}] {file.stem} {status} ({result.duration:.1f}s)")

    total_time = time.time() - start
    print(f"\nParallel time: {total_time:.1f}s")

    return results


def analyze_results(results: List[CheckResult]):
    """Analyze and print summary of results"""
    total = len(results)
    success_count = sum(1 for r in results if r.success)
    error_count = total - success_count
    total_errors = sum(len(r.errors) for r in results)
    total_warnings = sum(len(r.warnings) for r in results)
    total_duration = sum(r.duration for r in results)
    avg_duration = total_duration / total if total > 0 else 0

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Files checked:     {total}")
    print(f"Success:           {success_count} ({success_count/total*100:.1f}%)")
    print(f"Errors:            {error_count}")
    print(f"Total errors:      {total_errors}")
    print(f"Total warnings:    {total_warnings}")
    print(f"Avg duration:      {avg_duration:.2f}s per file")
    print()

    # Show files with errors
    if error_count > 0:
        print("FILES WITH ERRORS:")
        for result in results:
            if not result.success:
                print(f"\n  {result.file.stem}:")
                for error in result.errors[:3]:  # Show first 3 errors
                    print(f"    - {error[:100]}")
                if len(result.errors) > 3:
                    print(f"    ... and {len(result.errors) - 3} more")


def compare_performance(files: List[Path], num_workers: int):
    """Compare sequential vs parallel performance"""
    # Use subset for quick comparison
    test_files = files[:10]  # Test with 10 files

    print("PERFORMANCE COMPARISON")
    print("=" * 60)
    print()

    # Sequential
    seq_start = time.time()
    seq_results = check_files_sequential(test_files)
    seq_time = time.time() - seq_start

    print()

    # Parallel
    par_start = time.time()
    par_results = check_files_parallel(test_files, num_workers)
    par_time = time.time() - par_start

    print()
    print("=" * 60)
    print("SPEEDUP ANALYSIS")
    print("=" * 60)
    print(f"Sequential time:   {seq_time:.1f}s")
    print(f"Parallel time:     {par_time:.1f}s")
    speedup = seq_time / par_time if par_time > 0 else 0
    print(f"Speedup:           {speedup:.2f}x")
    print()

    if speedup > 1:
        print(f"✓ Parallel is {speedup:.2f}x faster!")
    else:
        print("⚠ No speedup detected (overhead may exceed benefit for small files)")

    # Estimate for full dataset
    if len(files) > len(test_files):
        estimated_seq = (seq_time / len(test_files)) * len(files)
        estimated_par = (par_time / len(test_files)) * len(files)
        print()
        print(f"ESTIMATED FOR ALL {len(files)} FILES:")
        print(f"Sequential:        ~{estimated_seq/60:.1f} minutes")
        print(f"Parallel:          ~{estimated_par/60:.1f} minutes")
        print(f"Time saved:        ~{(estimated_seq - estimated_par)/60:.1f} minutes")


def main():
    parser = argparse.ArgumentParser(description='Parallel Lean proof checker')
    parser.add_argument('--workers', type=int, default=8,
                        help='Number of parallel workers (default: 8)')
    parser.add_argument('--compare', action='store_true',
                        help='Compare sequential vs parallel performance')
    parser.add_argument('--files', type=int, default=0,
                        help='Limit to first N files (0 = all)')

    args = parser.parse_args()

    # Find all Lean files
    lean_files = sorted(TAXCODE_DIR.glob('Section*.lean'))

    if args.files > 0:
        lean_files = lean_files[:args.files]

    if not lean_files:
        print(f"No Lean files found in {TAXCODE_DIR}")
        return

    print(f"Found {len(lean_files)} Lean files")
    print()

    if args.compare:
        compare_performance(lean_files, args.workers)
    else:
        # Just run parallel check
        results = check_files_parallel(lean_files, args.workers)
        analyze_results(results)


if __name__ == '__main__':
    main()
