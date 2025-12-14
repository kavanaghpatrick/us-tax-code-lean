#!/usr/bin/env python3
"""
Safe Loophole Finder (v2.0 - Comprehensive Detection Edition)

Based on Grok + Codex recommendations after Ray-based approach crashed Mac.
v2.0 adds comprehensive contradiction detection based on codebase analysis.

ARCHITECTURE:
- ZERO parallelism (no Ray, no multiprocessing, no async)
- Single-threaded sequential processing
- Chunked with explicit sleeps between chunks
- Progress saved to disk for resumability
- Pure Python (only stdlib + optional psutil)

DETECTION PATTERNS (v2.0):
1. Type definition inconsistencies (Currency, FilingStatus, TaxYear)
2. Numeric threshold conflicts (different limits for same concept)
3. Deprecated function references (functions marked DEPRECATED still called)
4. Incomplete implementations (sorry, TODO, admit)
5. Overlapping boolean conditions (jurisdiction conflicts)
6. Original isTaxExempt/isTaxable heuristic

Usage:
    python3 safe_loophole_finder.py                    # Run all checks
    python3 safe_loophole_finder.py --resume           # Resume from progress
    python3 safe_loophole_finder.py --files 100        # Limit files
    python3 safe_loophole_finder.py --chunk-size 500   # Smaller chunks
"""

import argparse
import gc
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"
COMMON_DIR = PROJECT_ROOT / "src" / "Common"
PROGRESS_FILE = PROJECT_ROOT / "loophole_progress.json"

# Safety configuration
DEFAULT_CHUNK_SIZE = 1000       # Pairs per chunk
DEFAULT_SLEEP_BETWEEN = 0.5    # Seconds between chunks
DEFAULT_SLEEP_EVERY_N = 100    # Sleep briefly every N items in a chunk


def load_progress() -> Dict:
    """Load saved progress or return empty state."""
    if PROGRESS_FILE.exists():
        try:
            with open(PROGRESS_FILE) as f:
                return json.load(f)
        except Exception:
            pass
    return {
        "file_errors": {},
        "pairs_checked": 0,
        "contradictions": [],
        "type_issues": [],
        "threshold_issues": [],
        "deprecated_issues": [],
        "incomplete_issues": [],
        "completed": False
    }


def save_progress(progress: Dict):
    """Save progress to disk for resumability."""
    with open(PROGRESS_FILE, 'w') as f:
        json.dump(progress, f, indent=2)


def run_build() -> Dict[str, List[str]]:
    """
    Run lake build and parse errors.
    Single subprocess with timeout - safe.
    """
    print("\n" + "="*60)
    print("PHASE 1: COMPILATION")
    print("="*60)

    start = time.time()

    try:
        result = subprocess.run(
            ['lake', 'build'],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=300  # 5 min max
        )
        print(f"Build completed in {time.time()-start:.1f}s")
    except subprocess.TimeoutExpired:
        print("Build timed out after 300s")
        return {}
    except FileNotFoundError:
        print("'lake' not found, skipping build")
        return {}

    # Parse errors
    errors = {}
    for line in result.stderr.split('\n'):
        match = re.match(r'^(src/[^:]+\.lean):(\d+):(\d+): error: (.+)$', line)
        if match:
            path = str(PROJECT_ROOT / match.group(1))
            if path not in errors:
                errors[path] = []
            errors[path].append(f"Line {match.group(2)}: {match.group(4)}")

    print(f"Found {sum(len(e) for e in errors.values())} errors in {len(errors)} files")
    return errors


def load_files(max_files: int = 0) -> List[Path]:
    """Load Lean files to check."""
    files = sorted(TAXCODE_DIR.glob('Section*.lean'))
    if max_files > 0:
        files = files[:max_files]
    return files


def load_file_contents(files: List[Path]) -> Dict[str, str]:
    """
    Load all file contents into memory.
    Sequential, single-threaded, safe.
    """
    print("\n" + "="*60)
    print("PHASE 2: LOADING FILES")
    print("="*60)

    contents = {}
    total_size = 0

    for i, f in enumerate(files):
        try:
            text = f.read_text()
            contents[str(f)] = text
            total_size += len(text)

            # Progress indicator
            if (i + 1) % 100 == 0:
                print(f"  Loaded {i+1}/{len(files)} files...")

        except Exception as e:
            print(f"  Warning: {f.name}: {e}")

    print(f"Loaded {len(contents)} files ({total_size/1024/1024:.1f} MB)")
    return contents


def check_file_errors(files: List[Path], build_errors: Dict[str, List[str]]) -> Dict[str, bool]:
    """
    Check files for errors using dict lookup.
    Instant, no CPU pressure.
    """
    print("\n" + "="*60)
    print("PHASE 3: CHECKING FILE ERRORS")
    print("="*60)

    results = {}
    for f in files:
        path = str(f)
        has_errors = path in build_errors and len(build_errors[path]) > 0
        results[path] = not has_errors  # True = passed

    passed = sum(1 for v in results.values() if v)
    print(f"Results: {passed}/{len(results)} files passed")

    return results


# =============================================================================
# TYPE DEFINITION DETECTION (v2.0)
# =============================================================================

def extract_type_definitions(content: str, filename: str) -> Dict[str, List[Dict]]:
    """Extract type definitions from a Lean file."""
    definitions = {
        'Currency': [],
        'FilingStatus': [],
        'TaxYear': [],
        'TaxRate': [],
    }

    lines = content.split('\n')
    for i, line in enumerate(lines):
        # Currency definitions
        if re.search(r'def\s+Currency\s*:?=', line) or re.search(r'abbrev\s+Currency\s*:?=', line):
            definitions['Currency'].append({
                'file': filename,
                'line': i + 1,
                'content': line.strip()
            })

        # FilingStatus definitions
        if re.search(r'inductive\s+FilingStatus', line) or re.search(r'structure\s+FilingStatus', line):
            # Count variants in next ~10 lines
            variants = []
            for j in range(i, min(i+15, len(lines))):
                var_match = re.search(r'\|\s*(\w+)', lines[j])
                if var_match:
                    variants.append(var_match.group(1))
            definitions['FilingStatus'].append({
                'file': filename,
                'line': i + 1,
                'variants': variants,
                'variant_count': len(variants)
            })

        # TaxYear definitions
        if re.search(r'structure\s+TaxYear', line) or re.search(r'def\s+TaxYear\s*:?=', line):
            definitions['TaxYear'].append({
                'file': filename,
                'line': i + 1,
                'content': line.strip()
            })

    return definitions


def check_type_consistency(contents: Dict[str, str]) -> List[Dict]:
    """Check for inconsistent type definitions across files."""
    all_definitions = {
        'Currency': [],
        'FilingStatus': [],
        'TaxYear': [],
        'TaxRate': [],
    }

    for filepath, content in contents.items():
        filename = Path(filepath).name
        defs = extract_type_definitions(content, filename)
        for type_name, type_defs in defs.items():
            all_definitions[type_name].extend(type_defs)

    issues = []

    # Check FilingStatus variant consistency
    fs_defs = all_definitions['FilingStatus']
    if len(fs_defs) > 1:
        variant_counts = set(d.get('variant_count', 0) for d in fs_defs)
        if len(variant_counts) > 1:
            issues.append({
                'type': 'type_inconsistency',
                'category': 'FilingStatus',
                'severity': 'HIGH',
                'message': f"FilingStatus has {len(variant_counts)} different variant counts: {variant_counts}",
                'locations': [f"{d['file']}:{d['line']}" for d in fs_defs]
            })

    # Check Currency definition consistency
    curr_defs = all_definitions['Currency']
    if len(curr_defs) > 1:
        unique_contents = set(d.get('content', '') for d in curr_defs)
        if len(unique_contents) > 1:
            issues.append({
                'type': 'type_inconsistency',
                'category': 'Currency',
                'severity': 'MEDIUM',
                'message': f"Currency has {len(unique_contents)} different definitions",
                'definitions': list(unique_contents)[:5]
            })

    # Report duplicate definitions (even if consistent)
    for type_name, defs in all_definitions.items():
        if len(defs) > 5:  # More than 5 duplicates is concerning
            issues.append({
                'type': 'duplicate_definition',
                'category': type_name,
                'severity': 'LOW',
                'message': f"{type_name} defined {len(defs)} times instead of importing from Common.Basic",
                'count': len(defs)
            })

    return issues


# =============================================================================
# THRESHOLD CONFLICT DETECTION (v2.0)
# =============================================================================

def extract_thresholds(content: str, filename: str) -> List[Dict]:
    """Extract numeric thresholds from a Lean file."""
    thresholds = []
    lines = content.split('\n')

    for i, line in enumerate(lines):
        # Match definitions with large numbers (likely dollar amounts)
        matches = re.findall(r'(def|let)\s+(\w+)\s*:\s*\w*\s*:?=\s*(\d{4,})', line)
        for match in matches:
            keyword, name, value = match
            thresholds.append({
                'file': filename,
                'line': i + 1,
                'name': name,
                'value': int(value),
                'context': line.strip()[:80]
            })

        # Match percentage thresholds (0.X or X% patterns)
        pct_matches = re.findall(r'(def|let)\s+(\w+)\s*[^=]*=\s*(0\.\d+|\d+)\s*--.*[pP]ercent', line)
        for match in pct_matches:
            keyword, name, value = match
            thresholds.append({
                'file': filename,
                'line': i + 1,
                'name': name,
                'value': float(value),
                'is_percentage': True,
                'context': line.strip()[:80]
            })

    return thresholds


def check_threshold_conflicts(contents: Dict[str, str]) -> List[Dict]:
    """Check for conflicting thresholds across files."""
    all_thresholds = []

    for filepath, content in contents.items():
        filename = Path(filepath).name
        all_thresholds.extend(extract_thresholds(content, filename))

    issues = []

    # Group by similar names
    name_groups = {}
    for t in all_thresholds:
        # Normalize name (lowercase, remove underscores)
        normalized = t['name'].lower().replace('_', '')
        if normalized not in name_groups:
            name_groups[normalized] = []
        name_groups[normalized].append(t)

    # Check for conflicts in same-named thresholds
    for name, group in name_groups.items():
        if len(group) > 1:
            values = set(t['value'] for t in group)
            if len(values) > 1:
                issues.append({
                    'type': 'threshold_conflict',
                    'name': name,
                    'severity': 'HIGH',
                    'message': f"Threshold '{name}' has conflicting values: {values}",
                    'locations': [f"{t['file']}:{t['line']}" for t in group]
                })

    return issues


# =============================================================================
# DEPRECATED FUNCTION DETECTION (v2.0)
# =============================================================================

def extract_deprecated_functions(content: str, filename: str) -> Tuple[List[str], List[str]]:
    """Extract deprecated functions and all function calls."""
    deprecated = []
    function_calls = []

    lines = content.split('\n')
    for i, line in enumerate(lines):
        # Find DEPRECATED markers
        if 'DEPRECATED' in line.upper() or 'deprecated' in line:
            # Look for function name on same or next line
            for j in range(i, min(i+3, len(lines))):
                func_match = re.search(r'def\s+(\w+)', lines[j])
                if func_match:
                    deprecated.append(func_match.group(1))
                    break

        # Find all function calls (identifier followed by parentheses or arguments)
        calls = re.findall(r'(?:^|[^a-zA-Z])([a-z][a-zA-Z0-9_]*)\s*(?:\(|[a-zA-Z])', line)
        function_calls.extend(calls)

    return deprecated, function_calls


def check_deprecated_usage(contents: Dict[str, str]) -> List[Dict]:
    """Check for deprecated functions still being used."""
    all_deprecated = set()
    all_calls = {}  # function -> [files that call it]

    for filepath, content in contents.items():
        filename = Path(filepath).name
        deprecated, calls = extract_deprecated_functions(content, filename)
        all_deprecated.update(deprecated)
        for call in calls:
            if call not in all_calls:
                all_calls[call] = []
            if filename not in all_calls[call]:
                all_calls[call].append(filename)

    issues = []
    for deprecated_func in all_deprecated:
        if deprecated_func in all_calls:
            callers = all_calls[deprecated_func]
            if len(callers) > 1:  # Called from multiple files
                issues.append({
                    'type': 'deprecated_usage',
                    'function': deprecated_func,
                    'severity': 'HIGH',
                    'message': f"Deprecated function '{deprecated_func}' still called from {len(callers)} files",
                    'callers': callers[:5]
                })

    return issues


# =============================================================================
# INCOMPLETE IMPLEMENTATION DETECTION (v2.0)
# =============================================================================

def check_incomplete_implementations(contents: Dict[str, str]) -> List[Dict]:
    """Check for sorry, TODO, and admit markers."""
    issues = []

    sorry_files = []
    todo_files = []
    admit_files = []

    for filepath, content in contents.items():
        filename = Path(filepath).name

        # Count sorries
        sorry_count = len(re.findall(r'\bsorry\b', content))
        if sorry_count > 0:
            sorry_files.append({'file': filename, 'count': sorry_count})

        # Count TODOs
        todo_count = len(re.findall(r'TODO', content))
        if todo_count > 0:
            todo_files.append({'file': filename, 'count': todo_count})

        # Count admits
        admit_count = len(re.findall(r'\badmit\b', content))
        if admit_count > 0:
            admit_files.append({'file': filename, 'count': admit_count})

    if sorry_files:
        total_sorries = sum(f['count'] for f in sorry_files)
        issues.append({
            'type': 'incomplete_proof',
            'category': 'sorry',
            'severity': 'MEDIUM',
            'message': f"{total_sorries} unproven theorems (sorry) in {len(sorry_files)} files",
            'files': [f['file'] for f in sorted(sorry_files, key=lambda x: -x['count'])[:10]]
        })

    if todo_files:
        total_todos = sum(f['count'] for f in todo_files)
        issues.append({
            'type': 'incomplete_impl',
            'category': 'TODO',
            'severity': 'LOW',
            'message': f"{total_todos} TODOs in {len(todo_files)} files",
            'files': [f['file'] for f in sorted(todo_files, key=lambda x: -x['count'])[:10]]
        })

    return issues


# =============================================================================
# PAIRWISE CONTRADICTION DETECTION (v2.0 - Enhanced)
# =============================================================================

def check_contradiction(content1: str, content2: str, file1: str, file2: str) -> List[Dict]:
    """
    Check if two file contents have contradictions.
    Pure CPU operation, no I/O.

    v2.0 adds multiple detection patterns.
    """
    contradictions = []

    # Pattern 1: Original isTaxExempt vs isTaxable (keep for compatibility)
    has_exempt_1 = 'isTaxExempt' in content1 and 'true' in content1.lower()
    has_taxable_2 = 'isTaxable' in content2 or ('isTaxExempt' in content2 and 'false' in content2.lower())
    if has_exempt_1 and has_taxable_2:
        contradictions.append({
            'pattern': 'exempt_vs_taxable',
            'file1': file1,
            'file2': file2,
            'confidence': 0.3,
            'description': 'isTaxExempt=true vs isTaxable (may be different contexts)'
        })

    # Pattern 2: Same function name, different return values
    funcs1 = set(re.findall(r'def\s+(\w+)\s*.*:=\s*(true|false)\b', content1))
    funcs2 = set(re.findall(r'def\s+(\w+)\s*.*:=\s*(true|false)\b', content2))
    for name1, val1 in funcs1:
        for name2, val2 in funcs2:
            if name1 == name2 and val1 != val2:
                contradictions.append({
                    'pattern': 'boolean_function_conflict',
                    'file1': file1,
                    'file2': file2,
                    'function': name1,
                    'values': [val1, val2],
                    'confidence': 0.7,
                    'description': f"Function '{name1}' returns {val1} in {file1} but {val2} in {file2}"
                })

    # Pattern 3: Conflicting rate definitions (same pattern name, different values)
    rates1 = dict(re.findall(r'def\s+(\w*[Rr]ate\w*)\s*:.*:=\s*(\d+(?:\.\d+)?)', content1))
    rates2 = dict(re.findall(r'def\s+(\w*[Rr]ate\w*)\s*:.*:=\s*(\d+(?:\.\d+)?)', content2))
    for name in set(rates1.keys()) & set(rates2.keys()):
        if rates1[name] != rates2[name]:
            contradictions.append({
                'pattern': 'rate_conflict',
                'file1': file1,
                'file2': file2,
                'rate_name': name,
                'values': [rates1[name], rates2[name]],
                'confidence': 0.8,
                'description': f"Rate '{name}' is {rates1[name]} in {file1} but {rates2[name]} in {file2}"
            })

    # Pattern 4: Overlapping section references with different treatments
    # Look for comments citing same IRC section with opposite conclusions
    sec_refs1 = set(re.findall(r'IRC\s*§?\s*(\d+)', content1))
    sec_refs2 = set(re.findall(r'IRC\s*§?\s*(\d+)', content2))
    overlapping = sec_refs1 & sec_refs2
    if overlapping and (file1 != file2):
        # Check if both files have opposite boolean results for same section reference
        for sec in overlapping:
            if (f'§{sec}' in content1 and 'exempt' in content1.lower() and
                f'§{sec}' in content2 and 'taxable' in content2.lower()):
                contradictions.append({
                    'pattern': 'section_reference_conflict',
                    'file1': file1,
                    'file2': file2,
                    'section': sec,
                    'confidence': 0.5,
                    'description': f"IRC §{sec} cited in both files with potentially opposite treatment"
                })

    # Pattern 5: Mutually exclusive conditions that might overlap
    # Check for conditions on same entity type with different requirements
    entity_patterns = [
        (r'is_foreign\s*=\s*true', r'is_domestic\s*=\s*true'),
        (r'is_individual\s*=\s*true', r'is_corporation\s*=\s*true'),
        (r'is_exempt\s*=\s*true', r'is_taxable\s*=\s*true'),
    ]
    for pattern_true, pattern_false in entity_patterns:
        if re.search(pattern_true, content1) and re.search(pattern_true, content2):
            if re.search(pattern_false, content1) or re.search(pattern_false, content2):
                # Both files discuss same entity type with potentially conflicting logic
                contradictions.append({
                    'pattern': 'entity_type_conflict',
                    'file1': file1,
                    'file2': file2,
                    'confidence': 0.4,
                    'description': 'Same entity type with potentially conflicting conditions'
                })
                break

    return contradictions


def check_contradictions_sequential(
    files: List[Path],
    contents: Dict[str, str],
    progress: Dict,
    chunk_size: int = DEFAULT_CHUNK_SIZE,
    sleep_between: float = DEFAULT_SLEEP_BETWEEN,
    sleep_every_n: int = DEFAULT_SLEEP_EVERY_N
) -> List[Dict]:
    """
    Check all pairs for contradictions.

    SEQUENTIAL - no parallelism, no process spawning.
    CHUNKED - process in batches with sleeps.
    RESUMABLE - saves progress after each chunk.
    """
    print("\n" + "="*60)
    print("PHASE 4: CHECKING PAIRWISE CONTRADICTIONS (Sequential)")
    print("="*60)

    file_list = [str(f) for f in files]
    total_pairs = len(file_list) * (len(file_list) - 1) // 2

    print(f"Total pairs: {total_pairs:,}")
    print(f"Chunk size: {chunk_size}")
    print(f"Sleep between chunks: {sleep_between}s")

    # Resume from progress
    pairs_checked = progress.get('pairs_checked', 0)
    contradictions = progress.get('contradictions', [])

    if pairs_checked > 0:
        print(f"Resuming from pair {pairs_checked:,}")

    # Generate pairs
    pair_index = 0
    current_chunk_count = 0
    start_time = time.time()

    for i, f1 in enumerate(file_list):
        for f2 in file_list[i+1:]:
            # Skip already checked pairs
            if pair_index < pairs_checked:
                pair_index += 1
                continue

            # Check this pair
            content1 = contents.get(f1, "")
            content2 = contents.get(f2, "")
            file1_name = Path(f1).name
            file2_name = Path(f2).name

            results = check_contradiction(content1, content2, file1_name, file2_name)
            contradictions.extend(results)

            pair_index += 1
            pairs_checked += 1
            current_chunk_count += 1

            # Brief sleep every N items to prevent CPU spike
            if current_chunk_count % sleep_every_n == 0:
                time.sleep(0.001)  # 1ms micro-sleep

            # End of chunk - save progress and sleep
            if current_chunk_count >= chunk_size:
                # Save progress
                progress['pairs_checked'] = pairs_checked
                progress['contradictions'] = contradictions
                save_progress(progress)

                # Progress report
                elapsed = time.time() - start_time
                rate = pairs_checked / elapsed if elapsed > 0 else 0
                eta = (total_pairs - pairs_checked) / rate if rate > 0 else 0

                print(f"  {pairs_checked:,}/{total_pairs:,} ({100*pairs_checked/total_pairs:.1f}%) "
                      f"- {rate:.0f} pairs/s - ETA: {eta:.0f}s - Found: {len(contradictions)}")

                # Sleep between chunks
                time.sleep(sleep_between)

                # Explicit garbage collection
                gc.collect()

                current_chunk_count = 0

    # Final save
    progress['pairs_checked'] = pairs_checked
    progress['contradictions'] = contradictions
    progress['completed'] = True
    save_progress(progress)

    elapsed = time.time() - start_time
    print(f"\nCompleted in {elapsed:.1f}s")
    print(f"Found {len(contradictions)} potential contradictions")

    return contradictions


def main():
    parser = argparse.ArgumentParser(
        description='Safe loophole finder v2.0 (comprehensive detection)',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--files', type=int, default=0,
                        help='Max files to check (0 = all)')
    parser.add_argument('--resume', action='store_true',
                        help='Resume from saved progress')
    parser.add_argument('--chunk-size', type=int, default=DEFAULT_CHUNK_SIZE,
                        help=f'Pairs per chunk (default: {DEFAULT_CHUNK_SIZE})')
    parser.add_argument('--sleep', type=float, default=DEFAULT_SLEEP_BETWEEN,
                        help=f'Sleep between chunks (default: {DEFAULT_SLEEP_BETWEEN}s)')
    parser.add_argument('--skip-contradictions', action='store_true',
                        help='Skip pairwise contradiction checking')
    parser.add_argument('--skip-global', action='store_true',
                        help='Skip global checks (types, thresholds, deprecated)')
    parser.add_argument('--reset', action='store_true',
                        help='Reset progress and start fresh')

    args = parser.parse_args()

    print("="*60)
    print("SAFE LOOPHOLE FINDER v2.0")
    print("Comprehensive Detection - Zero Parallelism")
    print("="*60)

    # Load or reset progress
    if args.reset and PROGRESS_FILE.exists():
        PROGRESS_FILE.unlink()
        print("Progress reset.")

    progress = load_progress() if args.resume else {
        "file_errors": {},
        "pairs_checked": 0,
        "contradictions": [],
        "type_issues": [],
        "threshold_issues": [],
        "deprecated_issues": [],
        "incomplete_issues": [],
        "completed": False
    }

    # Phase 1: Build
    build_errors = run_build()

    # Phase 2: Load files
    files = load_files(args.files)
    if not files:
        print("No files found!")
        return

    print(f"\nProcessing {len(files)} files")

    contents = load_file_contents(files)

    # Phase 3: Check file errors (instant)
    file_results = check_file_errors(files, build_errors)
    progress['file_errors'] = {k: v for k, v in file_results.items()}

    # Phase 4: Global checks (v2.0)
    if not args.skip_global:
        print("\n" + "="*60)
        print("PHASE 4a: GLOBAL CONSISTENCY CHECKS (v2.0)")
        print("="*60)

        # Type consistency
        print("  Checking type definitions...")
        type_issues = check_type_consistency(contents)
        progress['type_issues'] = type_issues
        print(f"    Found {len(type_issues)} type consistency issues")

        # Threshold conflicts
        print("  Checking threshold conflicts...")
        threshold_issues = check_threshold_conflicts(contents)
        progress['threshold_issues'] = threshold_issues
        print(f"    Found {len(threshold_issues)} threshold issues")

        # Deprecated usage
        print("  Checking deprecated function usage...")
        deprecated_issues = check_deprecated_usage(contents)
        progress['deprecated_issues'] = deprecated_issues
        print(f"    Found {len(deprecated_issues)} deprecated usage issues")

        # Incomplete implementations
        print("  Checking incomplete implementations...")
        incomplete_issues = check_incomplete_implementations(contents)
        progress['incomplete_issues'] = incomplete_issues
        print(f"    Found {len(incomplete_issues)} incomplete implementation issues")

        save_progress(progress)

    # Phase 5: Check pairwise contradictions (sequential, chunked)
    if not args.skip_contradictions:
        contradictions = check_contradictions_sequential(
            files, contents, progress,
            chunk_size=args.chunk_size,
            sleep_between=args.sleep
        )

        if contradictions:
            print("\nPAIRWISE CONTRADICTIONS BY PATTERN:")
            by_pattern = {}
            for c in contradictions:
                pattern = c.get('pattern', 'unknown')
                if pattern not in by_pattern:
                    by_pattern[pattern] = []
                by_pattern[pattern].append(c)

            for pattern, items in sorted(by_pattern.items(), key=lambda x: -len(x[1])):
                print(f"\n  {pattern}: {len(items)} found")
                for item in items[:3]:
                    print(f"    - {item.get('file1', '?')} <-> {item.get('file2', '?')}")
                    if 'description' in item:
                        print(f"      {item['description']}")

    # Summary
    passed = sum(1 for v in file_results.values() if v)
    print("\n" + "="*60)
    print("FINAL RESULTS (v2.0)")
    print("="*60)
    print(f"Files: {passed}/{len(files)} passed build")

    if not args.skip_global:
        total_global = (len(progress.get('type_issues', [])) +
                       len(progress.get('threshold_issues', [])) +
                       len(progress.get('deprecated_issues', [])) +
                       len(progress.get('incomplete_issues', [])))
        print(f"Global issues: {total_global}")
        print(f"  - Type consistency: {len(progress.get('type_issues', []))}")
        print(f"  - Threshold conflicts: {len(progress.get('threshold_issues', []))}")
        print(f"  - Deprecated usage: {len(progress.get('deprecated_issues', []))}")
        print(f"  - Incomplete: {len(progress.get('incomplete_issues', []))}")

    if not args.skip_contradictions:
        print(f"Pairwise contradictions: {len(progress.get('contradictions', []))} found")

    print(f"\nProgress saved to: {PROGRESS_FILE}")


if __name__ == '__main__':
    main()
