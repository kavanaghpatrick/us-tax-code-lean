#!/usr/bin/env python3
"""
Minimal Build Checker - Outputs only summary statistics.

Builds all sections, suppresses verbose output, returns only:
- Success/failure counts
- List of failed sections (names only)
- Exit code 0 if all pass, 1 if any fail

Usage:
    python scripts/build_check.py              # Check all
    python scripts/build_check.py --sample 50  # Random sample of 50
    python scripts/build_check.py --batch 1    # First batch of 100
"""

import argparse
import json
import os
import random
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / 'src' / 'TaxCode'
RESULTS_FILE = PROJECT_ROOT / 'data' / 'build_check_results.json'


def get_all_sections():
    """Get all main section files."""
    files = list(TAXCODE_DIR.glob('Section*.lean'))
    main_files = [f for f in files if not any(x in f.name for x in ['_aristotle', '_output', '_backup'])]
    return sorted(main_files, key=lambda f: int(re.search(r'Section(\d+)', f.stem).group(1)) if re.search(r'Section(\d+)', f.stem) else 0)


def build_one(section_file):
    """Build one section, return (name, success, error_snippet)."""
    name = section_file.stem
    module = f"TaxCode.{name}"

    try:
        result = subprocess.run(
            ['lake', 'build', module],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=120
        )

        if result.returncode == 0:
            # Check for sorry warnings
            has_sorry = 'sorry' in result.stderr.lower()
            return (name, True, 'sorry' if has_sorry else None)
        else:
            # Extract first error line
            for line in (result.stdout + result.stderr).split('\n'):
                if 'error:' in line.lower():
                    # Extract just the error message, not the full path
                    match = re.search(r'error:\s*(.{0,60})', line, re.IGNORECASE)
                    if match:
                        return (name, False, match.group(1).strip())
            return (name, False, 'unknown error')
    except subprocess.TimeoutExpired:
        return (name, False, 'timeout')
    except Exception as e:
        return (name, False, str(e)[:40])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--sample', type=int, help='Random sample size')
    parser.add_argument('--batch', type=int, help='Batch number (1-8, each ~100 sections)')
    parser.add_argument('--parallel', type=int, default=6, help='Parallel workers')
    args = parser.parse_args()

    all_sections = get_all_sections()
    total_available = len(all_sections)

    # Select sections to check
    if args.sample:
        sections = random.sample(all_sections, min(args.sample, total_available))
        mode = f"sample({args.sample})"
    elif args.batch:
        batch_size = 100
        start = (args.batch - 1) * batch_size
        end = start + batch_size
        sections = all_sections[start:end]
        mode = f"batch{args.batch}"
    else:
        sections = all_sections
        mode = "full"

    total = len(sections)

    # Build in parallel with minimal output
    results = []
    done = 0

    with ThreadPoolExecutor(max_workers=args.parallel) as executor:
        futures = {executor.submit(build_one, s): s for s in sections}
        for future in as_completed(futures):
            name, success, error = future.result()
            results.append((name, success, error))
            done += 1
            # Single-line progress (overwrites itself)
            print(f"\r[{done}/{total}] {name}...", end="", flush=True)

    print()  # Newline after progress

    # Compute stats
    passed = [r for r in results if r[1]]
    failed = [r for r in results if not r[1]]
    with_sorry = [r for r in passed if r[2] == 'sorry']

    # Save detailed results
    RESULTS_FILE.parent.mkdir(parents=True, exist_ok=True)
    with open(RESULTS_FILE, 'w') as f:
        json.dump({
            'mode': mode,
            'total': total,
            'passed': len(passed),
            'failed': len(failed),
            'with_sorry': len(with_sorry),
            'failures': [(r[0], r[2]) for r in failed],
            'sorry_sections': [r[0] for r in with_sorry]
        }, f, indent=2)

    # Print concise summary
    print(f"\n{'='*50}")
    print(f"BUILD CHECK: {mode} ({total} sections)")
    print(f"{'='*50}")
    print(f"✓ Passed:     {len(passed)}")
    print(f"✗ Failed:     {len(failed)}")
    print(f"⚠ With sorry: {len(with_sorry)}")
    print(f"Success rate: {len(passed)/total*100:.1f}%")

    if failed:
        print(f"\nFailed sections:")
        for name, success, error in sorted(failed, key=lambda x: int(re.search(r'\d+', x[0]).group())):
            print(f"  {name}: {error}")

    print(f"\nDetails: {RESULTS_FILE}")

    return 0 if not failed else 1


if __name__ == '__main__':
    sys.exit(main())
