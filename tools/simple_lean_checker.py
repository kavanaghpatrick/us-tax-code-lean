#!/usr/bin/env python3
"""
Simple Lean Checker - FIX #60: Avoid lake build race condition

This is the CORRECT way to check Lean files - let lake handle parallelism.

FIX #60 EXPLANATION:
- Running multiple `lake build` processes in parallel creates lock contention
- Lake itself is already parallel (uses multiple threads internally)
- 8 workers × lake's 8 threads = 64 threads fighting over .lake/build locks
- Result: SLOWER than sequential due to lock contention

SOLUTION:
- Run `lake build` ONCE and let it handle parallelism
- Lake knows the dependency graph and optimizes the build order
- No lock contention, no race conditions, faster overall

Usage:
    python3 simple_lean_checker.py [--targets Section61 Section62 ...]
"""

import argparse
import subprocess
import time
from pathlib import Path
import sys

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"


def check_lean_files(targets: list[str] = None) -> dict:
    """
    Check Lean files using lake's built-in parallelism.

    FIX #60: Runs lake build ONCE instead of multiple parallel instances.

    Args:
        targets: List of specific targets to build (e.g., ["Section61", "Section62"])
                If None, builds all targets defined in lakefile.lean

    Returns:
        dict with keys: success, duration, errors, warnings, stdout, stderr
    """
    print("Running lake build (using lake's built-in parallelism)...")
    start = time.time()

    # Build command - let lake handle parallelism
    cmd = ['lake', 'build']
    if targets:
        cmd.extend(targets)
        print(f"Building {len(targets)} targets: {', '.join(targets[:5])}{' ...' if len(targets) > 5 else ''}")
    else:
        print("Building all targets from lakefile.lean")

    try:
        result = subprocess.run(
            cmd,
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=300  # 5 minutes timeout
        )

        duration = time.time() - start

        # Parse output for errors and warnings
        errors = []
        warnings = []

        for line in result.stderr.split('\n'):
            line_lower = line.lower()
            if 'error:' in line_lower or 'error [' in line_lower:
                errors.append(line.strip())
            elif 'warning:' in line_lower or 'warning [' in line_lower:
                warnings.append(line.strip())

        success = result.returncode == 0 and len(errors) == 0

        # Print summary
        print(f"\n{'='*60}")
        print(f"RESULTS")
        print(f"{'='*60}")
        print(f"Duration:      {duration:.1f}s")
        print(f"Success:       {'✓ YES' if success else '✗ NO'}")
        print(f"Errors:        {len(errors)}")
        print(f"Warnings:      {len(warnings)}")
        print(f"Return code:   {result.returncode}")

        if errors:
            print(f"\nFIRST 10 ERRORS:")
            for error in errors[:10]:
                print(f"  {error[:200]}")
            if len(errors) > 10:
                print(f"  ... and {len(errors) - 10} more")

        if warnings:
            print(f"\nFIRST 5 WARNINGS:")
            for warning in warnings[:5]:
                print(f"  {warning[:200]}")
            if len(warnings) > 5:
                print(f"  ... and {len(warnings) - 5} more")

        return {
            'success': success,
            'duration': duration,
            'errors': errors,
            'warnings': warnings,
            'stdout': result.stdout,
            'stderr': result.stderr,
            'returncode': result.returncode
        }

    except subprocess.TimeoutExpired:
        duration = time.time() - start
        print(f"\n✗ TIMEOUT after {duration:.1f}s")
        return {
            'success': False,
            'duration': duration,
            'errors': ['Build timeout after 300 seconds'],
            'warnings': [],
            'stdout': '',
            'stderr': '',
            'returncode': -1
        }
    except Exception as e:
        duration = time.time() - start
        print(f"\n✗ ERROR: {e}")
        return {
            'success': False,
            'duration': duration,
            'errors': [str(e)],
            'warnings': [],
            'stdout': '',
            'stderr': '',
            'returncode': -1
        }


def find_section_targets() -> list[str]:
    """Find all Section*.lean files and return their target names."""
    lean_files = sorted(TAXCODE_DIR.glob('Section*.lean'))
    # FIX (Gemini): Prepend 'TaxCode.' to match Lake module names
    # Lake targets are namespaced: TaxCode.Section61, not Section61
    return [f"TaxCode.{f.stem}" for f in lean_files]


def main():
    parser = argparse.ArgumentParser(
        description='Simple Lean checker (FIX #60: no race conditions)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Build all targets
  python3 simple_lean_checker.py

  # Build specific sections
  python3 simple_lean_checker.py --targets Section61 Section62

  # Build all Section*.lean files
  python3 simple_lean_checker.py --auto-discover

Why this is better than parallel_lean_checker.py:
  - No race conditions (lake manages .lake/build directory)
  - Faster (lake optimizes build order, no lock contention)
  - Simpler (let lake do what it's designed to do)
        """
    )
    parser.add_argument(
        '--targets',
        nargs='+',
        help='Specific targets to build (e.g., Section61 Section62)'
    )
    parser.add_argument(
        '--auto-discover',
        action='store_true',
        help='Auto-discover all Section*.lean files and build them'
    )

    args = parser.parse_args()

    # Determine targets
    targets = None
    if args.targets:
        targets = args.targets
    elif args.auto_discover:
        targets = find_section_targets()
        if not targets:
            print(f"No Section*.lean files found in {TAXCODE_DIR}")
            return 1
        print(f"Auto-discovered {len(targets)} targets")

    # Run check
    result = check_lean_files(targets)

    # Exit with appropriate code
    return 0 if result['success'] else 1


if __name__ == '__main__':
    sys.exit(main())
