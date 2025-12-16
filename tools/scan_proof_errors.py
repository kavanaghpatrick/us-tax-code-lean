#!/usr/bin/env python3
"""
Scan all Lean files for proof errors and categorize them.

This script builds each Section*.lean file and categorizes the types of errors found.
"""

import subprocess
import re
from pathlib import Path
from collections import defaultdict
import json

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"


def check_section(section_path: Path) -> dict:
    """Check a single section and return categorized errors."""
    try:
        result = subprocess.run(
            ['lake', 'build', f'TaxCode.{section_path.stem}'],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=60
        )

        errors = []
        warnings = []

        # Parse stderr for errors and warnings
        for line in result.stderr.split('\n'):
            if 'error:' in line.lower():
                errors.append(line.strip())
            elif 'warning:' in line.lower():
                warnings.append(line.strip())

        # Categorize errors
        categories = defaultdict(list)

        for error in errors:
            if 'aesop: failed to prove the goal' in error:
                categories['aesop_failure'].append(error)
            elif 'Expected type must not contain metavariables' in error:
                categories['metavariable_error'].append(error)
            elif 'type mismatch' in error:
                categories['type_mismatch'].append(error)
            elif 'timeout' in error.lower():
                categories['timeout'].append(error)
            elif 'environment already contains' in error:
                categories['duplicate_definition'].append(error)
            elif 'failed to prove strict positivity' in error:
                categories['positivity_error'].append(error)
            elif 'unknown identifier' in error:
                categories['unknown_identifier'].append(error)
            else:
                categories['other_error'].append(error)

        # Categorize warnings
        warning_categories = defaultdict(list)
        for warning in warnings:
            if 'aesop: failed to prove' in warning:
                warning_categories['aesop_warning'].append(warning)
            elif 'unused' in warning.lower():
                warning_categories['unused'].append(warning)
            elif 'deprecated' in warning.lower():
                warning_categories['deprecated'].append(warning)
            else:
                warning_categories['other_warning'].append(warning)

        return {
            'file': section_path.stem,
            'success': result.returncode == 0 and len(errors) == 0,
            'error_count': len(errors),
            'warning_count': len(warnings),
            'error_categories': dict(categories),
            'warning_categories': dict(warning_categories),
            'returncode': result.returncode
        }

    except subprocess.TimeoutExpired:
        return {
            'file': section_path.stem,
            'success': False,
            'error_count': 1,
            'warning_count': 0,
            'error_categories': {'timeout': ['Build timeout after 60 seconds']},
            'warning_categories': {},
            'returncode': -1
        }
    except Exception as e:
        return {
            'file': section_path.stem,
            'success': False,
            'error_count': 1,
            'warning_count': 0,
            'error_categories': {'exception': [str(e)]},
            'warning_categories': {},
            'returncode': -1
        }


def main():
    # Find all Section*.lean files (exclude _aristotle variants for now)
    all_sections = sorted(TAXCODE_DIR.glob('Section*.lean'))
    # Filter to main sections only (no _aristotle)
    main_sections = [s for s in all_sections if '_aristotle' not in s.stem]

    print(f"Scanning {len(main_sections)} main Section files...")
    print(f"(Excluding {len(all_sections) - len(main_sections)} _aristotle variants)")
    print()

    results = []
    success_count = 0

    for i, section in enumerate(main_sections[:50], 1):  # Limit to first 50 for speed
        print(f"[{i}/50] {section.stem}...", end='', flush=True)
        result = check_section(section)
        results.append(result)

        if result['success']:
            print(" ✓")
            success_count += 1
        else:
            print(f" ✗ ({result['error_count']} errors, {result['warning_count']} warnings)")

    # Aggregate statistics
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Files scanned:     {len(results)}")
    print(f"Success:           {success_count} ({success_count/len(results)*100:.1f}%)")
    print(f"Failures:          {len(results) - success_count}")
    print()

    # Aggregate error categories
    all_error_categories = defaultdict(int)
    all_warning_categories = defaultdict(int)

    for result in results:
        for category, errors in result['error_categories'].items():
            all_error_categories[category] += len(errors)
        for category, warnings in result['warning_categories'].items():
            all_warning_categories[category] += len(warnings)

    print("ERROR CATEGORIES:")
    for category, count in sorted(all_error_categories.items(), key=lambda x: -x[1]):
        print(f"  {category:30s}: {count:4d}")

    print("\nWARNING CATEGORIES:")
    for category, count in sorted(all_warning_categories.items(), key=lambda x: -x[1]):
        print(f"  {category:30s}: {count:4d}")

    # Save detailed results
    output_file = PROJECT_ROOT / "PROOF_ERROR_SCAN.json"
    with open(output_file, 'w') as f:
        json.dump({
            'summary': {
                'total_files': len(results),
                'success_count': success_count,
                'failure_count': len(results) - success_count,
                'error_categories': dict(all_error_categories),
                'warning_categories': dict(all_warning_categories)
            },
            'details': results
        }, f, indent=2)

    print(f"\nDetailed results saved to: {output_file}")

    # List sections that work
    working_sections = [r['file'] for r in results if r['success']]
    if working_sections:
        print(f"\n✓ WORKING SECTIONS ({len(working_sections)}):")
        for section in working_sections[:10]:
            print(f"  - {section}")
        if len(working_sections) > 10:
            print(f"  ... and {len(working_sections) - 10} more")


if __name__ == '__main__':
    main()
