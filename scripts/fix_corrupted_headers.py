#!/usr/bin/env python3
"""
Fix corrupted TaxYear/FilingStatus headers in Aristotle output files.

The corrupted pattern:
    structure TaxYear where year : Nat

    ; h_valid : year ≥ 1913; deriving

    DecidableEq, Repr
    inductive FilingStatus | Single | MarriedFilingJointly...

Should be:
    structure TaxYear where
      year : Nat
      h_valid : year ≥ 1913
      deriving DecidableEq, Repr

    inductive FilingStatus
      | Single
      | MarriedFilingJointly
      ...

Usage:
    python scripts/fix_corrupted_headers.py --dry-run   # Preview changes
    python scripts/fix_corrupted_headers.py --fix       # Apply fixes
"""

import argparse
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / 'src' / 'TaxCode'

# The correct header to replace corrupted versions
CORRECT_HEADER = '''def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited

'''


def is_corrupted(content: str) -> bool:
    """Check if file has the corrupted semicolon pattern."""
    return '; h_valid : year' in content or '; h_valid :' in content


def fix_file(filepath: Path, dry_run: bool = True) -> bool:
    """Fix a single file. Returns True if fixed."""
    content = filepath.read_text()

    if not is_corrupted(content):
        return False

    # Pattern to match the corrupted header block
    # This matches from "def Currency" through the FilingStatus definition
    pattern = r'def Currency := Int\s*\n\s*structure TaxYear where year : Nat\s*\n\s*; h_valid : year ≥ 1913; deriving\s*\n\s*DecidableEq, Repr\s*\n\s*inductive FilingStatus \| Single \| MarriedFilingJointly \| MarriedFilingSeparately \| HeadOfHousehold \| QualifyingWidower \| Estate \| Trust deriving Repr, DecidableEq, Inhabited'

    new_content = re.sub(pattern, CORRECT_HEADER.strip(), content)

    if new_content == content:
        # Try alternative pattern (might have slight variations)
        pattern2 = r'def Currency := Int\s*\n\s*structure TaxYear where year : Nat\s*\n\s*; h_valid : year ≥ 1913; deriving\s*\n\s*DecidableEq, Repr\s*\n\s*inductive FilingStatus.*?deriving Repr, DecidableEq, Inhabited'
        new_content = re.sub(pattern2, CORRECT_HEADER.strip(), content, flags=re.DOTALL)

    if new_content == content:
        print(f"  Warning: Pattern not matched for {filepath.name}")
        return False

    if not dry_run:
        filepath.write_text(new_content)

    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dry-run', action='store_true', help='Preview without changing files')
    parser.add_argument('--fix', action='store_true', help='Apply fixes')
    args = parser.parse_args()

    if not args.dry_run and not args.fix:
        print("Specify --dry-run or --fix")
        return 1

    # Find corrupted files
    all_files = list(TAXCODE_DIR.glob('Section*.lean'))
    main_files = [f for f in all_files if not any(x in f.name for x in ['_aristotle', '_output', '_backup'])]

    corrupted = [f for f in main_files if is_corrupted(f.read_text())]

    print(f"Found {len(corrupted)} corrupted files out of {len(main_files)} total")

    if args.dry_run:
        print("\nDry run - no changes will be made")

    fixed = 0
    failed = 0

    for filepath in sorted(corrupted):
        result = fix_file(filepath, dry_run=args.dry_run)
        if result:
            fixed += 1
            print(f"  {'Would fix' if args.dry_run else 'Fixed'}: {filepath.name}")
        else:
            failed += 1

    print(f"\n{'Would fix' if args.dry_run else 'Fixed'}: {fixed}")
    print(f"Failed to match pattern: {failed}")

    return 0


if __name__ == '__main__':
    import sys
    sys.exit(main())
