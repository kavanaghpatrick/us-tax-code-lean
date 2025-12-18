#!/usr/bin/env python3
"""
Fix unclosed doc comments in Lean files.

Finds files where /-! doc comment is never closed and adds -/ before TODO lines.
"""

import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / 'src' / 'TaxCode'


def needs_fix(filepath: Path) -> bool:
    """Check if file has unclosed comment ending with TODO."""
    content = filepath.read_text()
    # Count all comment opens (both /- and /-!)
    all_opens = content.count('/-')
    closes = content.count('-/')

    if all_opens <= closes:
        return False

    # Check if ends with TODO
    lines = content.strip().split('\n')
    for line in reversed(lines[-20:]):
        if line.strip():
            return '-- TODO' in line or 'See References' in line
    return False


def fix_file(filepath: Path) -> bool:
    """Add -/ before the TODO lines to close the doc comment."""
    content = filepath.read_text()

    # Find where TODO comments start
    lines = content.split('\n')
    todo_start = None

    for i, line in enumerate(lines):
        if '-- TODO' in line:
            todo_start = i
            break

    if todo_start is None:
        # Try to find "See References" as alternative end marker
        for i, line in enumerate(lines):
            if 'See References' in line:
                todo_start = i + 1
                break

    if todo_start is None:
        return False

    # Insert -/ before TODO lines
    lines.insert(todo_start, '-/')
    lines.insert(todo_start, '')  # blank line for readability

    filepath.write_text('\n'.join(lines))
    return True


def main():
    all_files = list(TAXCODE_DIR.glob('Section*.lean'))
    main_files = [f for f in all_files if not any(x in f.name for x in ['_aristotle', '_output', '_backup'])]

    fixed = 0
    for filepath in sorted(main_files):
        if needs_fix(filepath):
            if fix_file(filepath):
                print(f"Fixed: {filepath.name}")
                fixed += 1
            else:
                print(f"Could not fix: {filepath.name}")

    print(f"\nTotal fixed: {fixed}")


if __name__ == '__main__':
    main()
