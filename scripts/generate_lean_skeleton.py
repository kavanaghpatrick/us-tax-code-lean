#!/usr/bin/env python3
"""
Lean Skeleton Generator

Generates Lean 4 skeleton files from scraped IRC section data.

Usage:
    python scripts/generate_lean_skeleton.py --section 61
    python scripts/generate_lean_skeleton.py --batch 61,62,63
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List


LEAN_TEMPLATE = """import Common.Basic

/-!
# IRC Section {section} - {title}

This file formalizes {section_desc}.

## References
- [26 USC §{section}]({url})

## Summary
{summary}
-/

-- TODO: Add type definitions

-- TODO: Add main functions

-- TODO: Add theorems to prove

-- Example usage
#check placeholder
"""

TEST_TEMPLATE = """import TaxCode.Section{section}
import Common.Basic

/-!
# IRC Section {section} Tests

Test cases for {title}.
-/

-- TODO: Add test cases

#eval placeholder  -- Replace with actual tests
"""


class LeanSkeletonGenerator:
    """Generate Lean skeleton files from IRC section data."""

    def __init__(self, sections_data: List[Dict]):
        """Initialize with scraped section data."""
        self.sections = {s['section']: s for s in sections_data}

    def generate_skeleton(self, section_num: int) -> str:
        """Generate Lean skeleton for a section."""
        if section_num not in self.sections:
            raise ValueError(f"Section {section_num} not found in data")

        section = self.sections[section_num]

        # Extract first paragraph as summary
        text = section.get('text', '')
        paragraphs = text.split('\n\n')
        summary = paragraphs[0] if paragraphs else "TODO: Add summary"

        # Clean up summary for Lean comment
        summary = summary.replace('§', '§')  # Normalize section symbol
        summary = '\n'.join(f"   {line.strip()}" for line in summary.split('\n') if line.strip())

        # Section description
        section_desc = f"IRC §{section_num} ({section['title']})"

        return LEAN_TEMPLATE.format(
            section=section_num,
            title=section['title'],
            section_desc=section_desc,
            url=section['url'],
            summary=summary or "   TODO: Add summary"
        )

    def generate_test_skeleton(self, section_num: int) -> str:
        """Generate test file skeleton."""
        if section_num not in self.sections:
            raise ValueError(f"Section {section_num} not found")

        section = self.sections[section_num]

        return TEST_TEMPLATE.format(
            section=section_num,
            title=section['title']
        )

    def write_section_file(self, section_num: int, output_dir: Path):
        """Write Lean skeleton file."""
        skeleton = self.generate_skeleton(section_num)

        # Create output directory
        src_dir = output_dir / 'src' / 'TaxCode'
        src_dir.mkdir(parents=True, exist_ok=True)

        # Write file
        output_file = src_dir / f'Section{section_num}.lean'
        with open(output_file, 'w') as f:
            f.write(skeleton)

        print(f"Generated: {output_file}")
        return output_file

    def write_test_file(self, section_num: int, output_dir: Path):
        """Write test skeleton file."""
        test_skeleton = self.generate_test_skeleton(section_num)

        # Create test directory
        test_dir = output_dir / 'src' / 'Tests'
        test_dir.mkdir(parents=True, exist_ok=True)

        # Write file
        output_file = test_dir / f'Section{section_num}Tests.lean'
        with open(output_file, 'w') as f:
            f.write(test_skeleton)

        print(f"Generated: {output_file}")
        return output_file


def main():
    parser = argparse.ArgumentParser(description='Generate Lean skeletons from IRC sections')
    parser.add_argument('--section', type=str, help='Single section number')
    parser.add_argument('--batch', type=str, help='Comma-separated section numbers')
    parser.add_argument('--data', type=str, default='data/sections.json', help='Input JSON file')
    parser.add_argument('--output-dir', type=str, default='.', help='Output directory')

    args = parser.parse_args()

    # Load section data
    data_file = Path(args.data)
    if not data_file.exists():
        print(f"Error: {data_file} not found. Run scrape_cornell.py first.", file=sys.stderr)
        return 1

    with open(data_file) as f:
        sections_data = json.load(f)

    generator = LeanSkeletonGenerator(sections_data)
    output_dir = Path(args.output_dir)

    # Determine which sections to generate
    section_nums = []
    if args.section:
        section_nums = [int(args.section)]
    elif args.batch:
        section_nums = [int(s.strip()) for s in args.batch.split(',')]
    else:
        parser.print_help()
        return 1

    # Generate skeletons
    for section_num in section_nums:
        try:
            generator.write_section_file(section_num, output_dir)
            generator.write_test_file(section_num, output_dir)
        except ValueError as e:
            print(f"Error: {e}", file=sys.stderr)
            return 1

    print(f"\nGenerated {len(section_nums)} section skeletons")
    return 0


if __name__ == '__main__':
    sys.exit(main())
