#!/usr/bin/env python3
"""
Batch Formalization System for Phase 1

Systematically prepares and submits IRC sections to Aristotle for formalization.
Handles section selection, skeleton generation, preparation, and submission tracking.

Usage:
    python scripts/batch_formalize.py --wave 1 --dry-run
    python scripts/batch_formalize.py --wave 1 --prepare-only
    python scripts/batch_formalize.py --wave 1 --submit
    python scripts/batch_formalize.py --sections 61,62,63 --submit
"""

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Set


# Predefined waves for systematic formalization
WAVES = {
    1: [1, 61, 62, 63, 151, 152, 162, 163, 164, 165, 166, 167, 168, 169, 170, 1001, 1011, 1012, 1221, 1222],
    2: [21, 24, 32, 25, 55, 56, 57, 213, 67, 68, 2, 3, 7703],
    3: [64, 65, 1211, 1212, 1231, 1014, 1015, 1016, 1222, 121],
    4: [174, 179, 183, 195, 197, 199, 274, 72, 102, 105],
    5: [401, 402, 408, 219, 117, 127, 221, 71, 215, 106],
}


class BatchFormalizationSystem:
    """Manages batch formalization workflow."""

    def __init__(self, dry_run: bool = False):
        self.dry_run = dry_run
        self.project_root = Path(__file__).parent.parent
        self.sections_db = self.project_root / 'data' / 'sections.json'
        self.lean_dir = self.project_root / 'src' / 'TaxCode'
        self.progress_file = self.project_root / 'data' / 'batch_progress.json'

        self.load_sections_db()
        self.load_progress()

    def load_sections_db(self):
        """Load scraped sections database."""
        if self.sections_db.exists():
            with open(self.sections_db) as f:
                self.sections = {s['section']: s for s in json.load(f)}
            print(f"✓ Loaded {len(self.sections)} scraped sections")
        else:
            print(f"✗ Sections database not found: {self.sections_db}")
            self.sections = {}

    def load_progress(self):
        """Load batch processing progress."""
        if self.progress_file.exists():
            with open(self.progress_file) as f:
                self.progress = json.load(f)
        else:
            self.progress = {
                'waves_completed': [],
                'skeletons_created': [],
                'prepared': [],
                'submitted': [],
                'failed': []
            }

    def save_progress(self):
        """Save batch processing progress."""
        if not self.dry_run:
            self.progress_file.parent.mkdir(parents=True, exist_ok=True)
            with open(self.progress_file, 'w') as f:
                json.dump(self.progress, f, indent=2)

    def check_section_status(self, section_num: str) -> Dict[str, bool]:
        """Check the status of a section."""
        status = {
            'scraped': section_num in self.sections,
            'has_lean': (self.lean_dir / f'Section{section_num}.lean').exists(),
            'has_aristotle': (self.lean_dir / f'Section{section_num}_aristotle.lean').exists(),
            'prepared': section_num in self.progress['prepared'],
            'submitted': section_num in self.progress['submitted'],
        }
        return status

    def create_skeleton(self, section_num: str) -> bool:
        """Create a basic Lean skeleton for a section."""
        lean_file = self.lean_dir / f'Section{section_num}.lean'

        if lean_file.exists():
            print(f"  Section{section_num}.lean already exists")
            return True

        if section_num not in self.sections:
            print(f"  ✗ Section {section_num} not scraped - cannot create skeleton")
            return False

        section_data = self.sections[section_num]

        skeleton = f'''import Common.Basic

/-!
# IRC Section {section_num} - {section_data.get('title', 'Title Unknown')}

{section_data.get('content', '')[:500]}...

## References
- [26 USC §{section_num}]({section_data.get('url', '')})

## Key Provisions
- TODO: Identify key provisions
-/

-- TODO: Define data structures

-- TODO: Define functions

-- TODO: Write theorems with sorry

-- Examples
#eval "Section {section_num} loaded"
'''

        if self.dry_run:
            print(f"  [DRY RUN] Would create {lean_file}")
            return True
        else:
            lean_file.write_text(skeleton)
            print(f"  ✓ Created skeleton: {lean_file.name}")
            self.progress['skeletons_created'].append(section_num)
            return True

    def prepare_section(self, section_num: str) -> bool:
        """Prepare section for Aristotle (inline Common.Basic)."""
        lean_file = self.lean_dir / f'Section{section_num}.lean'

        if not lean_file.exists():
            print(f"  ✗ {lean_file.name} does not exist")
            return False

        if self.dry_run:
            print(f"  [DRY RUN] Would prepare Section{section_num}")
            return True

        # Run prepare_aristotle.py
        cmd = ['python3', 'scripts/prepare_aristotle.py', section_num]
        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode == 0:
            print(f"  ✓ Prepared Section{section_num}_aristotle.lean")
            self.progress['prepared'].append(section_num)
            return True
        else:
            print(f"  ✗ Failed to prepare Section{section_num}")
            print(f"    {result.stderr}")
            self.progress['failed'].append(section_num)
            return False

    def submit_section(self, section_num: str) -> bool:
        """Submit section to Aristotle."""
        aristotle_file = self.lean_dir / f'Section{section_num}_aristotle.lean'

        if not aristotle_file.exists():
            print(f"  ✗ {aristotle_file.name} does not exist")
            return False

        if self.dry_run:
            print(f"  [DRY RUN] Would submit Section{section_num} to Aristotle")
            return True

        # Run aristotle prove-from-file
        cmd = [
            'aristotle', 'prove-from-file',
            str(aristotle_file),
            '--no-wait'  # Don't block, results via email
        ]

        print(f"  → Submitting to Aristotle (async)...")
        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode == 0:
            print(f"  ✓ Submitted Section{section_num}")
            self.progress['submitted'].append(section_num)
            return True
        else:
            print(f"  ✗ Failed to submit Section{section_num}")
            print(f"    {result.stderr}")
            self.progress['failed'].append(section_num)
            return False

    def process_wave(self, wave_num: int, prepare_only: bool = False, submit: bool = False):
        """Process an entire wave of sections."""
        if wave_num not in WAVES:
            print(f"✗ Invalid wave number: {wave_num}")
            print(f"Available waves: {list(WAVES.keys())}")
            return

        sections = WAVES[wave_num]
        print(f"\n{'='*80}")
        print(f"WAVE {wave_num}: Processing {len(sections)} sections")
        print(f"{'='*80}\n")

        stats = {'created': 0, 'prepared': 0, 'submitted': 0, 'failed': 0}

        for i, section_num in enumerate(sections, 1):
            section_str = str(section_num)
            print(f"\n[{i}/{len(sections)}] Section {section_num}")
            print("-" * 60)

            status = self.check_section_status(section_str)
            print(f"  Status: scraped={status['scraped']}, lean={status['has_lean']}, "
                  f"aristotle={status['has_aristotle']}, submitted={status['submitted']}")

            # Create skeleton if needed
            if not status['has_lean']:
                if self.create_skeleton(section_str):
                    stats['created'] += 1
                else:
                    stats['failed'] += 1
                    continue

            # Prepare for Aristotle
            if not status['has_aristotle'] or not status['prepared']:
                if self.prepare_section(section_str):
                    stats['prepared'] += 1
                else:
                    stats['failed'] += 1
                    continue

            # Submit (if requested)
            if submit and not status['submitted']:
                if self.submit_section(section_str):
                    stats['submitted'] += 1
                    # Add delay between submissions
                    if i < len(sections) and not self.dry_run:
                        print(f"  ⏳ Waiting 3s before next submission...")
                        time.sleep(3)
                else:
                    stats['failed'] += 1

        # Save progress
        self.save_progress()

        # Print summary
        print(f"\n{'='*80}")
        print(f"WAVE {wave_num} SUMMARY")
        print(f"{'='*80}")
        print(f"  Skeletons created: {stats['created']}")
        print(f"  Prepared: {stats['prepared']}")
        print(f"  Submitted: {stats['submitted']}")
        print(f"  Failed: {stats['failed']}")
        print(f"{'='*80}\n")

        if not self.dry_run and stats['failed'] == 0:
            if wave_num not in self.progress['waves_completed']:
                self.progress['waves_completed'].append(wave_num)
                self.save_progress()

    def process_sections(self, section_nums: List[str], prepare_only: bool = False, submit: bool = False):
        """Process specific sections."""
        print(f"\n{'='*80}")
        print(f"Processing {len(section_nums)} specific sections")
        print(f"{'='*80}\n")

        stats = {'created': 0, 'prepared': 0, 'submitted': 0, 'failed': 0}

        for i, section_num in enumerate(section_nums, 1):
            print(f"\n[{i}/{len(section_nums)}] Section {section_num}")
            print("-" * 60)

            status = self.check_section_status(section_num)
            print(f"  Status: scraped={status['scraped']}, lean={status['has_lean']}, "
                  f"aristotle={status['has_aristotle']}, submitted={status['submitted']}")

            if not status['has_lean']:
                if self.create_skeleton(section_num):
                    stats['created'] += 1
                else:
                    stats['failed'] += 1
                    continue

            if not status['has_aristotle'] or not status['prepared']:
                if self.prepare_section(section_num):
                    stats['prepared'] += 1
                else:
                    stats['failed'] += 1
                    continue

            if submit and not status['submitted']:
                if self.submit_section(section_num):
                    stats['submitted'] += 1
                    if i < len(section_nums) and not self.dry_run:
                        print(f"  ⏳ Waiting 3s...")
                        time.sleep(3)
                else:
                    stats['failed'] += 1

        self.save_progress()

        print(f"\n{'='*80}")
        print(f"SUMMARY")
        print(f"{'='*80}")
        print(f"  Skeletons created: {stats['created']}")
        print(f"  Prepared: {stats['prepared']}")
        print(f"  Submitted: {stats['submitted']}")
        print(f"  Failed: {stats['failed']}")
        print(f"{'='*80}\n")


def main():
    parser = argparse.ArgumentParser(description='Batch formalization system for Phase 1')
    parser.add_argument('--wave', type=int, help='Process entire wave (1-5)')
    parser.add_argument('--sections', type=str, help='Comma-separated section numbers')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be done')
    parser.add_argument('--prepare-only', action='store_true', help='Only prepare, do not submit')
    parser.add_argument('--submit', action='store_true', help='Submit to Aristotle')
    parser.add_argument('--status', action='store_true', help='Show current progress')

    args = parser.parse_args()

    system = BatchFormalizationSystem(dry_run=args.dry_run)

    if args.status:
        print("\n" + "="*80)
        print("BATCH FORMALIZATION PROGRESS")
        print("="*80)
        print(f"Waves completed: {system.progress['waves_completed']}")
        print(f"Skeletons created: {len(system.progress['skeletons_created'])}")
        print(f"Prepared: {len(system.progress['prepared'])}")
        print(f"Submitted: {len(system.progress['submitted'])}")
        print(f"Failed: {len(system.progress['failed'])}")
        print("="*80 + "\n")
        return 0

    if args.wave:
        system.process_wave(args.wave, prepare_only=args.prepare_only, submit=args.submit)
    elif args.sections:
        section_nums = [s.strip() for s in args.sections.split(',')]
        system.process_sections(section_nums, prepare_only=args.prepare_only, submit=args.submit)
    else:
        parser.print_help()
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
