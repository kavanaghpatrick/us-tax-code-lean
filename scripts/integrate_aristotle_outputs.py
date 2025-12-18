#!/usr/bin/env python3
"""
Integrate Aristotle Output Files into Main Sections

Compares *_aristotle_output.lean files with main Section*.lean files and
integrates completed proofs, replacing sorry placeholders.

Usage:
    python scripts/integrate_aristotle_outputs.py --scan       # Show what would be integrated
    python scripts/integrate_aristotle_outputs.py --integrate  # Perform integration
    python scripts/integrate_aristotle_outputs.py --section 61 # Integrate specific section
"""

import argparse
import re
import shutil
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass


@dataclass
class IntegrationCandidate:
    """A section that can be integrated"""
    section: str
    main_file: Path
    output_file: Path
    main_has_sorry: bool
    output_has_sorry: bool
    main_lines: int
    output_lines: int
    recommendation: str  # 'integrate', 'skip', 'review'


class AristotleIntegrator:
    """Integrates Aristotle outputs into main section files"""

    def __init__(self):
        self.project_root = Path(__file__).parent.parent
        self.taxcode_dir = self.project_root / 'src' / 'TaxCode'
        self.backup_dir = self.project_root / 'backups' / 'pre_integration'

    def find_integration_candidates(self) -> List[IntegrationCandidate]:
        """Find all sections with output files that could be integrated"""
        candidates = []

        for output_file in self.taxcode_dir.glob('*_aristotle_output.lean'):
            # Extract section number from filename
            match = re.search(r'Section(\d+(?:_\d+)?)_aristotle_output\.lean', output_file.name)
            if not match:
                continue

            section = match.group(1)
            main_file = self.taxcode_dir / f'Section{section}.lean'

            if not main_file.exists():
                continue

            # Analyze both files
            main_content = main_file.read_text()
            output_content = output_file.read_text()

            main_has_sorry = self._has_real_sorry(main_content)
            output_has_sorry = self._has_real_sorry(output_content)
            output_is_failure = self._is_aristotle_failure(output_content)

            main_lines = len(main_content.split('\n'))
            output_lines = len(output_content.split('\n'))

            # Determine recommendation
            if output_is_failure:
                recommendation = 'failed'  # Aristotle run failed
            elif not main_has_sorry:
                recommendation = 'skip'  # Main already complete
            elif output_has_sorry:
                recommendation = 'review'  # Output also has sorry
            elif output_lines < main_lines * 0.5:
                recommendation = 'review'  # Output much shorter, might be incomplete
            else:
                recommendation = 'integrate'

            candidates.append(IntegrationCandidate(
                section=section,
                main_file=main_file,
                output_file=output_file,
                main_has_sorry=main_has_sorry,
                output_has_sorry=output_has_sorry,
                main_lines=main_lines,
                output_lines=output_lines,
                recommendation=recommendation
            ))

        return sorted(candidates, key=lambda c: self._section_sort_key(c.section))

    def _has_real_sorry(self, content: str) -> bool:
        """Check if content has actual sorry usage (not just comments)"""
        for line in content.split('\n'):
            # Skip comments
            if line.strip().startswith('--'):
                continue
            # Check for sorry keyword
            if re.search(r'\bsorry\b', line):
                # Exclude "without sorry" type comments
                if 'without' in line.lower() and 'sorry' in line.lower():
                    continue
                return True
        return False

    def _is_aristotle_failure(self, content: str) -> bool:
        """Check if output file represents a failed Aristotle run"""
        failure_markers = [
            'Aristotle failed to load',
            'Aristotle encountered an error',
            'failed to prove',
            'compilation failed'
        ]
        return any(marker in content for marker in failure_markers)

    def _section_sort_key(self, section: str) -> Tuple:
        """Sort key for section numbers"""
        parts = section.split('_')
        return tuple(int(p) for p in parts)

    def scan(self) -> Dict:
        """Scan and report integration candidates"""
        candidates = self.find_integration_candidates()

        stats = {
            'total': len(candidates),
            'integrate': 0,
            'skip': 0,
            'review': 0,
            'failed': 0
        }

        print(f"\n{'='*70}")
        print(f"ARISTOTLE OUTPUT INTEGRATION SCAN")
        print(f"{'='*70}\n")

        for rec in ['integrate', 'review', 'failed', 'skip']:
            group = [c for c in candidates if c.recommendation == rec]
            stats[rec] = len(group)

            if rec == 'integrate':
                icon = '✓'
                desc = 'Ready to integrate (output complete, main has sorry)'
            elif rec == 'review':
                icon = '⚠'
                desc = 'Needs review (output may be incomplete)'
            elif rec == 'failed':
                icon = '✗'
                desc = 'Aristotle run failed (needs resubmission)'
            else:
                icon = '○'
                desc = 'Skip (main already complete)'

            print(f"{icon} {rec.upper()}: {len(group)} sections - {desc}")

            if rec != 'skip' and group:
                for c in group[:10]:  # Show first 10
                    sorry_status = f"main:{'sorry' if c.main_has_sorry else 'ok'} out:{'sorry' if c.output_has_sorry else 'ok'}"
                    print(f"   Section{c.section}: {c.main_lines}→{c.output_lines} lines ({sorry_status})")
                if len(group) > 10:
                    print(f"   ... and {len(group)-10} more")
            print()

        print(f"{'='*70}")
        print(f"Summary: {stats['integrate']} ready | {stats['review']} review | {stats['failed']} failed | {stats['skip']} skip")
        print(f"{'='*70}\n")

        return stats

    def integrate_section(self, section: str, dry_run: bool = False) -> bool:
        """Integrate a single section's output into the main file"""
        main_file = self.taxcode_dir / f'Section{section}.lean'
        output_file = self.taxcode_dir / f'Section{section}_aristotle_output.lean'

        if not main_file.exists():
            print(f"  ✗ Main file not found: {main_file.name}")
            return False

        if not output_file.exists():
            print(f"  ✗ Output file not found: {output_file.name}")
            return False

        # Read files
        main_content = main_file.read_text()
        output_content = output_file.read_text()

        # Check if integration makes sense
        main_has_sorry = self._has_real_sorry(main_content)
        output_has_sorry = self._has_real_sorry(output_content)

        if not main_has_sorry:
            print(f"  ○ Section{section}: Main file has no sorry - skipping")
            return False

        if output_has_sorry:
            print(f"  ⚠ Section{section}: Output still has sorry - needs review")
            return False

        if dry_run:
            print(f"  [DRY RUN] Would integrate Section{section}")
            return True

        # Create backup
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        backup_file = self.backup_dir / f'Section{section}.lean.bak'
        shutil.copy(main_file, backup_file)

        # Replace main file with output content
        # But first, clean up any Aristotle headers from output
        clean_output = self._clean_aristotle_output(output_content)
        main_file.write_text(clean_output)

        print(f"  ✓ Section{section}: Integrated ({len(main_content.split(chr(10)))} → {len(clean_output.split(chr(10)))} lines)")
        return True

    def _clean_aristotle_output(self, content: str) -> str:
        """Clean Aristotle output for integration"""
        lines = content.split('\n')
        clean_lines = []
        skip_header = True

        for line in lines:
            # Skip Aristotle metadata header
            if skip_header:
                if line.startswith('/-') or line.startswith('This file was edited by Aristotle'):
                    continue
                if 'Lean version:' in line or 'Mathlib version:' in line:
                    continue
                if 'project request had uuid:' in line:
                    continue
                if 'Aristotle encountered an error' in line:
                    continue
                if line.strip() == '-/':
                    skip_header = False
                    continue
                if line.startswith('import') or line.strip() == '' or line.startswith('/-!'):
                    skip_header = False
                    # Don't continue - include this line

            clean_lines.append(line)

        return '\n'.join(clean_lines)

    def integrate_all(self, dry_run: bool = False, force: bool = False) -> Dict:
        """Integrate all eligible outputs"""
        candidates = self.find_integration_candidates()

        # Filter to only 'integrate' recommendations unless force
        if force:
            to_integrate = [c for c in candidates if c.recommendation in ['integrate', 'review']]
        else:
            to_integrate = [c for c in candidates if c.recommendation == 'integrate']

        print(f"\n{'='*70}")
        print(f"INTEGRATING {len(to_integrate)} SECTIONS")
        print(f"{'='*70}\n")

        success = 0
        failed = 0

        for candidate in to_integrate:
            if self.integrate_section(candidate.section, dry_run):
                success += 1
            else:
                failed += 1

        print(f"\n{'='*70}")
        print(f"Integration complete: {success} success, {failed} failed/skipped")
        print(f"{'='*70}\n")

        return {'success': success, 'failed': failed}


def main():
    parser = argparse.ArgumentParser(description='Integrate Aristotle outputs into main sections')
    parser.add_argument('--scan', action='store_true', help='Scan and report candidates')
    parser.add_argument('--integrate', action='store_true', help='Perform integration')
    parser.add_argument('--section', type=str, help='Integrate specific section')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be done')
    parser.add_argument('--force', action='store_true', help='Include review candidates')

    args = parser.parse_args()

    integrator = AristotleIntegrator()

    if args.scan:
        integrator.scan()
    elif args.section:
        integrator.integrate_section(args.section, args.dry_run)
    elif args.integrate:
        integrator.integrate_all(args.dry_run, args.force)
    else:
        # Default: scan
        integrator.scan()


if __name__ == '__main__':
    main()
