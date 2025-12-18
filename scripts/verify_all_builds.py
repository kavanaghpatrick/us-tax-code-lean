#!/usr/bin/env python3
"""
Comprehensive Build Verification for All Tax Code Sections

Builds each section individually and generates a detailed report.

Usage:
    python scripts/verify_all_builds.py                    # Full verification
    python scripts/verify_all_builds.py --quick            # Quick check (parallel, stop on first error batch)
    python scripts/verify_all_builds.py --sections 61,62   # Specific sections only
    python scripts/verify_all_builds.py --report           # Just show last report
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple


@dataclass
class BuildResult:
    """Result of building a single section"""
    section: str
    success: bool
    duration_ms: int
    warnings: List[str]
    errors: List[str]
    has_sorry: bool


class BuildVerifier:
    """Verifies all sections build successfully"""

    def __init__(self, project_root: Path = None):
        self.project_root = project_root or Path(__file__).parent.parent
        self.taxcode_dir = self.project_root / 'src' / 'TaxCode'
        self.report_file = self.project_root / 'data' / 'build_verification_report.json'
        self.results: Dict[str, BuildResult] = {}

    def get_section_files(self) -> List[Path]:
        """Get all main section files (excluding _aristotle, _output, _backup)"""
        all_files = list(self.taxcode_dir.glob('Section*.lean'))
        # Filter out derivative files
        main_files = [
            f for f in all_files
            if not any(x in f.name for x in ['_aristotle', '_output', '_backup'])
        ]
        return sorted(main_files, key=lambda f: self._section_sort_key(f.stem))

    def _section_sort_key(self, stem: str) -> Tuple:
        """Sort key for section names (handles Section1, Section61, Section1031, etc.)"""
        match = re.search(r'Section(\d+)(?:_(\d+))?', stem)
        if match:
            main = int(match.group(1))
            sub = int(match.group(2)) if match.group(2) else 0
            return (main, sub)
        return (999999, 0)

    def build_section(self, section_file: Path) -> BuildResult:
        """Build a single section and return the result"""
        section_name = section_file.stem  # e.g., "Section61"
        module_name = f"TaxCode.{section_name}"

        start_time = time.time()

        try:
            result = subprocess.run(
                ['lake', 'build', module_name],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=120  # 2 minute timeout per section
            )

            duration_ms = int((time.time() - start_time) * 1000)

            # Parse output for warnings and errors
            output = result.stdout + result.stderr
            warnings = []
            errors = []
            has_sorry = False

            for line in output.split('\n'):
                if 'warning:' in line.lower():
                    warnings.append(line.strip())
                    if 'sorry' in line.lower():
                        has_sorry = True
                elif 'error:' in line.lower():
                    errors.append(line.strip())

            success = result.returncode == 0

            return BuildResult(
                section=section_name,
                success=success,
                duration_ms=duration_ms,
                warnings=warnings,
                errors=errors,
                has_sorry=has_sorry
            )

        except subprocess.TimeoutExpired:
            return BuildResult(
                section=section_name,
                success=False,
                duration_ms=120000,
                warnings=[],
                errors=["Build timeout (>120s)"],
                has_sorry=False
            )
        except Exception as e:
            return BuildResult(
                section=section_name,
                success=False,
                duration_ms=0,
                warnings=[],
                errors=[str(e)],
                has_sorry=False
            )

    def verify_all(self, parallel: int = 4, sections: Optional[List[str]] = None) -> Dict:
        """Verify all sections build successfully"""
        section_files = self.get_section_files()

        # Filter to specific sections if requested
        if sections:
            section_set = set(f"Section{s}" for s in sections)
            section_files = [f for f in section_files if f.stem in section_set]

        total = len(section_files)
        print(f"\n{'='*60}")
        print(f"BUILD VERIFICATION: {total} sections")
        print(f"{'='*60}\n")

        start_time = time.time()
        completed = 0
        successes = 0
        failures = 0
        with_sorry = 0

        if parallel > 1:
            # Parallel execution
            with ThreadPoolExecutor(max_workers=parallel) as executor:
                future_to_file = {
                    executor.submit(self.build_section, f): f
                    for f in section_files
                }

                for future in as_completed(future_to_file):
                    result = future.result()
                    self.results[result.section] = result
                    completed += 1

                    if result.success:
                        successes += 1
                        icon = "✓" if not result.has_sorry else "⚠"
                        if result.has_sorry:
                            with_sorry += 1
                    else:
                        failures += 1
                        icon = "✗"

                    # Progress update
                    pct = (completed / total) * 100
                    print(f"\r[{completed}/{total}] {pct:.1f}% | ✓ {successes} | ✗ {failures} | ⚠ {with_sorry} sorry | {result.section}", end="")

        else:
            # Sequential execution
            for section_file in section_files:
                result = self.build_section(section_file)
                self.results[result.section] = result
                completed += 1

                if result.success:
                    successes += 1
                    icon = "✓" if not result.has_sorry else "⚠"
                    if result.has_sorry:
                        with_sorry += 1
                else:
                    failures += 1
                    icon = "✗"

                pct = (completed / total) * 100
                print(f"\r[{completed}/{total}] {pct:.1f}% | ✓ {successes} | ✗ {failures} | ⚠ {with_sorry} sorry | {result.section}", end="")

        total_time = time.time() - start_time
        print(f"\n\n{'='*60}")
        print(f"VERIFICATION COMPLETE in {total_time:.1f}s")
        print(f"{'='*60}")

        # Generate summary
        summary = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'total_sections': total,
            'successes': successes,
            'failures': failures,
            'with_sorry': with_sorry,
            'success_rate': f"{(successes/total)*100:.1f}%" if total > 0 else "N/A",
            'total_time_seconds': round(total_time, 1),
            'failed_sections': [
                {'section': r.section, 'errors': r.errors[:3]}  # First 3 errors
                for r in self.results.values() if not r.success
            ],
            'sorry_sections': [
                r.section for r in self.results.values() if r.has_sorry
            ]
        }

        # Save report
        self.save_report(summary)

        # Print summary
        print(f"\nSuccesses: {successes}/{total} ({summary['success_rate']})")
        print(f"Failures:  {failures}")
        print(f"With sorry: {with_sorry}")

        if failures > 0:
            print(f"\n❌ FAILED SECTIONS ({failures}):")
            for r in sorted(self.results.values(), key=lambda x: self._section_sort_key(x.section)):
                if not r.success:
                    error_preview = r.errors[0][:80] + "..." if r.errors and len(r.errors[0]) > 80 else (r.errors[0] if r.errors else "Unknown error")
                    print(f"  • {r.section}: {error_preview}")

        if with_sorry > 0:
            print(f"\n⚠ SECTIONS WITH SORRY ({with_sorry}):")
            sorry_sections = [r.section for r in self.results.values() if r.has_sorry]
            for i in range(0, len(sorry_sections), 10):
                print(f"  {', '.join(sorry_sections[i:i+10])}")

        return summary

    def save_report(self, summary: Dict):
        """Save detailed report to disk"""
        self.report_file.parent.mkdir(parents=True, exist_ok=True)

        report = {
            'summary': summary,
            'results': {k: asdict(v) for k, v in self.results.items()}
        }

        with open(self.report_file, 'w') as f:
            json.dump(report, f, indent=2)

        print(f"\nReport saved: {self.report_file}")

    def show_report(self):
        """Show the last verification report"""
        if not self.report_file.exists():
            print("No verification report found. Run verification first.")
            return

        with open(self.report_file) as f:
            report = json.load(f)

        summary = report['summary']
        print(f"\n{'='*60}")
        print(f"LAST BUILD VERIFICATION REPORT")
        print(f"{'='*60}")
        print(f"Timestamp: {summary['timestamp']}")
        print(f"Total sections: {summary['total_sections']}")
        print(f"Success rate: {summary['success_rate']}")
        print(f"Successes: {summary['successes']}")
        print(f"Failures: {summary['failures']}")
        print(f"With sorry: {summary['with_sorry']}")
        print(f"Total time: {summary['total_time_seconds']}s")

        if summary['failed_sections']:
            print(f"\n❌ FAILED SECTIONS:")
            for item in summary['failed_sections']:
                print(f"  • {item['section']}")
                for err in item['errors'][:2]:
                    print(f"      {err[:100]}")

        if summary['sorry_sections']:
            print(f"\n⚠ SECTIONS WITH SORRY:")
            sections = summary['sorry_sections']
            for i in range(0, len(sections), 10):
                print(f"  {', '.join(sections[i:i+10])}")


def main():
    parser = argparse.ArgumentParser(description='Verify all sections build successfully')
    parser.add_argument('--quick', action='store_true', help='Quick parallel check')
    parser.add_argument('--sections', type=str, help='Comma-separated section numbers')
    parser.add_argument('--report', action='store_true', help='Show last report')
    parser.add_argument('--parallel', type=int, default=4, help='Number of parallel builds')

    args = parser.parse_args()

    verifier = BuildVerifier()

    if args.report:
        verifier.show_report()
        return 0

    sections = None
    if args.sections:
        sections = [s.strip() for s in args.sections.split(',')]

    summary = verifier.verify_all(
        parallel=args.parallel if args.quick else 1,
        sections=sections
    )

    # Return non-zero if any failures
    return 0 if summary['failures'] == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
