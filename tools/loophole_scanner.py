#!/usr/bin/env python3
"""
Tax Code Loophole Scanner - Static Analysis for Lean Formalizations

Scans Lean files for patterns that indicate potential loopholes:
1. Threshold cliffs (comparisons with constants)
2. Vacuous truth (.all/.any on potentially empty lists)
3. Division-by-zero guards
4. Short-circuit logic
5. Cross-section references
"""

import re
import os
import json
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from collections import defaultdict

@dataclass
class Finding:
    category: str
    file: str
    line: int
    code: str
    description: str
    severity: str  # "high", "medium", "low"

@dataclass
class ScanResults:
    findings: List[Finding] = field(default_factory=list)
    thresholds: Dict[str, List[Tuple[str, int, str]]] = field(default_factory=lambda: defaultdict(list))
    cross_refs: Dict[str, List[str]] = field(default_factory=lambda: defaultdict(list))

    def add(self, finding: Finding):
        self.findings.append(finding)

    def summary(self) -> Dict:
        by_category = defaultdict(list)
        by_severity = defaultdict(list)
        for f in self.findings:
            by_category[f.category].append(f)
            by_severity[f.severity].append(f)
        return {
            "total": len(self.findings),
            "by_category": {k: len(v) for k, v in by_category.items()},
            "by_severity": {k: len(v) for k, v in by_severity.items()},
            "thresholds_found": sum(len(v) for v in self.thresholds.values()),
            "cross_references": sum(len(v) for v in self.cross_refs.values()),
        }


class LoopholeScanner:
    def __init__(self, src_dir: str):
        self.src_dir = Path(src_dir)
        self.results = ScanResults()

        # Patterns to detect
        self.patterns = {
            # Threshold comparisons - potential cliff effects
            "threshold_gte": re.compile(r'[>≥]=?\s*\(?(\d+)\s*[:/]\s*(\d+)\)?'),
            "threshold_lte": re.compile(r'[<≤]=?\s*\(?(\d+)\s*[:/]\s*(\d+)\)?'),
            "threshold_const": re.compile(r'(threshold|Threshold|THRESHOLD)\s*[:=]\s*(\d+)'),
            "percentage": re.compile(r'(\d+)\s*/\s*100'),

            # Vacuous truth - .all/.any on lists
            "vacuous_all": re.compile(r'\.all\s+fun'),
            "vacuous_any": re.compile(r'\.any\s+fun'),
            "list_filter": re.compile(r'\.filter\s*\('),
            "empty_list_check": re.compile(r'\.isEmpty|\.length\s*[=!]=\s*0|== \[\]'),

            # Division by zero guards
            "div_zero_guard": re.compile(r'if\s+\w+\s*[=!]=\s*0\s+then\s+0\s+else'),
            "div_zero_guard2": re.compile(r'if\s+\w+\s*=\s*0\s+then\s+0'),

            # Short-circuit logic
            "or_true": re.compile(r'\|\|\s*true'),
            "and_false": re.compile(r'&&\s*false'),
            "getD_false": re.compile(r'\.getD\s+false'),
            "getD_true": re.compile(r'\.getD\s+true'),

            # Cross-section references
            "section_ref": re.compile(r'[§](\d+)(?:\([a-z]\))?|Section\s*(\d+)|IRC\s*§?\s*(\d+)'),

            # Loophole comments (already identified)
            "loophole_comment": re.compile(r'LOOPHOLE|loophole|-- Note:|vacuous|cliff', re.IGNORECASE),

            # Exception patterns
            "exception_pattern": re.compile(r'exception|Exception|excepted|Excepted'),

            # Max/min which can create cliffs
            "max_min": re.compile(r'\bmax\b|\bmin\b|Int\.max|Int\.min'),
        }

    def scan_file(self, filepath: Path) -> None:
        """Scan a single Lean file for loophole patterns."""
        try:
            content = filepath.read_text()
        except Exception as e:
            print(f"Error reading {filepath}: {e}")
            return

        lines = content.split('\n')
        filename = filepath.name

        for line_num, line in enumerate(lines, 1):
            self._check_thresholds(filename, line_num, line)
            self._check_vacuous_truth(filename, line_num, line)
            self._check_division_guards(filename, line_num, line)
            self._check_short_circuits(filename, line_num, line)
            self._check_cross_refs(filename, line_num, line)
            self._check_existing_loopholes(filename, line_num, line)
            self._check_exceptions(filename, line_num, line)
            self._check_max_min(filename, line_num, line)

    def _check_thresholds(self, file: str, line: int, code: str) -> None:
        """Find threshold constants that could create cliff effects."""
        # Look for percentage thresholds
        for match in self.patterns["percentage"].finditer(code):
            pct = int(match.group(1))
            if pct in [5, 10, 20, 25, 50, 70, 75, 90, 95]:  # Common tax thresholds
                self.results.thresholds[file].append((code.strip(), line, f"{pct}%"))
                self.results.add(Finding(
                    category="threshold_cliff",
                    file=file, line=line,
                    code=code.strip(),
                    description=f"Threshold at {pct}% - potential cliff effect",
                    severity="medium"
                ))

        # Look for named thresholds
        match = self.patterns["threshold_const"].search(code)
        if match:
            self.results.add(Finding(
                category="threshold_cliff",
                file=file, line=line,
                code=code.strip(),
                description=f"Named threshold constant: {match.group(0)}",
                severity="medium"
            ))

    def _check_vacuous_truth(self, file: str, line: int, code: str) -> None:
        """Find .all/.any on lists that could be empty (vacuous truth)."""
        if self.patterns["vacuous_all"].search(code):
            self.results.add(Finding(
                category="vacuous_truth",
                file=file, line=line,
                code=code.strip(),
                description=".all on list - returns true for empty list (vacuous truth)",
                severity="high"
            ))
        if self.patterns["vacuous_any"].search(code):
            self.results.add(Finding(
                category="vacuous_truth",
                file=file, line=line,
                code=code.strip(),
                description=".any on list - returns false for empty list",
                severity="medium"
            ))

    def _check_division_guards(self, file: str, line: int, code: str) -> None:
        """Find division-by-zero guards that return 0."""
        if self.patterns["div_zero_guard"].search(code) or self.patterns["div_zero_guard2"].search(code):
            self.results.add(Finding(
                category="division_guard",
                file=file, line=line,
                code=code.strip(),
                description="Division-by-zero guard returns 0 - could be exploited with zero denominators",
                severity="medium"
            ))

    def _check_short_circuits(self, file: str, line: int, code: str) -> None:
        """Find short-circuit logic patterns."""
        if self.patterns["getD_false"].search(code):
            self.results.add(Finding(
                category="short_circuit",
                file=file, line=line,
                code=code.strip(),
                description=".getD false - None becomes false (may bypass check)",
                severity="low"
            ))
        if self.patterns["getD_true"].search(code):
            self.results.add(Finding(
                category="short_circuit",
                file=file, line=line,
                code=code.strip(),
                description=".getD true - None becomes true (may pass check vacuously)",
                severity="medium"
            ))

    def _check_cross_refs(self, file: str, line: int, code: str) -> None:
        """Find cross-references to other IRC sections."""
        for match in self.patterns["section_ref"].finditer(code):
            section = match.group(1) or match.group(2) or match.group(3)
            if section:
                self.results.cross_refs[file].append(f"§{section}")

    def _check_existing_loopholes(self, file: str, line: int, code: str) -> None:
        """Find comments that already identify loopholes."""
        if self.patterns["loophole_comment"].search(code):
            self.results.add(Finding(
                category="documented_loophole",
                file=file, line=line,
                code=code.strip(),
                description="Existing loophole documentation found",
                severity="high"
            ))

    def _check_exceptions(self, file: str, line: int, code: str) -> None:
        """Find exception patterns that could be exploited."""
        if self.patterns["exception_pattern"].search(code):
            # Only flag if it looks like a function/definition, not just a comment
            if 'def ' in code or 'Exception' in code or 'excepted' in code.lower():
                self.results.add(Finding(
                    category="exception_rule",
                    file=file, line=line,
                    code=code.strip(),
                    description="Exception rule - may provide planning opportunity",
                    severity="low"
                ))

    def _check_max_min(self, file: str, line: int, code: str) -> None:
        """Find max/min usage which can create floor/ceiling effects."""
        if self.patterns["max_min"].search(code):
            if 'max' in code.lower() and ('0' in code or 'zero' in code.lower()):
                self.results.add(Finding(
                    category="floor_ceiling",
                    file=file, line=line,
                    code=code.strip(),
                    description="max with 0 creates floor - negative values become 0",
                    severity="low"
                ))

    def scan_all(self) -> ScanResults:
        """Scan all Lean files in the source directory."""
        lean_files = list(self.src_dir.glob("**/*.lean"))
        print(f"Scanning {len(lean_files)} Lean files...")

        for filepath in lean_files:
            # Skip backup and output files
            if '_backup' in filepath.name or '_output' in filepath.name:
                continue
            self.scan_file(filepath)

        return self.results

    def report(self) -> str:
        """Generate a detailed report of findings."""
        lines = []
        lines.append("=" * 70)
        lines.append("TAX CODE LOOPHOLE SCANNER - STATIC ANALYSIS REPORT")
        lines.append("=" * 70)
        lines.append("")

        summary = self.results.summary()
        lines.append(f"Total findings: {summary['total']}")
        lines.append("")
        lines.append("By Category:")
        for cat, count in sorted(summary['by_category'].items(), key=lambda x: -x[1]):
            lines.append(f"  {cat}: {count}")
        lines.append("")
        lines.append("By Severity:")
        for sev, count in sorted(summary['by_severity'].items()):
            lines.append(f"  {sev}: {count}")
        lines.append("")
        lines.append(f"Threshold constants found: {summary['thresholds_found']}")
        lines.append(f"Cross-section references: {summary['cross_references']}")
        lines.append("")

        # Group findings by file and category
        by_file = defaultdict(list)
        for f in self.results.findings:
            by_file[f.file].append(f)

        lines.append("-" * 70)
        lines.append("DETAILED FINDINGS")
        lines.append("-" * 70)

        for file in sorted(by_file.keys()):
            findings = by_file[file]
            high_sev = [f for f in findings if f.severity == "high"]
            if not high_sev and len(findings) < 3:
                continue  # Skip files with only low-severity findings

            lines.append(f"\n### {file}")
            lines.append("")

            # Sort by severity then line number
            sev_order = {"high": 0, "medium": 1, "low": 2}
            for finding in sorted(findings, key=lambda x: (sev_order[x.severity], x.line)):
                if finding.severity == "low":
                    continue  # Skip low severity in detailed report
                lines.append(f"  [{finding.severity.upper()}] Line {finding.line}: {finding.category}")
                lines.append(f"    {finding.description}")
                # Truncate long code lines
                code = finding.code[:80] + "..." if len(finding.code) > 80 else finding.code
                lines.append(f"    Code: {code}")
                lines.append("")

        # Cross-reference analysis
        lines.append("-" * 70)
        lines.append("CROSS-SECTION INTERACTIONS")
        lines.append("-" * 70)
        lines.append("")

        # Find sections that reference each other
        all_refs = defaultdict(set)
        for file, refs in self.results.cross_refs.items():
            section_match = re.search(r'Section(\d+)', file)
            if section_match:
                src_section = section_match.group(1)
                for ref in refs:
                    ref_num = re.search(r'(\d+)', ref)
                    if ref_num and ref_num.group(1) != src_section:
                        all_refs[src_section].add(ref_num.group(1))

        for src, targets in sorted(all_refs.items()):
            if len(targets) > 2:
                lines.append(f"  §{src} references: {', '.join(f'§{t}' for t in sorted(targets))}")

        return "\n".join(lines)


def main():
    import sys

    # Default to TaxCode directory
    src_dir = sys.argv[1] if len(sys.argv) > 1 else "src/TaxCode"

    scanner = LoopholeScanner(src_dir)
    results = scanner.scan_all()

    # Print report
    report = scanner.report()
    print(report)

    # Save detailed JSON results
    json_output = {
        "summary": results.summary(),
        "findings": [
            {
                "category": f.category,
                "file": f.file,
                "line": f.line,
                "code": f.code,
                "description": f.description,
                "severity": f.severity
            }
            for f in results.findings
        ],
        "thresholds": {k: v for k, v in results.thresholds.items()},
        "cross_refs": {k: list(v) for k, v in results.cross_refs.items()},
    }

    output_path = Path("loophole_scan_results.json")
    output_path.write_text(json.dumps(json_output, indent=2))
    print(f"\nDetailed results saved to: {output_path}")


if __name__ == "__main__":
    main()
