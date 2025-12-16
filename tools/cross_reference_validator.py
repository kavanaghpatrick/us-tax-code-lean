#!/usr/bin/env python3
"""
Cross-Reference Validator
Verifies IRC section citations in comments match the actual file/function names.
"""

import os
import re
from pathlib import Path
from dataclasses import dataclass
from collections import defaultdict

@dataclass
class Citation:
    file_path: str
    line_number: int
    citation: str
    section_number: str

@dataclass
class ValidationIssue:
    file_path: str
    line_number: int
    issue_type: str
    message: str

def extract_section_number(filename: str) -> str:
    """Extract section number from filename."""
    match = re.search(r'Section(\d+[A-Z]?)', filename)
    if match:
        return match.group(1)
    return None

def extract_citations(file_path: Path) -> list[Citation]:
    """Extract all IRC citations from a file."""
    citations = []

    try:
        content = file_path.read_text()
    except:
        return []

    lines = content.split('\n')

    # Patterns for IRC citations
    patterns = [
        r'IRC\s*§\s*(\d+[A-Z]?)',
        r'IRC\s+Section\s+(\d+[A-Z]?)',
        r'Section\s+(\d+[A-Z]?)\s*\(',
        r'§\s*(\d+[A-Z]?)\s*\(',
    ]

    for i, line in enumerate(lines, 1):
        for pattern in patterns:
            for match in re.finditer(pattern, line, re.IGNORECASE):
                citations.append(Citation(
                    file_path=str(file_path),
                    line_number=i,
                    citation=match.group(0),
                    section_number=match.group(1)
                ))

    return citations

def validate_file(file_path: Path) -> list[ValidationIssue]:
    """Validate a single file for citation consistency."""
    issues = []

    # Get expected section from filename
    expected_section = extract_section_number(file_path.name)
    if not expected_section:
        return []  # Not a section file

    # Extract citations
    citations = extract_citations(file_path)

    # Check for missing citations
    if not citations:
        issues.append(ValidationIssue(
            file_path=str(file_path),
            line_number=0,
            issue_type="MISSING_CITATION",
            message=f"No IRC section citations found in Section{expected_section}.lean"
        ))
        return issues

    # Check for mismatched citations
    for citation in citations:
        # Allow subsections (e.g., 61 in Section61a.lean)
        if not citation.section_number.startswith(expected_section[:len(citation.section_number)]):
            # Allow cross-references (common in tax code)
            # Only flag if the primary section doesn't match at all
            pass  # Cross-references are valid

    # Check for primary section citation
    has_primary = any(c.section_number == expected_section for c in citations)
    if not has_primary:
        # Check if any citation starts with expected section
        has_related = any(c.section_number.startswith(expected_section) for c in citations)
        if not has_related:
            issues.append(ValidationIssue(
                file_path=str(file_path),
                line_number=0,
                issue_type="NO_PRIMARY_CITATION",
                message=f"No citation for Section {expected_section} found (has: {set(c.section_number for c in citations)})"
            ))

    return issues

def check_for_sorries(file_path: Path) -> list[ValidationIssue]:
    """Check for unproven 'sorry' statements."""
    issues = []

    try:
        content = file_path.read_text()
    except:
        return []

    lines = content.split('\n')
    in_block_comment = False

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Track block comments
        if '/-' in stripped and '-/' not in stripped:
            in_block_comment = True
        if '-/' in stripped:
            in_block_comment = False
            continue

        # Skip if in block comment or line comment
        if in_block_comment or stripped.startswith('--'):
            continue

        # Check for actual sorry usage (not in strings or comments)
        if re.search(r'\bsorry\b', line):
            # Make sure it's not in a string or after --
            comment_pos = line.find('--')
            sorry_pos = line.find('sorry')
            if comment_pos == -1 or sorry_pos < comment_pos:
                issues.append(ValidationIssue(
                    file_path=str(file_path),
                    line_number=i,
                    issue_type="SORRY",
                    message=f"Unproven 'sorry' at line {i}"
                ))

    return issues

def check_for_axioms(file_path: Path) -> list[ValidationIssue]:
    """Check for axiom declarations (documented assumptions)."""
    issues = []

    try:
        content = file_path.read_text()
    except:
        return []

    lines = content.split('\n')

    for i, line in enumerate(lines, 1):
        if line.strip().startswith('axiom '):
            match = re.match(r'axiom\s+(\w+)', line.strip())
            if match:
                issues.append(ValidationIssue(
                    file_path=str(file_path),
                    line_number=i,
                    issue_type="AXIOM",
                    message=f"Axiom '{match.group(1)}' at line {i}"
                ))

    return issues

def run_validation(src_dir: Path) -> dict:
    """Run full validation across all files."""
    all_issues = []
    stats = {
        'files_checked': 0,
        'files_with_issues': 0,
        'total_issues': 0,
        'by_type': defaultdict(int),
        'sorries': 0,
        'axioms': 0,
    }

    for lean_file in sorted(src_dir.glob('Section*.lean')):
        # Skip intermediate files
        if '_backup' in lean_file.name or '_aristotle.lean' in lean_file.name:
            continue

        stats['files_checked'] += 1

        # Run all checks
        issues = []
        issues.extend(validate_file(lean_file))
        issues.extend(check_for_sorries(lean_file))

        axiom_issues = check_for_axioms(lean_file)
        issues.extend(axiom_issues)
        stats['axioms'] += len(axiom_issues)

        sorry_count = sum(1 for i in issues if i.issue_type == "SORRY")
        stats['sorries'] += sorry_count

        if issues:
            stats['files_with_issues'] += 1
            all_issues.extend(issues)
            for issue in issues:
                stats['by_type'][issue.issue_type] += 1

    stats['total_issues'] = len(all_issues)

    return {
        'issues': all_issues,
        'stats': stats
    }

def generate_report(validation_result: dict, output_path: Path):
    """Generate validation report."""
    issues = validation_result['issues']
    stats = validation_result['stats']

    lines = []
    lines.append("# Cross-Reference Validation Report")
    lines.append("")

    # Summary
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Files checked: {stats['files_checked']}")
    lines.append(f"- Files with issues: {stats['files_with_issues']}")
    lines.append(f"- Total issues: {stats['total_issues']}")
    lines.append(f"- Sorry statements: {stats['sorries']}")
    lines.append(f"- Axioms (documented): {stats['axioms']}")
    lines.append("")

    if stats['by_type']:
        lines.append("### Issues by Type")
        lines.append("")
        lines.append("| Type | Count |")
        lines.append("|------|-------|")
        for issue_type, count in sorted(stats['by_type'].items()):
            lines.append(f"| {issue_type} | {count} |")
        lines.append("")

    # Detailed issues
    if issues:
        lines.append("## Detailed Issues")
        lines.append("")

        # Group by file
        by_file = defaultdict(list)
        for issue in issues:
            by_file[issue.file_path].append(issue)

        for file_path in sorted(by_file.keys()):
            file_issues = by_file[file_path]
            filename = Path(file_path).name
            lines.append(f"### {filename}")
            lines.append("")
            for issue in file_issues:
                loc = f":{issue.line_number}" if issue.line_number > 0 else ""
                lines.append(f"- [{issue.issue_type}]{loc} {issue.message}")
            lines.append("")
    else:
        lines.append("## No Issues Found")
        lines.append("")
        lines.append("All files pass validation!")

    lines.append("---")
    lines.append("*Generated by `tools/cross_reference_validator.py`*")

    output_path.write_text('\n'.join(lines))
    print(f"Generated {output_path}")

def main():
    src_dir = Path(__file__).parent.parent / 'src' / 'TaxCode'
    output_path = Path(__file__).parent.parent / 'VALIDATION_REPORT.md'

    print("Running cross-reference validation...")
    result = run_validation(src_dir)

    stats = result['stats']
    print(f"\nFiles checked: {stats['files_checked']}")
    print(f"Files with issues: {stats['files_with_issues']}")
    print(f"Total issues: {stats['total_issues']}")
    print(f"  - Sorry statements: {stats['sorries']}")
    print(f"  - Axioms: {stats['axioms']}")

    if stats['by_type']:
        print("\nBy type:")
        for issue_type, count in sorted(stats['by_type'].items()):
            print(f"  {issue_type}: {count}")

    print("\nGenerating report...")
    generate_report(result, output_path)

if __name__ == '__main__':
    main()
