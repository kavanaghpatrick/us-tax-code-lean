#!/usr/bin/env python3
"""
IRC Section Contradiction Detector

Analyzes formalized IRC sections to find potential contradictions where
two sections could give opposite answers for the same scenario.

Approach:
1. Categorize sections by topic (income, exclusions, deductions, credits)
2. Extract key predicates (isTaxable, isExcluded, isDeductible)
3. Identify pairs that could conflict
4. Generate test scenarios to verify contradictions

Output:
- contradiction_analysis.md (human-readable report)
- potential_contradictions.json (machine-readable data)
"""

import re
import json
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Set, Tuple
from dataclasses import dataclass, asdict

# Path to the TaxCode directory
TAX_CODE_DIR = Path(__file__).parent.parent / "src" / "TaxCode"


@dataclass
class SectionInfo:
    """Information about a formalized IRC section"""
    number: int
    title: str
    category: str  # income, exclusion, deduction, credit, basis, etc.
    predicates: List[str]  # isTaxable, isExcluded, isDeductible, etc.
    structures: List[str]  # Bond, Expense, Transfer, etc.


@dataclass
class PotentialContradiction:
    """A potential contradiction between two sections"""
    section1: int
    section2: int
    conflict_type: str  # "income_vs_exclusion", "deductible_vs_nondeductible", etc.
    description: str
    severity: str  # "high", "medium", "low"


def extract_section_number(filename: str) -> int:
    """Extract section number from filename like 'Section103.lean'"""
    match = re.match(r"Section(\d+)\.lean", filename)
    if match:
        return int(match.group(1))
    return None


def categorize_section(title: str, content: str) -> str:
    """
    Categorize section based on title and content.

    Categories:
    - income: Sections about what's included in gross income
    - exclusion: Sections about what's excluded from income
    - deduction: Sections about deductible expenses
    - credit: Tax credits
    - rate: Tax rate calculations
    - basis: Basis calculations
    - timing: Recognition timing
    - corporate: Corporate-specific rules
    - international: International tax
    - estate: Estate and gift tax
    - other: Everything else
    """
    title_lower = title.lower()
    content_lower = content.lower()

    # Exclusions (§101-139)
    if any(word in title_lower for word in ['exclusion', 'excluded', 'exempt', 'not includible']):
        return 'exclusion'

    # Income (§61-91)
    if any(word in title_lower for word in ['gross income', 'includible', 'taxable income']):
        return 'income'

    # Deductions (§161-199, §211-223)
    if any(word in title_lower for word in ['deduction', 'deductible', 'expense']):
        return 'deduction'

    # Credits (§21-54)
    if 'credit' in title_lower:
        return 'credit'

    # Rates (§1, §11, §55)
    if any(word in title_lower for word in ['tax imposed', 'rate', 'alternative minimum tax']):
        return 'rate'

    # Basis (§1011-1023)
    if any(word in title_lower for word in ['basis', 'adjusted basis']):
        return 'basis'

    # Corporate (§301-385)
    if any(word in title_lower for word in ['corporation', 'dividend', 'distribution']):
        return 'corporate'

    # Estate/Gift (§2001-2801)
    if any(word in title_lower for word in ['estate', 'gift', 'generation-skipping']):
        return 'estate'

    return 'other'


def extract_predicates(content: str) -> List[str]:
    """
    Extract key predicate functions from Lean code.

    Looks for patterns like:
    - def isTaxable ...
    - def isExcluded ...
    - def isDeductible ...
    - def isTaxExempt ...
    - def calculateTax ...
    """
    predicates = []

    # Pattern: def <name> ...
    pattern = r"def\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*"
    for match in re.finditer(pattern, content):
        pred_name = match.group(1)
        # Filter for tax-relevant predicates
        if any(keyword in pred_name.lower() for keyword in [
            'tax', 'deduct', 'exclude', 'exempt', 'credit', 'income',
            'basis', 'gain', 'loss', 'qualified', 'eligible'
        ]):
            predicates.append(pred_name)

    return predicates


def extract_structures(content: str) -> List[str]:
    """
    Extract structure definitions from Lean code.

    Looks for patterns like:
    - structure Bond where ...
    - structure Expense where ...
    - structure Transfer where ...
    """
    structures = []

    # Pattern: structure <name> where ...
    pattern = r"structure\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+where"
    for match in re.finditer(pattern, content):
        structures.append(match.group(1))

    return structures


def analyze_sections() -> List[SectionInfo]:
    """Analyze all sections and extract relevant information"""
    sections = []

    for lean_file in TAX_CODE_DIR.glob("Section*.lean"):
        section_num = extract_section_number(lean_file.name)
        if section_num is None:
            continue

        content = lean_file.read_text()

        # Extract title
        title_match = re.search(r"IRC Section \d+ - (.+)", content)
        title = title_match.group(1).strip() if title_match else "Unknown"

        # Categorize and extract predicates
        category = categorize_section(title, content)
        predicates = extract_predicates(content)
        structures = extract_structures(content)

        sections.append(SectionInfo(
            number=section_num,
            title=title,
            category=category,
            predicates=predicates,
            structures=structures
        ))

    return sections


def detect_contradictions(sections: List[SectionInfo]) -> List[PotentialContradiction]:
    """
    Detect potential contradictions between sections.

    Contradiction types:
    1. Income vs. Exclusion: One section includes in income, another excludes
    2. Deductible vs. Non-deductible: One allows deduction, another denies
    3. Rate conflicts: Different sections apply different tax rates
    4. Timing conflicts: Different recognition timing
    """
    contradictions = []

    # Group sections by category
    by_category = defaultdict(list)
    for section in sections:
        by_category[section.category].append(section)

    # Check 1: Income sections vs. Exclusion sections
    # If both deal with the same topic, they might conflict
    income_sections = by_category['income']
    exclusion_sections = by_category['exclusion']

    for inc_sec in income_sections:
        for exc_sec in exclusion_sections:
            # Check if they share common structures or predicates
            common_structs = set(inc_sec.structures) & set(exc_sec.structures)
            if common_structs:
                contradictions.append(PotentialContradiction(
                    section1=inc_sec.number,
                    section2=exc_sec.number,
                    conflict_type='income_vs_exclusion',
                    description=f"§{inc_sec.number} ({inc_sec.title}) may include income that §{exc_sec.number} ({exc_sec.title}) excludes. Common structures: {', '.join(common_structs)}",
                    severity='medium'
                ))

    # Check 2: Multiple sections in same category with conflicting predicates
    # Example: Two deduction sections where one says "deductible" and another says "not deductible"
    for category, secs in by_category.items():
        if len(secs) < 2:
            continue

        # Look for opposing predicates
        for i, sec1 in enumerate(secs):
            for sec2 in secs[i+1:]:
                # Check for predicates that might conflict
                pred1_set = set(p.lower() for p in sec1.predicates)
                pred2_set = set(p.lower() for p in sec2.predicates)

                # Look for opposite patterns
                conflicts = []
                if any('taxable' in p for p in pred1_set) and any('exempt' in p for p in pred2_set):
                    conflicts.append("taxable vs. exempt")
                if any('deductible' in p for p in pred1_set) and any('nondeduct' in p for p in pred2_set):
                    conflicts.append("deductible vs. non-deductible")

                if conflicts:
                    contradictions.append(PotentialContradiction(
                        section1=sec1.number,
                        section2=sec2.number,
                        conflict_type=f'{category}_conflict',
                        description=f"§{sec1.number} and §{sec2.number} may have conflicting rules: {', '.join(conflicts)}",
                        severity='low'
                    ))

    # Check 3: Specific known conflict patterns

    # Pattern: Multiple bond-related sections (from circular references)
    bond_sections = [s for s in sections if 'bond' in s.title.lower()]
    if len(bond_sections) >= 2:
        # Check circular reference group (103, 141, 143, 144, 1394)
        circular_group = [103, 141, 143, 144, 1394]
        circular_secs = [s for s in bond_sections if s.number in circular_group]
        if len(circular_secs) >= 2:
            for i, sec1 in enumerate(circular_secs):
                for sec2 in circular_secs[i+1:]:
                    contradictions.append(PotentialContradiction(
                        section1=sec1.number,
                        section2=sec2.number,
                        conflict_type='circular_reference',
                        description=f"§{sec1.number} and §{sec2.number} are part of circular reference chain - may create ambiguous definitions",
                        severity='high'
                    ))

    # Pattern: Multiple compensation/deduction sections
    comp_sections = [s for s in sections if 'compensation' in s.title.lower() or 'salary' in s.title.lower()]
    if len(comp_sections) >= 2:
        for i, sec1 in enumerate(comp_sections):
            for sec2 in comp_sections[i+1:]:
                contradictions.append(PotentialContradiction(
                    section1=sec1.number,
                    section2=sec2.number,
                    conflict_type='overlapping_rules',
                    description=f"§{sec1.number} ({sec1.title}) and §{sec2.number} ({sec2.title}) both regulate compensation - potential overlap",
                    severity='medium'
                ))

    return contradictions


def generate_report(sections: List[SectionInfo], contradictions: List[PotentialContradiction], output_path: Path):
    """Generate human-readable contradiction analysis report"""
    with open(output_path, 'w') as f:
        f.write("# IRC Section Contradiction Analysis\n\n")
        f.write(f"**Total Sections Analyzed**: {len(sections)}\n\n")
        f.write(f"**Potential Contradictions Found**: {len(contradictions)}\n\n")

        # Summary by category
        by_category = defaultdict(int)
        for section in sections:
            by_category[section.category] += 1

        f.write("## Sections by Category\n\n")
        for category, count in sorted(by_category.items(), key=lambda x: x[1], reverse=True):
            f.write(f"- **{category.capitalize()}**: {count} sections\n")
        f.write("\n")

        # Contradictions by severity
        by_severity = defaultdict(list)
        for contradiction in contradictions:
            by_severity[contradiction.severity].append(contradiction)

        f.write("## Potential Contradictions\n\n")

        for severity in ['high', 'medium', 'low']:
            if severity not in by_severity:
                continue

            f.write(f"### {severity.capitalize()} Severity ({len(by_severity[severity])} found)\n\n")

            for contradiction in by_severity[severity][:20]:  # Limit to top 20
                f.write(f"#### §{contradiction.section1} vs. §{contradiction.section2}\n\n")
                f.write(f"**Type**: {contradiction.conflict_type}\n\n")
                f.write(f"{contradiction.description}\n\n")

            if len(by_severity[severity]) > 20:
                f.write(f"*... and {len(by_severity[severity]) - 20} more*\n\n")

        # Section details
        f.write("## Section Details\n\n")

        for category in sorted(by_category.keys()):
            secs = [s for s in sections if s.category == category]
            if not secs:
                continue

            f.write(f"### {category.capitalize()} ({len(secs)} sections)\n\n")

            for sec in sorted(secs, key=lambda s: s.number)[:10]:  # Top 10 per category
                f.write(f"- **§{sec.number}**: {sec.title}\n")
                if sec.predicates:
                    f.write(f"  - Predicates: {', '.join(sec.predicates[:5])}\n")
                if sec.structures:
                    f.write(f"  - Structures: {', '.join(sec.structures)}\n")

            if len(secs) > 10:
                f.write(f"\n*... and {len(secs) - 10} more*\n")
            f.write("\n")


def main():
    """Main entry point"""
    print("IRC Section Contradiction Detector")
    print("=" * 50)
    print()

    # Analyze sections
    print("Analyzing sections...")
    sections = analyze_sections()
    print(f"✓ Analyzed {len(sections)} sections")
    print()

    # Detect contradictions
    print("Detecting contradictions...")
    contradictions = detect_contradictions(sections)
    print(f"✓ Found {len(contradictions)} potential contradictions")
    print()

    # Group by severity
    by_severity = defaultdict(int)
    for c in contradictions:
        by_severity[c.severity] += 1

    print("Breakdown by severity:")
    for severity in ['high', 'medium', 'low']:
        if severity in by_severity:
            print(f"  - {severity.capitalize()}: {by_severity[severity]}")
    print()

    # Generate outputs
    output_dir = Path(__file__).parent.parent / "analysis"
    output_dir.mkdir(exist_ok=True)

    report_file = output_dir / "contradiction_analysis.md"
    json_file = output_dir / "potential_contradictions.json"

    print("Generating outputs...")
    generate_report(sections, contradictions, report_file)
    print(f"✓ Created {report_file}")

    # Save JSON
    with open(json_file, 'w') as f:
        json.dump([asdict(c) for c in contradictions], f, indent=2)
    print(f"✓ Created {json_file}")
    print()

    print("Done! Review the analysis in:")
    print(f"  {report_file}")


if __name__ == "__main__":
    main()
