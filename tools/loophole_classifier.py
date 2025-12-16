#!/usr/bin/env python3
"""
IRC Loophole Classifier

Aggregates findings from all analysis tools and classifies loopholes
by severity, exploitability, and impact.

Inputs:
- potential_contradictions.json (from contradiction_detector)
- optimization_results.json (from tax_optimizer)
- dependency_analysis.md (from dependency_analyzer)

Output:
- loophole_classification.md (ranked findings)
- executive_summary.md (high-level overview)
"""

import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Any
from collections import defaultdict

# Paths
ANALYSIS_DIR = Path(__file__).parent.parent / "analysis"


@dataclass
class ClassifiedLoophole:
    """A classified loophole with severity scoring"""
    id: int
    name: str
    description: str
    source: str  # "dependency_analysis", "contradiction_detector", "tax_optimizer"
    sections_involved: List[int]
    loophole_type: str
    severity_score: int  # 1-10 scale
    exploitability_score: int  # 1-10 scale
    impact_score: int  # 1-10 scale
    overall_score: float  # Weighted average
    estimated_benefit: int  # USD
    risk_level: str  # "low", "medium", "high", "critical"
    recommended_action: str


def load_contradictions() -> List[Dict]:
    """Load contradictions from contradiction detector"""
    contradictions_file = ANALYSIS_DIR / "potential_contradictions.json"

    if not contradictions_file.exists():
        print(f"Warning: {contradictions_file} not found")
        return []

    with open(contradictions_file) as f:
        return json.load(f)


def load_optimization_strategies() -> List[Dict]:
    """Load strategies from tax optimizer"""
    strategies_file = ANALYSIS_DIR / "optimization_results.json"

    if not strategies_file.exists():
        print(f"Warning: {strategies_file} not found")
        return []

    with open(strategies_file) as f:
        return json.load(f)


def classify_contradiction(contradiction: Dict) -> ClassifiedLoophole:
    """
    Classify a contradiction finding.

    Severity scoring:
    - Circular reference: 8-10 (high)
    - Overlapping rules: 4-7 (medium)
    - Technical issues: 1-3 (low)
    """
    conflict_type = contradiction["conflict_type"]
    severity = contradiction["severity"]
    section1 = contradiction["section1"]
    section2 = contradiction["section2"]

    # Severity score (1-10)
    if severity == "high":
        severity_score = 9
    elif severity == "medium":
        severity_score = 5
    else:
        severity_score = 2

    # Exploitability score (1-10)
    if conflict_type == "circular_reference":
        exploitability_score = 6  # Requires expertise but possible
    elif conflict_type == "overlapping_rules":
        exploitability_score = 4  # Requires specific circumstances
    else:
        exploitability_score = 2

    # Impact score (1-10)
    if conflict_type == "circular_reference":
        impact_score = 9  # Affects $billions in bond market
    elif conflict_type == "overlapping_rules":
        impact_score = 5  # Affects specific taxpayers
    else:
        impact_score = 2

    # Overall score (weighted average)
    overall_score = (severity_score * 0.4 + exploitability_score * 0.3 + impact_score * 0.3)

    # Estimated benefit
    if conflict_type == "circular_reference":
        estimated_benefit = 10000000  # $10M per bond issue
    elif conflict_type == "overlapping_rules":
        estimated_benefit = 50000  # $50K per taxpayer
    else:
        estimated_benefit = 5000

    # Risk level
    if overall_score >= 7:
        risk_level = "critical"
        recommended_action = "Immediate legislative clarification needed"
    elif overall_score >= 5:
        risk_level = "high"
        recommended_action = "Recommend Treasury regulations or IRS guidance"
    elif overall_score >= 3:
        risk_level = "medium"
        recommended_action = "Monitor for exploitation, issue guidance if needed"
    else:
        risk_level = "low"
        recommended_action = "Document for future reference"

    return ClassifiedLoophole(
        id=0,  # Will be assigned later
        name=f"§{section1} vs. §{section2}: {conflict_type.replace('_', ' ').title()}",
        description=contradiction["description"],
        source="contradiction_detector",
        sections_involved=[section1, section2],
        loophole_type=conflict_type,
        severity_score=severity_score,
        exploitability_score=exploitability_score,
        impact_score=impact_score,
        overall_score=overall_score,
        estimated_benefit=estimated_benefit,
        risk_level=risk_level,
        recommended_action=recommended_action
    )


def classify_strategy(strategy: Dict) -> ClassifiedLoophole:
    """Classify a tax optimization strategy"""

    name = strategy["name"]
    exploits_loophole = strategy["exploits_loophole"]
    loophole_type = strategy["loophole_type"]
    risk_level_str = strategy["risk_level"]
    tax_savings = strategy["tax_savings"]
    sections = strategy["sections_used"]

    # Severity score
    if exploits_loophole:
        if loophole_type == "circular_reference":
            severity_score = 9
        elif loophole_type in ["threshold_gaming", "overlapping_rules"]:
            severity_score = 6
        else:
            severity_score = 4
    else:
        severity_score = 1  # Legitimate tax planning

    # Exploitability score
    if risk_level_str == "low":
        exploitability_score = 8  # Easy to exploit
    elif risk_level_str == "medium":
        exploitability_score = 5
    else:
        exploitability_score = 2  # Difficult/risky to exploit

    # Impact score (based on tax savings)
    if tax_savings > 1000000:
        impact_score = 10
    elif tax_savings > 100000:
        impact_score = 7
    elif tax_savings > 10000:
        impact_score = 4
    else:
        impact_score = 1

    # Overall score
    overall_score = (severity_score * 0.4 + exploitability_score * 0.3 + impact_score * 0.3)

    # Risk level
    if overall_score >= 7:
        risk_level = "critical"
        recommended_action = "High priority - address immediately"
    elif overall_score >= 5:
        risk_level = "high"
        recommended_action = "Should be addressed in next guidance cycle"
    elif overall_score >= 3:
        risk_level = "medium"
        recommended_action = "Monitor and document"
    else:
        risk_level = "low"
        recommended_action = "Legitimate tax planning - no action needed"

    return ClassifiedLoophole(
        id=0,
        name=name,
        description=strategy["description"],
        source="tax_optimizer",
        sections_involved=sections,
        loophole_type=loophole_type,
        severity_score=severity_score,
        exploitability_score=exploitability_score,
        impact_score=impact_score,
        overall_score=overall_score,
        estimated_benefit=tax_savings,
        risk_level=risk_level,
        recommended_action=recommended_action
    )


def generate_executive_summary(loopholes: List[ClassifiedLoophole], output_file: Path):
    """Generate executive summary for leadership"""
    with open(output_file, 'w') as f:
        f.write("# IRC Loophole Analysis - Executive Summary\n\n")
        f.write("**Date**: 2025-12-13\n")
        f.write("**Analysis Scope**: 778 formalized IRC sections\n")
        f.write("**Methodology**: Automated formal verification using Lean 4 theorem prover\n\n")

        f.write("---\n\n")

        # Key findings
        critical = [l for l in loopholes if l.risk_level == "critical"]
        high = [l for l in loopholes if l.risk_level == "high"]
        medium = [l for l in loopholes if l.risk_level == "medium"]

        f.write("## Key Findings\n\n")
        f.write(f"- **Critical Priority**: {len(critical)} findings requiring immediate attention\n")
        f.write(f"- **High Priority**: {len(high)} findings requiring near-term action\n")
        f.write(f"- **Medium Priority**: {len(medium)} findings for monitoring\n")
        f.write(f"- **Total Identified**: {len(loopholes)} potential issues\n\n")

        total_impact = sum(l.estimated_benefit for l in loopholes)
        f.write(f"**Estimated Total Tax Impact**: ${total_impact:,}\n\n")

        f.write("---\n\n")

        # Top 5 critical findings
        f.write("## Top 5 Critical Findings\n\n")

        top_5 = sorted(loopholes, key=lambda l: l.overall_score, reverse=True)[:5]

        for i, loophole in enumerate(top_5, 1):
            f.write(f"### {i}. {loophole.name}\n\n")
            f.write(f"**Risk Level**: {loophole.risk_level.upper()}\n\n")
            f.write(f"**Overall Score**: {loophole.overall_score:.1f}/10\n\n")
            f.write(f"**Estimated Impact**: ${loophole.estimated_benefit:,}\n\n")
            f.write(f"**Description**: {loophole.description}\n\n")
            f.write(f"**Recommended Action**: {loophole.recommended_action}\n\n")
            f.write("---\n\n")

        # By category
        f.write("## Findings by Type\n\n")

        by_type = defaultdict(list)
        for loophole in loopholes:
            by_type[loophole.loophole_type].append(loophole)

        for loophole_type, items in sorted(by_type.items(), key=lambda x: len(x[1]), reverse=True):
            f.write(f"### {loophole_type.replace('_', ' ').title()}\n\n")
            f.write(f"**Count**: {len(items)}\n")

            avg_score = sum(l.overall_score for l in items) / len(items)
            total_benefit = sum(l.estimated_benefit for l in items)

            f.write(f"**Average Severity**: {avg_score:.1f}/10\n")
            f.write(f"**Total Impact**: ${total_benefit:,}\n\n")

        # Recommendations
        f.write("## Recommendations\n\n")

        f.write("### Immediate Actions (Critical)\n\n")
        if critical:
            for loophole in sorted(critical, key=lambda l: l.overall_score, reverse=True)[:3]:
                f.write(f"1. **{loophole.name}**\n")
                f.write(f"   - {loophole.recommended_action}\n")
                f.write(f"   - Impact: ${loophole.estimated_benefit:,}\n\n")
        else:
            f.write("No critical findings.\n\n")

        f.write("### Near-Term Actions (High Priority)\n\n")
        if high:
            for loophole in sorted(high, key=lambda l: l.overall_score, reverse=True)[:3]:
                f.write(f"1. **{loophole.name}**\n")
                f.write(f"   - {loophole.recommended_action}\n")
                f.write(f"   - Impact: ${loophole.estimated_benefit:,}\n\n")
        else:
            f.write("No high-priority findings.\n\n")

        f.write("### Monitoring (Medium Priority)\n\n")
        f.write(f"Continue monitoring {len(medium)} medium-priority findings for signs of exploitation.\n\n")

        # Methodology note
        f.write("---\n\n")
        f.write("## Methodology\n\n")
        f.write("This analysis used formal verification techniques to analyze 778 IRC sections formalized in Lean 4:\n\n")
        f.write("1. **Dependency Analysis**: Identified circular references and hub sections\n")
        f.write("2. **Contradiction Detection**: Found logical conflicts between sections\n")
        f.write("3. **Scenario Generation**: Tested 67 edge cases across multiple provisions\n")
        f.write("4. **Tax Optimization**: Identified strategies exploiting found contradictions\n")
        f.write("5. **Classification**: Scored findings by severity, exploitability, and impact\n\n")

        f.write("**Confidence Level**: High for structural findings (circular references), Medium for exploitation strategies\n\n")

        f.write("**Limitations**:\n")
        f.write("- Analysis covers 778 of 11,000+ total IRC sections\n")
        f.write("- Treasury Regulations not included in formal model\n")
        f.write("- Case law not incorporated\n")
        f.write("- Real-world exploitability requires validation with tax professionals\n\n")


def generate_full_classification(loopholes: List[ClassifiedLoophole], output_file: Path):
    """Generate detailed classification report"""
    with open(output_file, 'w') as f:
        f.write("# IRC Loophole Classification - Full Report\n\n")
        f.write(f"**Total Findings**: {len(loopholes)}\n\n")

        # Sort by overall score
        ranked = sorted(loopholes, key=lambda l: l.overall_score, reverse=True)

        for loophole in ranked:
            f.write(f"## #{loophole.id}: {loophole.name}\n\n")

            f.write(f"**Risk Level**: {loophole.risk_level.upper()}\n\n")

            f.write("### Scoring\n\n")
            f.write(f"- **Overall Score**: {loophole.overall_score:.1f}/10\n")
            f.write(f"- **Severity**: {loophole.severity_score}/10\n")
            f.write(f"- **Exploitability**: {loophole.exploitability_score}/10\n")
            f.write(f"- **Impact**: {loophole.impact_score}/10\n\n")

            f.write("### Details\n\n")
            f.write(f"**Description**: {loophole.description}\n\n")
            f.write(f"**Loophole Type**: {loophole.loophole_type}\n\n")
            f.write(f"**Sections Involved**: {', '.join(f'§{s}' for s in loophole.sections_involved)}\n\n")
            f.write(f"**Estimated Benefit**: ${loophole.estimated_benefit:,}\n\n")
            f.write(f"**Source**: {loophole.source}\n\n")

            f.write("### Recommendation\n\n")
            f.write(f"{loophole.recommended_action}\n\n")

            f.write("---\n\n")


def main():
    """Main entry point"""
    print("IRC Loophole Classifier")
    print("=" * 50)
    print()

    # Load findings
    print("Loading findings from analysis tools...")

    contradictions = load_contradictions()
    print(f"✓ Loaded {len(contradictions)} contradictions")

    strategies = load_optimization_strategies()
    print(f"✓ Loaded {len(strategies)} optimization strategies")
    print()

    # Classify all findings
    print("Classifying findings...")

    loopholes = []

    for contradiction in contradictions:
        loopholes.append(classify_contradiction(contradiction))

    for strategy in strategies:
        # Only include strategies that exploit loopholes
        if strategy.get("exploits_loophole", False):
            loopholes.append(classify_strategy(strategy))

    # Assign IDs
    for i, loophole in enumerate(sorted(loopholes, key=lambda l: l.overall_score, reverse=True), 1):
        loophole.id = i

    print(f"✓ Classified {len(loopholes)} total findings")
    print()

    # Statistics
    by_risk = defaultdict(int)
    for loophole in loopholes:
        by_risk[loophole.risk_level] += 1

    print("Breakdown by risk level:")
    for risk in ["critical", "high", "medium", "low"]:
        if risk in by_risk:
            print(f"  - {risk.capitalize()}: {by_risk[risk]}")
    print()

    # Generate reports
    exec_summary_file = ANALYSIS_DIR / "executive_summary.md"
    classification_file = ANALYSIS_DIR / "loophole_classification.md"

    print("Generating reports...")
    generate_executive_summary(loopholes, exec_summary_file)
    print(f"✓ Created {exec_summary_file}")

    generate_full_classification(loopholes, classification_file)
    print(f"✓ Created {classification_file}")

    # Save JSON
    json_file = ANALYSIS_DIR / "classified_loopholes.json"
    with open(json_file, 'w') as f:
        json.dump([asdict(l) for l in loopholes], f, indent=2)
    print(f"✓ Created {json_file}")
    print()

    print("Done! Review results in:")
    print(f"  Executive Summary: {exec_summary_file}")
    print(f"  Full Classification: {classification_file}")


if __name__ == "__main__":
    main()
