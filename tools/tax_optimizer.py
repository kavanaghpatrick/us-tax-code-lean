#!/usr/bin/env python3
"""
IRC Section Tax Optimizer

Finds tax minimization strategies by testing formalized IRC sections
against various scenarios. Identifies combinations of provisions that
create unexpected benefits.

Approach:
1. Load test scenarios
2. For each scenario, enumerate possible strategy combinations
3. Calculate tax impact of each combination
4. Rank by total tax savings
5. Flag strategies that exploit known contradictions/loopholes

Output:
- optimization_strategies.md (ranked strategies)
- optimization_results.json (machine-readable results)
"""

import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Any, Tuple
from collections import defaultdict

# Paths
TOOLS_DIR = Path(__file__).parent
ANALYSIS_DIR = TOOLS_DIR.parent / "analysis"

# Tax rates (simplified - using 2024 rates for illustration)
TAX_BRACKETS_SINGLE = [
    (11000, 0.10),
    (44725, 0.12),
    (95375, 0.22),
    (182100, 0.24),
    (231250, 0.32),
    (578125, 0.35),
    (float('inf'), 0.37)
]

TAX_BRACKETS_MFJ = [
    (22000, 0.10),
    (89050, 0.12),
    (190750, 0.22),
    (364200, 0.24),
    (462500, 0.32),
    (693750, 0.35),
    (float('inf'), 0.37)
]


@dataclass
class Strategy:
    """A tax minimization strategy"""
    name: str
    description: str
    sections_used: List[int]
    tax_savings: int
    exploits_loophole: bool
    loophole_type: str
    risk_level: str  # low, medium, high
    steps: List[str]


def calculate_tax(income: int, filing_status: str) -> int:
    """Calculate federal income tax using simplified brackets"""
    brackets = TAX_BRACKETS_MFJ if filing_status == "MarriedFilingJointly" else TAX_BRACKETS_SINGLE

    tax = 0
    prev_bracket = 0

    for bracket_max, rate in brackets:
        if income <= bracket_max:
            tax += (income - prev_bracket) * rate
            break
        else:
            tax += (bracket_max - prev_bracket) * rate
            prev_bracket = bracket_max

    return int(tax)


def calculate_bond_tax_savings(bond: Dict[str, Any]) -> Tuple[int, str]:
    """
    Calculate tax savings from bond tax-exemption.

    Returns: (savings_amount, explanation)
    """
    interest = bond["interest"]
    expected_exempt = bond["expected_tax_exempt"]

    if expected_exempt:
        # Assume 37% top bracket (conservative estimate)
        savings = int(interest * 0.37)
        explanation = f"Interest ${interest:,} tax-exempt under §103"
    else:
        savings = 0
        explanation = f"Interest ${interest:,} is taxable"

    return savings, explanation


def calculate_expense_deduction_savings(expense: Dict[str, Any]) -> Tuple[int, str]:
    """
    Calculate tax savings from expense deduction.

    Returns: (savings_amount, explanation)
    """
    expected_deductible = expense["expected_deductible"]

    if expected_deductible > 0:
        # Assume 37% top bracket
        savings = int(expected_deductible * 0.37)
        explanation = f"Deduction ${expected_deductible:,} under §162"
    else:
        savings = 0
        explanation = "Expense not deductible"

    return savings, explanation


def find_bond_strategies(bonds: List[Dict]) -> List[Strategy]:
    """
    Find tax strategies using bond scenarios.

    Focus on exploiting circular reference loopholes.
    """
    strategies = []

    # Strategy 1: 10% Threshold Gaming
    threshold_bonds = [b for b in bonds if
                       b.get("private_business_use_percent", 0) == 0.10 and
                       b.get("expected_tax_exempt", False)]

    if threshold_bonds:
        bond = threshold_bonds[0]
        savings, _ = calculate_bond_tax_savings(bond)

        strategies.append(Strategy(
            name="10% Private Use Threshold Gaming",
            description="Structure bond to have exactly 10.0% private use (at threshold, not over)",
            sections_used=[103, 141],
            tax_savings=savings,
            exploits_loophole=True,
            loophole_type="threshold_gaming",
            risk_level="low",
            steps=[
                "Issue state/local bond with proceeds of $1M+",
                "Structure private business use to be exactly 10.0% (not 10.1%)",
                "Ensure private security payments also exactly 10.0%",
                "§141 test: 'greater than 10%' means 10.0% passes",
                "Result: Interest remains tax-exempt under §103",
                f"Tax savings: ${savings:,} (37% of ${bond['interest']:,} interest)"
            ]
        ))

    # Strategy 2: Circular Reference Ambiguity
    # Use circular references in §103→§141→§144→§103 to argue for exemption
    pab_bonds = [b for b in bonds if
                 b.get("private_business_use_percent", 0) > 0.10 and
                 not b.get("is_qualified_private_activity", False) and
                 b.get("issuer") in ["State", "Local"]]

    if pab_bonds:
        bond = pab_bonds[0]
        # Assume we can argue for exemption due to circular definition ambiguity
        potential_savings = int(bond["interest"] * 0.37)

        strategies.append(Strategy(
            name="Circular Reference Ambiguity Argument",
            description="Exploit circular definitions in §§103-141-144 to argue bond qualification",
            sections_used=[103, 141, 144],
            tax_savings=potential_savings,
            exploits_loophole=True,
            loophole_type="circular_reference",
            risk_level="high",
            steps=[
                "Issue bond that appears to be private activity bond under §141",
                "Argue that §141 definition requires checking §144 qualification",
                "Show §144 qualification refers back to §103 exemption",
                "Claim circular chain makes definition ambiguous",
                "Under tax law canon, ambiguity resolved in favor of taxpayer",
                f"Potential savings: ${potential_savings:,} (if argument succeeds)",
                "⚠️ HIGH RISK: IRS would likely challenge this argument"
            ]
        ))

    # Strategy 3: Federally Guaranteed Bond Arbitrage
    # (This is actually NOT a loophole - it's clear in statute, but illustrate for completeness)
    fed_bonds = [b for b in bonds if b.get("is_federally_guaranteed", False)]
    state_bonds = [b for b in bonds if
                   not b.get("is_federally_guaranteed", False) and
                   b.get("issuer") in ["State", "Local"] and
                   b.get("expected_tax_exempt", True)]

    if fed_bonds and state_bonds:
        fed_bond = fed_bonds[0]
        state_bond = state_bonds[0]

        # This isn't a loophole, just illustrating the rule
        strategies.append(Strategy(
            name="Avoid Federal Guarantee (§149(b) Compliance)",
            description="Structure state bond WITHOUT federal guarantee to maintain exemption",
            sections_used=[103, 149],
            tax_savings=int(state_bond["interest"] * 0.37),
            exploits_loophole=False,
            loophole_type="none",
            risk_level="low",
            steps=[
                "Issue state/local bond",
                "Ensure NO federal guarantee (§149(b) disqualifies)",
                "Keep private use under 10%",
                "Maintain proper registration",
                f"Result: Interest ${state_bond['interest']:,} is tax-exempt",
                "This is standard bond structuring, not a loophole"
            ]
        ))

    return strategies


def find_expense_strategies(expenses: List[Dict]) -> List[Strategy]:
    """
    Find tax strategies using expense scenarios.

    Focus on overlapping compensation rules.
    """
    strategies = []

    # Strategy 1: Executive Compensation Restructuring
    exec_comp = [e for e in expenses if e.get("expense_type") == "ExecutiveCompensation"]

    if exec_comp:
        expense = exec_comp[0]
        amount = expense["amount"]
        cap = 1000000

        if amount > cap:
            # Split into cash (deductible up to cap) + equity (potentially different rules)
            cash_deduction = cap
            equity_amount = amount - cap

            strategies.append(Strategy(
                name="Executive Compensation Split Strategy",
                description="Circumvent §162(m) $1M cap by using equity compensation",
                sections_used=[162],  # Also involves stock option sections not formalized
                tax_savings=int(equity_amount * 0.21),  # Corporate rate
                exploits_loophole=False,  # This is common tax planning, not a loophole
                loophole_type="statutory_gap",
                risk_level="low",
                steps=[
                    f"Original plan: ${amount:,} cash compensation",
                    f"Deduction limited to: ${cap:,} under §162(m)",
                    f"Lost deduction: ${amount - cap:,}",
                    "",
                    "Restructured plan:",
                    f"1. Pay ${cap:,} in cash (deductible)",
                    f"2. Grant ${equity_amount:,} in stock options",
                    "3. Stock options deductible under different rules (not subject to §162(m) cap)",
                    f"4. Total deduction: ${amount:,}",
                    f"Tax savings: ${int(equity_amount * 0.21):,} (corporate rate on ${equity_amount:,})"
                ]
            ))

    # Strategy 2: Overlapping Compensation Benefits
    # This is the medium-severity finding from contradiction detector

    strategies.append(Strategy(
        name="Combat Zone + Deferred Compensation Stacking",
        description="Stack §112 combat pay exclusion with §457 deferred comp deduction",
        sections_used=[112, 457],
        tax_savings=50000,  # Hypothetical
        exploits_loophole=True,
        loophole_type="overlapping_rules",
        risk_level="medium",
        steps=[
            "Scenario: State government employee deployed to combat zone",
            "",
            "Step 1: Exclude combat pay under §112",
            "  - Salary: $100,000",
            "  - Combat zone exclusion: $100,000",
            "  - Taxable income: $0",
            "",
            "Step 2: Employer contributes to §457 deferred comp plan",
            "  - Contribution: $20,000",
            "  - Deductible to employer: $20,000",
            "",
            "Question: Can employer deduct contribution to plan for excluded income?",
            "Statutory text unclear on interaction between §112 and §457",
            "",
            "If allowed: Double benefit (exclusion + deduction)",
            "Tax savings: ~$50,000 (combined employee exclusion + employer deduction)",
            "",
            "⚠️ MEDIUM RISK: IRS would likely issue guidance preventing this"
        ]
    ))

    # Strategy 3: Travel Expense Optimization
    travel_exp = [e for e in expenses if e.get("expense_type") == "Travel"]

    if travel_exp:
        expense = travel_exp[0]
        amount = expense["amount"]
        expected = expense["expected_deductible"]

        if expected < amount:
            lavish = amount - expected

            strategies.append(Strategy(
                name="Travel Expense Documentation Strategy",
                description="Minimize 'lavish' portion by detailed documentation",
                sections_used=[162],
                tax_savings=int(lavish * 0.37),
                exploits_loophole=False,
                loophole_type="none",
                risk_level="low",
                steps=[
                    f"Total travel expense: ${amount:,}",
                    f"'Lavish or extravagant' portion: ${lavish:,} (not deductible)",
                    f"Reasonable portion: ${expected:,} (deductible)",
                    "",
                    "Optimization:",
                    "1. Maintain detailed receipts showing business necessity",
                    "2. Document why expenses were reasonable (client meetings, etc.)",
                    "3. Compare to industry standards",
                    "4. Result: Reduce 'lavish' classification, increase deduction",
                    "",
                    "This is compliance, not a loophole"
                ]
            ))

    return strategies


def find_combined_strategies() -> List[Strategy]:
    """
    Find strategies combining multiple sections.

    This is where novel loopholes might be discovered.
    """
    strategies = []

    # Strategy: Bond Interest + Business Expense Interaction
    # Can you deduct expenses incurred to earn tax-exempt income?
    # §265 says NO, but is it formalized correctly?

    strategies.append(Strategy(
        name="Tax-Exempt Interest + Deduction Interaction",
        description="Check if formalization properly handles §265 disallowance",
        sections_used=[103, 162, 265],  # Note: §265 may not be formalized
        tax_savings=0,  # Unknown - needs investigation
        exploits_loophole=False,
        loophole_type="potential_gap",
        risk_level="low",
        steps=[
            "Scenario: Taxpayer owns tax-exempt bonds earning $100K interest",
            "Taxpayer incurs $20K expenses to manage bond portfolio",
            "",
            "Question: Can taxpayer deduct the $20K expenses?",
            "",
            "§103: Bond interest is tax-exempt",
            "§162: Trade/business expenses are deductible",
            "§265: NO deduction for expenses allocable to tax-exempt income",
            "",
            "Check: Is §265 formalized in our codebase?",
            "If not, formalization may be incomplete",
            "",
            "Action item: Search for Section265.lean file"
        ]
    ))

    return strategies


def main():
    """Main entry point"""
    print("IRC Section Tax Optimizer")
    print("=" * 50)
    print()

    # Load scenarios
    scenarios_file = ANALYSIS_DIR / "test_scenarios.json"
    if not scenarios_file.exists():
        print(f"Error: {scenarios_file} not found")
        print("Run scenario_generator.py first")
        return

    with open(scenarios_file) as f:
        scenarios = json.load(f)

    bonds = scenarios.get("bonds", [])
    expenses = scenarios.get("expenses", [])

    print(f"Loaded {len(bonds)} bond scenarios")
    print(f"Loaded {len(expenses)} expense scenarios")
    print()

    # Find strategies
    print("Analyzing bond strategies...")
    bond_strategies = find_bond_strategies(bonds)
    print(f"✓ Found {len(bond_strategies)} bond strategies")

    print("Analyzing expense strategies...")
    expense_strategies = find_expense_strategies(expenses)
    print(f"✓ Found {len(expense_strategies)} expense strategies")

    print("Analyzing combined strategies...")
    combined_strategies = find_combined_strategies()
    print(f"✓ Found {len(combined_strategies)} combined strategies")
    print()

    all_strategies = bond_strategies + expense_strategies + combined_strategies

    # Rank by tax savings
    ranked = sorted(all_strategies, key=lambda s: s.tax_savings, reverse=True)

    # Statistics
    total_savings = sum(s.tax_savings for s in ranked)
    loophole_count = sum(1 for s in ranked if s.exploits_loophole)

    print("Results:")
    print(f"  Total strategies: {len(ranked)}")
    print(f"  Exploits loopholes: {loophole_count}")
    print(f"  Total potential savings: ${total_savings:,}")
    print()

    # Generate report
    report_file = ANALYSIS_DIR / "optimization_strategies.md"
    with open(report_file, 'w') as f:
        f.write("# IRC Tax Optimization Strategies\n\n")
        f.write(f"**Total Strategies Identified**: {len(ranked)}\n\n")
        f.write(f"**Strategies Exploiting Loopholes**: {loophole_count}\n\n")
        f.write(f"**Total Potential Savings**: ${total_savings:,}\n\n")

        f.write("---\n\n")

        for i, strategy in enumerate(ranked, 1):
            f.write(f"## Strategy #{i}: {strategy.name}\n\n")
            f.write(f"**Description**: {strategy.description}\n\n")
            f.write(f"**IRC Sections Used**: {', '.join(f'§{s}' for s in strategy.sections_used)}\n\n")
            f.write(f"**Tax Savings**: ${strategy.tax_savings:,}\n\n")
            f.write(f"**Exploits Loophole**: {'Yes' if strategy.exploits_loophole else 'No'}\n\n")
            if strategy.exploits_loophole:
                f.write(f"**Loophole Type**: {strategy.loophole_type}\n\n")
            f.write(f"**Risk Level**: {strategy.risk_level.upper()}\n\n")

            f.write("### Implementation Steps\n\n")
            for step in strategy.steps:
                if step:
                    f.write(f"{step}\n\n")
                else:
                    f.write("\n")

            f.write("---\n\n")

    print(f"✓ Generated {report_file}")

    # Save JSON
    json_file = ANALYSIS_DIR / "optimization_results.json"
    with open(json_file, 'w') as f:
        json.dump([asdict(s) for s in ranked], f, indent=2)

    print(f"✓ Generated {json_file}")
    print()
    print("Done! Review optimization strategies in:")
    print(f"  {report_file}")


if __name__ == "__main__":
    main()
