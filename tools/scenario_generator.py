#!/usr/bin/env python3
"""
IRC Section Scenario Generator

Generates realistic tax scenarios to test formalized IRC sections.
Uses property-based testing approach to find edge cases.

Output:
- test_scenarios.json (machine-readable test cases)
- scenario_analysis.md (human-readable report)
"""

import json
import random
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Any
from enum import Enum

# Path to output directory
OUTPUT_DIR = Path(__file__).parent.parent / "analysis"


class FilingStatus(Enum):
    SINGLE = "Single"
    MARRIED_FILING_JOINTLY = "MarriedFilingJointly"
    MARRIED_FILING_SEPARATELY = "MarriedFilingSeparately"
    HEAD_OF_HOUSEHOLD = "HeadOfHousehold"
    QUALIFYING_WIDOWER = "QualifyingWidower"


class IssuerType(Enum):
    STATE = "State"
    LOCAL = "Local"
    FEDERAL = "Federal"
    CORPORATE = "Corporate"


class ExpenseType(Enum):
    SALARY = "Salary"
    TRAVEL = "Travel"
    RENT = "Rent"
    BRIBE = "Bribe"
    CHARITABLE = "CharitableContribution"
    FINE = "FineOrPenalty"
    EXEC_COMP = "ExecutiveCompensation"
    LOBBYING = "LobbyingExpense"


@dataclass
class TaxpayerScenario:
    """Represents a taxpayer for testing"""
    id: int
    filing_status: str
    gross_income: int
    wages: int
    capital_gains: int
    interest_income: int
    dividends: int
    num_dependents: int
    age: int
    is_blind: bool
    description: str


@dataclass
class BondScenario:
    """Represents a bond for testing IRC §103, §141, etc."""
    id: int
    issuer: str
    interest: int
    proceeds: int
    private_business_use_percent: float
    private_security_payment_percent: float
    private_loan_financing_amount: int
    is_qualified_private_activity: bool
    is_arbitrage: bool
    is_registration_required: bool
    is_registered: bool
    is_federally_guaranteed: bool
    expected_tax_exempt: bool
    description: str


@dataclass
class ExpenseScenario:
    """Represents an expense for testing IRC §162, etc."""
    id: int
    amount: int
    expense_type: str
    ordinary: bool
    necessary: bool
    paid_or_incurred: bool
    trade_or_business: bool
    expense_details: Dict[str, Any]
    expected_deductible: int
    description: str


def generate_taxpayer_scenarios(count: int) -> List[TaxpayerScenario]:
    """Generate diverse taxpayer scenarios"""
    scenarios = []

    # Income brackets to test
    income_brackets = [
        (10000, "Very low income"),
        (50000, "Low income"),
        (100000, "Middle income"),
        (250000, "Upper middle income"),
        (500000, "High income"),
        (1000000, "Very high income"),
        (10000000, "Ultra high income")
    ]

    scenario_id = 1

    for income, desc in income_brackets:
        for filing_status in FilingStatus:
            # Generate a few variations per combination
            for variation in range(count // (len(income_brackets) * len(FilingStatus)) + 1):
                wage_pct = random.uniform(0.5, 1.0)
                cap_gain_pct = random.uniform(0, 0.4)

                scenarios.append(TaxpayerScenario(
                    id=scenario_id,
                    filing_status=filing_status.value,
                    gross_income=income,
                    wages=int(income * wage_pct),
                    capital_gains=int(income * cap_gain_pct),
                    interest_income=int(income * random.uniform(0, 0.1)),
                    dividends=int(income * random.uniform(0, 0.1)),
                    num_dependents=random.randint(0, 5),
                    age=random.randint(18, 90),
                    is_blind=random.random() < 0.05,
                    description=f"{desc}, {filing_status.value}, {variation} dependents"
                ))
                scenario_id += 1

                if scenario_id > count:
                    return scenarios[:count]

    return scenarios[:count]


def generate_bond_scenarios() -> List[BondScenario]:
    """Generate diverse bond scenarios to test IRC §103, §141, §143, §144"""
    scenarios = []
    scenario_id = 1

    # Case 1: Standard state bond (should be tax-exempt)
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=500,
        proceeds=1000000,
        private_business_use_percent=0.0,
        private_security_payment_percent=0.0,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=True,
        description="Standard state bond - should be tax-exempt"
    ))
    scenario_id += 1

    # Case 2: Federal bond (NOT tax-exempt under §103)
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="Federal",
        interest=400,
        proceeds=1000000,
        private_business_use_percent=0.0,
        private_security_payment_percent=0.0,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=False,
        description="Federal bond - NOT tax-exempt"
    ))
    scenario_id += 1

    # Case 3: Private activity bond, not qualified (NOT exempt)
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="Local",
        interest=600,
        proceeds=1000000,
        private_business_use_percent=0.15,
        private_security_payment_percent=0.15,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=False,
        description="Private activity bond, not qualified - NOT exempt"
    ))
    scenario_id += 1

    # Case 4: Private activity bond, qualified (IS exempt)
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="Local",
        interest=550,
        proceeds=1000000,
        private_business_use_percent=0.20,
        private_security_payment_percent=0.20,
        private_loan_financing_amount=0,
        is_qualified_private_activity=True,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=True,
        description="Qualified private activity bond - IS exempt"
    ))
    scenario_id += 1

    # Case 5: Arbitrage bond (NOT exempt)
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=700,
        proceeds=1000000,
        private_business_use_percent=0.0,
        private_security_payment_percent=0.0,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=True,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=False,
        description="Arbitrage bond - NOT exempt"
    ))
    scenario_id += 1

    # Case 6: Federally guaranteed (NOT exempt per §149(b))
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=450,
        proceeds=1000000,
        private_business_use_percent=0.0,
        private_security_payment_percent=0.0,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=True,
        expected_tax_exempt=False,
        description="Federally guaranteed - NOT exempt (§149(b))"
    ))
    scenario_id += 1

    # Case 7: Large bond with private loan exceeding $5M threshold
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=1500,
        proceeds=200000000,
        private_business_use_percent=0.0,
        private_security_payment_percent=0.0,
        private_loan_financing_amount=6000000,  # > $5M threshold
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=False,
        description="Large bond with $6M private loan - triggers PAB status"
    ))
    scenario_id += 1

    # Case 8: Edge case - exactly at 10% private use threshold
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=500,
        proceeds=1000000,
        private_business_use_percent=0.10,  # Exactly at threshold
        private_security_payment_percent=0.10,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=True,  # Should be exempt (threshold is >, not >=)
        description="Edge case - exactly 10% private use (at threshold, not over)"
    ))
    scenario_id += 1

    # Case 9: Edge case - just over 10% threshold
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=500,
        proceeds=1000000,
        private_business_use_percent=0.11,  # Just over threshold
        private_security_payment_percent=0.11,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=True,
        is_federally_guaranteed=False,
        expected_tax_exempt=False,  # NOT exempt (over threshold)
        description="Just over 10% private use threshold - NOT exempt"
    ))
    scenario_id += 1

    # Case 10: Unregistered bond when registration required (NOT exempt)
    scenarios.append(BondScenario(
        id=scenario_id,
        issuer="State",
        interest=500,
        proceeds=1000000,
        private_business_use_percent=0.0,
        private_security_payment_percent=0.0,
        private_loan_financing_amount=0,
        is_qualified_private_activity=False,
        is_arbitrage=False,
        is_registration_required=True,
        is_registered=False,  # NOT registered
        is_federally_guaranteed=False,
        expected_tax_exempt=False,
        description="Unregistered bond when registration required - NOT exempt"
    ))

    return scenarios


def generate_expense_scenarios() -> List[ExpenseScenario]:
    """Generate diverse expense scenarios to test IRC §162"""
    scenarios = []
    scenario_id = 1

    # Case 1: Reasonable salary
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=100000,
        expense_type="Salary",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={"reasonable_amount": 120000, "services_rendered": True},
        expected_deductible=100000,
        description="Reasonable salary for services rendered - fully deductible"
    ))
    scenario_id += 1

    # Case 2: Unreasonable salary
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=500000,
        expense_type="Salary",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={"reasonable_amount": 100000, "services_rendered": True},
        expected_deductible=100000,  # Limited to reasonable amount
        description="Excessive salary - limited to reasonable amount"
    ))
    scenario_id += 1

    # Case 3: Illegal bribe (NOT deductible)
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=50000,
        expense_type="Bribe",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={"illegal": True},
        expected_deductible=0,
        description="Illegal bribe - NOT deductible (§162(c))"
    ))
    scenario_id += 1

    # Case 4: Government fine (NOT deductible per §162(f))
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=50000,
        expense_type="FineOrPenalty",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={"government_paid": True, "amount": 50000},
        expected_deductible=0,
        description="Government fine - NOT deductible (§162(f))"
    ))
    scenario_id += 1

    # Case 5: Executive compensation over $1M (§162(m) cap)
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=2000000,
        expense_type="ExecutiveCompensation",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={"is_public_company": True, "is_covered_employee": True, "amount": 2000000},
        expected_deductible=1000000,  # Capped at $1M
        description="Executive comp $2M for public company - capped at $1M (§162(m))"
    ))
    scenario_id += 1

    # Case 6: Lobbying expense (NOT deductible per §162(e))
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=75000,
        expense_type="LobbyingExpense",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={"is_direct_lobbying": True, "amount": 75000},
        expected_deductible=0,
        description="Lobbying expense - NOT deductible (§162(e))"
    ))
    scenario_id += 1

    # Case 7: Travel expense - lavish portion
    scenarios.append(ExpenseScenario(
        id=scenario_id,
        amount=10000,
        expense_type="Travel",
        ordinary=True,
        necessary=True,
        paid_or_incurred=True,
        trade_or_business=True,
        expense_details={
            "away_from_home": True,
            "lavish_amount": 3000,
            "employment_duration_days": 180,
            "is_federal_crime_investigation": False
        },
        expected_deductible=7000,  # 10000 - 3000 lavish
        description="Travel expense with lavish portion - deduct only reasonable part"
    ))

    return scenarios


def main():
    """Main entry point"""
    print("IRC Section Scenario Generator")
    print("=" * 50)
    print()

    # Generate scenarios
    print("Generating taxpayer scenarios...")
    taxpayers = generate_taxpayer_scenarios(50)
    print(f"✓ Generated {len(taxpayers)} taxpayer scenarios")

    print("Generating bond scenarios...")
    bonds = generate_bond_scenarios()
    print(f"✓ Generated {len(bonds)} bond scenarios")

    print("Generating expense scenarios...")
    expenses = generate_expense_scenarios()
    print(f"✓ Generated {len(expenses)} expense scenarios")
    print()

    # Save to JSON
    OUTPUT_DIR.mkdir(exist_ok=True)

    scenarios_file = OUTPUT_DIR / "test_scenarios.json"
    with open(scenarios_file, 'w') as f:
        json.dump({
            "taxpayers": [asdict(t) for t in taxpayers],
            "bonds": [asdict(b) for b in bonds],
            "expenses": [asdict(e) for e in expenses]
        }, f, indent=2)
    print(f"✓ Saved scenarios to {scenarios_file}")

    # Generate markdown report
    report_file = OUTPUT_DIR / "scenario_analysis.md"
    with open(report_file, 'w') as f:
        f.write("# IRC Test Scenario Analysis\n\n")
        f.write(f"**Total Scenarios Generated**: {len(taxpayers) + len(bonds) + len(expenses)}\n\n")

        f.write("## Taxpayer Scenarios\n\n")
        f.write(f"Generated {len(taxpayers)} diverse taxpayer scenarios covering:\n")
        f.write("- Income levels: $10K to $10M\n")
        f.write("- All filing statuses\n")
        f.write("- 0-5 dependents\n")
        f.write("- Ages 18-90\n\n")

        f.write("## Bond Scenarios (IRC §103, §141, §143, §144)\n\n")
        for bond in bonds:
            f.write(f"### Scenario {bond.id}: {bond.description}\n\n")
            f.write(f"- **Issuer**: {bond.issuer}\n")
            f.write(f"- **Interest**: ${bond.interest:,}\n")
            f.write(f"- **Proceeds**: ${bond.proceeds:,}\n")
            f.write(f"- **Private Use**: {bond.private_business_use_percent*100}%\n")
            f.write(f"- **Expected Result**: {'Tax-exempt' if bond.expected_tax_exempt else 'Taxable'}\n\n")

        f.write("## Expense Scenarios (IRC §162)\n\n")
        for expense in expenses:
            f.write(f"### Scenario {expense.id}: {expense.description}\n\n")
            f.write(f"- **Amount**: ${expense.amount:,}\n")
            f.write(f"- **Type**: {expense.expense_type}\n")
            f.write(f"- **Expected Deductible**: ${expense.expected_deductible:,}\n\n")

    print(f"✓ Generated report: {report_file}")
    print()
    print("Done! Scenarios ready for testing against Lean formalizations.")


if __name__ == "__main__":
    main()
