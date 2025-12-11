# IRC Section 1 - Tax Imposed

**Source**: [26 U.S. Code § 1](https://www.law.cornell.edu/uscode/text/26/1)

## Overview

IRC Section 1 establishes the basic income tax rates for individuals based on filing status. This is the foundational section that determines how much tax is owed on taxable income.

## Filing Statuses (IRC §1)

There are four primary rate schedules corresponding to filing statuses:

- **§1(a)**: Married individuals filing jointly and surviving spouses
- **§1(b)**: Heads of households
- **§1(c)**: Unmarried individuals (other than surviving spouses and heads of households)
- **§1(d)**: Married individuals filing separately

## Tax Brackets (2024 Example)

For simplicity, consider the Single filer brackets (§1(c)):

| Taxable Income Range | Tax Rate |
|---------------------|----------|
| $0 - $11,600       | 10%      |
| $11,600 - $47,150  | 12%      |
| $47,150 - $100,525 | 22%      |
| $100,525 - $191,950| 24%      |
| $191,950 - $243,725| 32%      |
| $243,725 - $609,350| 35%      |
| Over $609,350       | 37%      |

## Mathematical Definition

The tax is calculated as a progressive tax function where:
- Income is divided into brackets
- Each bracket is taxed at its marginal rate
- Total tax = sum of (bracket_width × bracket_rate) for all filled brackets

## Formalization Goals

1. Define a `TaxBracket` structure with lower bound, upper bound, and rate
2. Define rate schedules for each filing status
3. Define function `calculateTax : Currency → FilingStatus → TaxYear → Currency`
4. Prove properties:
   - Tax is monotonically increasing with income
   - Marginal rate never exceeds 37%
   - Tax brackets are contiguous (no gaps)

## Example Calculation

For a single filer with $50,000 taxable income in 2024:

```
Tax = (11,600 × 0.10) + (47,150 - 11,600) × 0.12 + (50,000 - 47,150) × 0.22
    = 1,160 + 4,266 + 627
    = 6,053
```

## Notes

- Bracket amounts are adjusted annually for inflation (IRC §1(f))
- This section only calculates regular income tax (see IRC §55 for AMT)
- Does not include additional taxes like self-employment tax
