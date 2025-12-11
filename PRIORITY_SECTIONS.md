# IRC Sections Priority List for Formalization

## Tier 1: Core Tax Calculation (30 sections) - HIGHEST PRIORITY

**Individual Tax Rates & Structure**
- [ ] §1 - Tax imposed (DONE - 2 theorems proved!)
- [ ] §2 - Definitions and special rules
- [ ] §3 - Tax tables for individuals

**Gross Income Definition**
- [ ] §61 - Gross income defined
- [ ] §62 - Adjusted gross income defined
- [ ] §63 - Taxable income defined

**Standard/Itemized Deductions**
- [ ] §67 - 2% floor on miscellaneous deductions
- [ ] §68 - Overall limitation on itemized deductions

**Personal Exemptions (historical)**
- [ ] §151 - Allowance of deductions for personal exemptions
- [ ] §152 - Dependent defined

**Filing Status**
- [ ] §2(b) - Head of household
- [ ] §7703 - Determination of marital status

**Alternative Minimum Tax (AMT)**
- [ ] §55 - Alternative minimum tax imposed
- [ ] §56 - Adjustments in computing AMT
- [ ] §57 - Items of tax preference

## Tier 2: Major Credits (20 sections) - HIGH PRIORITY

**Refundable Credits**
- [ ] §24 - Child tax credit (IN PROGRESS)
- [ ] §32 - Earned income tax credit (IN PROGRESS)
- [ ] §36B - Premium tax credit (ACA)

**Nonrefundable Credits**
- [ ] §21 - Child and dependent care credit
- [ ] §22 - Credit for elderly and disabled
- [ ] §23 - Adoption expenses credit
- [ ] §25A - Education credits (Hope/Lifetime Learning)
- [ ] §25B - Elective deferrals and IRA contributions (Saver's Credit)
- [ ] §25D - Residential energy credits

**Credit Limitations**
- [ ] §26 - Limitation based on tax liability

## Tier 3: Business Income & Deductions (35 sections) - HIGH PRIORITY

**Business Deductions**
- [ ] §162 - Trade or business expenses (IN PROGRESS)
- [ ] §163 - Interest
- [ ] §164 - Taxes
- [ ] §165 - Losses
- [ ] §166 - Bad debts
- [ ] §167 - Depreciation
- [ ] §168 - Accelerated cost recovery system (MACRS)
- [ ] §169 - Amortization of pollution control facilities
- [ ] §170 - Charitable contributions
- [ ] §174 - Research and experimental expenditures
- [ ] §179 - Election to expense certain depreciable business assets

**Limitations on Deductions**
- [ ] §183 - Activities not engaged in for profit (hobby loss)
- [ ] §195 - Start-up expenditures
- [ ] §197 - Amortization of goodwill and intangibles
- [ ] §199A - Qualified business income deduction (20% pass-through)

**Meals & Entertainment**
- [ ] §274 - Disallowance of certain entertainment expenses

## Tier 4: Capital Gains & Investments (25 sections) - MEDIUM PRIORITY

**Basis & Gain/Loss**
- [ ] §1001 - Determination of gain or loss
- [ ] §1011 - Adjusted basis for determining gain or loss
- [ ] §1012 - Basis of property - cost
- [ ] §1014 - Basis of property acquired from a decedent (step-up)
- [ ] §1015 - Basis of property acquired by gift
- [ ] §1016 - Adjustments to basis

**Capital Asset Definition**
- [ ] §64 - Ordinary income defined (IN PROGRESS)
- [ ] §65 - Ordinary loss defined (DONE - 1 theorem proved!)
- [ ] §1221 - Capital asset defined
- [ ] §1222 - Other terms relating to capital gains and losses
- [ ] §1231 - Property used in trade or business

**Capital Loss Limitations**
- [ ] §1211 - Limitation on capital losses
- [ ] §1212 - Capital loss carrybacks and carryovers

**Special Rates**
- [ ] §1(h) - Maximum capital gains rate
- [ ] §1411 - Net investment income tax (3.8%)

## Tier 5: Retirement & Savings (15 sections) - MEDIUM PRIORITY

**IRAs**
- [ ] §219 - Retirement savings (IRA deduction)
- [ ] §408 - Individual retirement accounts
- [ ] §408A - Roth IRAs

**401(k) & Qualified Plans**
- [ ] §401 - Qualified pension, profit-sharing, and stock bonus plans
- [ ] §402 - Taxability of beneficiary of employees' trust
- [ ] §403(b) - Tax-sheltered annuities

**Distributions**
- [ ] §72 - Annuities and life insurance contracts
- [ ] §408(d) - Tax treatment of IRA distributions

## Tier 6: Special Situations (20 sections) - LOWER PRIORITY

**Education**
- [ ] §117 - Qualified scholarships
- [ ] §127 - Educational assistance programs
- [ ] §221 - Interest on education loans

**Housing**
- [ ] §121 - Exclusion of gain from sale of principal residence
- [ ] §163(h) - Qualified residence interest (mortgage interest)

**Medical**
- [ ] §105 - Amounts received under accident and health plans
- [ ] §106 - Contributions by employer to accident and health plans
- [ ] §213 - Medical, dental, etc., expenses

**Divorce & Alimony**
- [ ] §71 - Alimony and separate maintenance payments
- [ ] §215 - Alimony, etc., payments

**Estate & Gift**
- [ ] §102 - Gifts and inheritances
- [ ] §2001 - Estate tax imposed
- [ ] §2501 - Gift tax imposed

## Summary Statistics

- **Total Prioritized**: ~145 sections
- **Currently Formalized**: 7 sections
- **In Progress**: 3 sections
- **Verified Theorems**: 3
- **Target for Phase 1**: 50-100 sections formalized

## Submission Strategy

**Wave 1** (Immediate - 20 sections):
Core calculation sections that others depend on
- §1, §61, §62, §63, §151, §152, §162-170, §1001, §1011, §1012

**Wave 2** (Next batch - 20 sections):
Major credits and common deductions
- §21, §24, §32, §25A, §25D, §55, §56, §57, §213, §163

**Wave 3** (20 sections):
Capital gains framework
- §64, §65, §1211, §1212, §1221, §1222, §1231, §1014, §1015, §1016

**Wave 4** (20 sections):
Business deductions and limitations
- §174, §179, §183, §195, §197, §199A, §274

**Wave 5** (20 sections):
Retirement and special situations
- §72, §401, §402, §408, §408A, §219, §121, §117

## Loophole Detection Targets

Once formalized, analyze for:
1. **Contradictory definitions** - Same term defined differently
2. **Missing constraints** - Deductions without upper bounds
3. **Circular logic** - A depends on B, B depends on A
4. **Boundary conditions** - What happens at $0, negative amounts?
5. **Phase-out cliffs** - Sudden benefit losses at thresholds
6. **Double benefits** - Same expense deductible multiple ways?

---

**Last Updated**: 2025-12-11
**Status**: Ready for Phase 1 mass submission
