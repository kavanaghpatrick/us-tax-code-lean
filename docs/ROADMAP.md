# US Tax Code Formalization Roadmap

## Vision
Create a complete, machine-verified formalization of the US Internal Revenue Code (Title 26) in Lean 4, enabling:
- Automated tax calculation verification
- Detection of legal inconsistencies and ambiguities
- Formal proofs of tax law properties
- Educational resource for understanding tax law

## Primary Source
[Cornell Law - 26 U.S. Code](https://www.law.cornell.edu/uscode/text/26)

---

## Phase 1: Foundation (Current)

### 1.1 Core Infrastructure ✓
- [x] Project setup with Lean 4 and Lake
- [x] Basic types (Currency, TaxYear, FilingStatus, Taxpayer)
- [x] Git repository with security (.gitignore for secrets)
- [x] Aristotle API integration

### 1.2 Section 1 - Tax Imposed (In Progress)
**IRC**: [26 USC §1](https://www.law.cornell.edu/uscode/text/26/1)

**Scope**: Tax rate schedules for all filing statuses

**Tasks**:
- [ ] Define 2024 tax brackets for all filing statuses
  - [ ] Single filers (§1(c))
  - [ ] Married filing jointly (§1(a))
  - [ ] Married filing separately (§1(d))
  - [ ] Head of household (§1(b))
  - [ ] Qualifying widow(er) (§2(b))
- [ ] Implement progressive tax calculation function
- [ ] Prove tax monotonicity (more income = more tax)
- [ ] Prove tax non-negativity
- [ ] Test with IRS examples

**Deliverable**: Working tax calculator for basic scenarios

---

## Phase 2: Income & Deductions

### 2.1 Section 61 - Gross Income Defined
**IRC**: [26 USC §61](https://www.law.cornell.edu/uscode/text/26/61)

**Scope**: Define what constitutes gross income

**Key Concepts**:
- Compensation for services (wages, fees, commissions)
- Business income
- Gains from property dealings
- Interest and dividends
- Rents and royalties
- 15 enumerated categories

**Tasks**:
- [ ] Define IncomeSource inductive type
- [ ] Formalize "all income from whatever source derived"
- [ ] Model specific income categories
- [ ] Prove income aggregation properties

### 2.2 Section 62 - Adjusted Gross Income
**IRC**: [26 USC §62](https://www.law.cornell.edu/uscode/text/26/62)

**Scope**: Above-the-line deductions

**Tasks**:
- [ ] Define AGI calculation
- [ ] Model educator expenses, HSA contributions, etc.
- [ ] Prove AGI ≤ Gross Income

### 2.3 Section 63 - Taxable Income
**IRC**: [26 USC §63](https://www.law.cornell.edu/uscode/text/26/63)

**Scope**: Standard deduction vs itemized deductions

**Tasks**:
- [ ] Define standard deduction amounts
- [ ] Model itemized deductions framework
- [ ] Implement max(standard, itemized) logic
- [ ] Prove taxable income ≤ AGI

---

## Phase 3: Common Deductions & Credits

### 3.1 Itemized Deductions

#### Section 164 - State/Local Taxes (SALT)
- [ ] $10,000 cap (post-TCJA)
- [ ] Property tax deduction
- [ ] State income tax deduction

#### Section 163 - Mortgage Interest
- [ ] Primary residence
- [ ] $750,000 debt limit (post-TCJA)
- [ ] Points deduction

#### Section 170 - Charitable Contributions
- [ ] AGI limits by organization type
- [ ] Carryover rules
- [ ] Substantiation requirements

### 3.2 Tax Credits

#### Section 21 - Child & Dependent Care
- [ ] $3,000/$6,000 limits
- [ ] Income phase-out
- [ ] Qualifying person requirements

#### Section 24 - Child Tax Credit
- [ ] $2,000 per child
- [ ] $500 for other dependents
- [ ] Refundable portion (ACTC)
- [ ] Income phase-outs

#### Section 25A - Education Credits
- [ ] American Opportunity Credit
- [ ] Lifetime Learning Credit
- [ ] Coordination rules

---

## Phase 4: Business & Self-Employment

### 4.1 Schedule C - Business Income
**IRC**: Sections 162, 179, 195

**Tasks**:
- [ ] Business expense deduction rules
- [ ] Section 179 expensing
- [ ] Startup costs amortization
- [ ] Home office deduction (§280A)

### 4.2 Self-Employment Tax
**IRC**: [Section 1401](https://www.law.cornell.edu/uscode/text/26/1401)

**Tasks**:
- [ ] Calculate SE tax (Social Security + Medicare)
- [ ] Above-the-line deduction for 1/2 SE tax
- [ ] Net earnings from self-employment

---

## Phase 5: Capital Gains & Investments

### 5.1 Section 1221 - Capital Asset Defined
- [ ] Define capital vs ordinary assets
- [ ] Inventory exception
- [ ] Real property used in trade/business

### 5.2 Section 1222 - Holding Periods
- [ ] Long-term vs short-term (12-month rule)
- [ ] Special rules (inheritance, gifts)

### 5.3 Section 1(h) - Capital Gains Rates
- [ ] 0%, 15%, 20% brackets
- [ ] Net capital gain calculation
- [ ] Qualified dividend treatment

---

## Phase 6: Complex Topics

### 6.1 Alternative Minimum Tax (AMT)
**IRC**: [Section 55](https://www.law.cornell.edu/uscode/text/26/55)

**Scope**: Parallel tax system

**Tasks**:
- [ ] AMT income adjustments
- [ ] AMT exemption and phase-out
- [ ] AMT rate structure (26%/28%)
- [ ] Prove max(regular tax, AMT) calculation

### 6.2 Net Investment Income Tax
**IRC**: [Section 1411](https://www.law.cornell.edu/uscode/text/26/1411)

**Tasks**:
- [ ] 3.8% surtax calculation
- [ ] Modified AGI thresholds
- [ ] Investment income definition

### 6.3 Retirement Accounts
**IRC**: Sections 401, 408, 408A

**Tasks**:
- [ ] Traditional IRA deduction limits
- [ ] Roth IRA contribution phase-outs
- [ ] 401(k) deferral limits
- [ ] Required minimum distributions (RMDs)

---

## Phase 7: Corporate & Passthrough

### 7.1 Section 11 - Corporate Tax
- [ ] Flat 21% rate (post-TCJA)
- [ ] Corporate income calculation

### 7.2 Section 199A - QBI Deduction
- [ ] 20% qualified business income deduction
- [ ] SSTB limitations
- [ ] W-2 wage and capital limitations

---

## Prioritization Strategy

### Tier 1 (Essential - 90% of Individual Returns)
1. Section 1 - Tax rates
2. Section 61 - Gross income
3. Section 63 - Taxable income (standard deduction)
4. Section 24 - Child tax credit
5. Section 32 - Earned income credit
6. Self-employment tax (§1401)

### Tier 2 (Common - 50% of Returns)
1. Itemized deductions (§§164, 163, 170)
2. Capital gains (§§1(h), 1221-1222)
3. Retirement contributions (§§219, 408)
4. Education credits (§25A)

### Tier 3 (Complex - 10% of Returns)
1. AMT (§55)
2. QBI deduction (§199A)
3. Net investment income tax (§1411)
4. Business depreciation (§§167, 168, 179)

---

## Testing Strategy

### Test Data Sources
1. **IRS Publications**: Examples from Pub 17, 505, 535
2. **IRS Forms Instructions**: Form 1040 instructions
3. **Tax Software**: Compare outputs with commercial software
4. **Edge Cases**: Bracket boundaries, phase-out cliffs

### Verification Approach
```lean
-- Example test case
def example_taxpayer_2024 : Taxpayer := {
  id := "123-45-6789"
  filingStatus := FilingStatus.Single
  taxYear := ⟨2024, by decide⟩
}

-- Test: Single filer with $50,000 income
example : calculateIncomeTax 5000000 FilingStatus.Single (TaxYear.mk 2024 (by decide)) = 605300 := by
  -- Proof that $50k income yields $6,053 tax
  sorry
```

---

## Milestones

### M1: MVP Tax Calculator (3 months)
- Sections 1, 61, 63 complete
- Standard deduction working
- Basic tax calculation for W-2 employees

### M2: Common Scenarios (6 months)
- All Tier 1 sections complete
- Self-employment tax
- Child tax credit
- Cover 70% of individual returns

### M3: Comprehensive Coverage (12 months)
- All Tier 1 + Tier 2 sections
- Capital gains taxation
- Itemized deductions
- Education credits
- Cover 90% of individual returns

### M4: Advanced Topics (18 months)
- AMT formalization
- QBI deduction
- Investment income surtax
- Cover 95% of individual returns

---

## Technical Debt & Future Work

### Known Limitations
1. **No state tax codes** - Federal only initially
2. **Static year** - Start with 2024, generalize later
3. **No inflation adjustments** - Hardcode 2024 values first
4. **Simplified edge cases** - Focus on common scenarios

### Future Enhancements
1. **Time-varying rules**: Model IRC changes over tax years
2. **State integration**: Add state tax codes
3. **Form generation**: Output actual IRS forms
4. **Natural language interface**: "I earned $X, what's my tax?"
5. **Policy simulation**: Test proposed tax law changes
6. **International**: FATCA, foreign tax credit

---

## Success Metrics

1. **Coverage**: % of Form 1040 lines formalized
2. **Accuracy**: Agreement with IRS examples
3. **Proofs**: Verified properties (monotonicity, bounds)
4. **Tests**: Passing test cases from IRS publications
5. **Documentation**: Every definition linked to IRC section

---

## Resources

### Primary Sources
- [Cornell Law - USC Title 26](https://www.law.cornell.edu/uscode/text/26)
- [IRS Publications](https://www.irs.gov/forms-pubs)
- [Treasury Regulations](https://www.ecfr.gov/current/title-26)

### Tools
- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Harmonic Aristotle](https://aristotle.harmonic.fun)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)

### Prior Art
- Tax calculation libraries (Open Source)
- Legal formalization research
- Theorem proving for specifications
