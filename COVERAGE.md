# US Tax Code Formalization - Coverage Report

**Last Updated: 2025-12-18**

## Project Statistics

| Metric | Value |
|--------|-------|
| Total Lean Files | 1,455 |
| Main Section Files | 752 |
| Aristotle Output Files | 703 |
| Lines of Lean Code | 537,400 |
| Theorems Proven | 607 |
| Remaining `sorry` | 17 |

---

## Coverage by Subtitle

### Subtitle A: Income Taxes (§1-1564) — ~93% Coverage

This is the **core of the tax code** - what most individuals and businesses use.

#### Complete (100%)

| Area | Sections | Description |
|------|----------|-------------|
| Tax Rates | §1-12 | Individual & corporate rates |
| Tax Credits | §21-54 | Child tax, earned income, R&D, etc. |
| AMT | §55-59 | Alternative Minimum Tax |
| Gross Income | §61-68 | The fundamental "income" concept |
| Income Inclusions | §71-91 | Alimony, annuities, Social Security |
| Income Exclusions | §101-140 | Life insurance, gifts, scholarships |
| Business Deductions | §161-199 | Expenses, depreciation, amortization |
| Itemized Deductions | §211-224 | Mortgage interest, SALT, charity |
| Corporate Deductions | §241-250 | DRD, organizational costs |
| NOL Rules | §261-281 | Net operating loss carrybacks/forwards |
| Deferred Compensation | §401-436 | 401(k), pensions, IRAs, 403(b) |
| Exempt Organizations | §501-530 | 501(c)(3), UBIT, foundations |
| RICs and REITs | §851-860 | Mutual funds, real estate trusts |
| Like-Kind Exchanges | §1031-1045 | Tax-deferred property swaps |
| Capital Gains | §1201-1260 | Long-term rates, character |
| S Corporations | §1361-1379 | Pass-through entity rules |
| Self-Employment Tax | §1401-1403 | SE tax calculation |
| FATCA | §1471-1474 | Foreign account reporting |

#### Good Coverage (70-90%)

| Area | Sections | Coverage |
|------|----------|----------|
| International Tax | §861-898 | ~74% - Source rules, FTC |
| Accounting Methods | §441-483 | ~79% - Cash vs accrual |
| Insurance Companies | §801-848 | ~62% - Life and P&C |

#### Partial Coverage (40-70%)

| Area | Sections | Coverage |
|------|----------|----------|
| Corporate Distributions | §301-318 | ~67% |
| Corporate Reorganizations | §351-386 | ~56% |
| CFCs | §951-965 | ~40% |

#### Major Gaps

| Area | Sections | Coverage | Impact |
|------|----------|----------|--------|
| **Partnerships** | §701-777 | **1%** | LLCs, investment funds, hedge funds |
| **Trusts & Estates** | §641-692 | **17%** | Trust income taxation, inheritance |
| **Natural Resources** | §611-638 | **0%** | Oil/gas depletion, mining |

---

### Subtitle B: Estate & Gift Taxes (§2001-2801) — ~89% Coverage

| Area | Coverage | Status |
|------|----------|--------|
| Estate Tax Rates & Credits | 100% | Complete |
| Gross Estate Inclusions | 100% | Complete |
| Estate Deductions | 100% | Complete |
| Gift Tax Rules | 100% | Complete |
| Special Valuation | 100% | Complete |
| Generation-Skipping Tax | 38% | Partial |

---

### Subtitle C: Employment Taxes (§3101-3512) — ~7% Coverage

| Area | Sections | Coverage | Status |
|------|----------|----------|--------|
| FICA | §3101-3128 | 0% | **Not formalized** |
| FUTA | §3301-3323 | 61% | Partial |
| Railroad Retirement | §3201-3241 | 0% | Not formalized |
| Withholding Procedures | §3401-3512 | 0% | Not formalized |

---

### Subtitles D-K — 0% Coverage

These are lower priority for most taxpayers:

| Subtitle | Sections | Description | Status |
|----------|----------|-------------|--------|
| D | §4001-5000D | Excise Taxes (fuel, luxury) | Not started |
| E | §5001-5891 | Alcohol, Tobacco, Firearms | Not started |
| F | §6001-7874 | IRS Procedure & Administration | Not started |
| G | §8001-8023 | Joint Committee on Taxation | Not started |
| H | §9001-9042 | Presidential Election Financing | Not started |
| I | §9500-9602 | Trust Fund Code | Not started |
| J | §9701-9722 | Coal Industry Health Benefits | Not started |
| K | §9801-9834 | Group Health Plan Requirements | Not started |

---

## Summary

```
                     │ Formalized │ Est. Total │ Coverage
─────────────────────┼────────────┼────────────┼──────────
Subtitle A (Income)  │    653     │    ~700    │   ~93%
Subtitle B (Estate)  │     98     │    ~110    │   ~89%
Subtitle C (Employ)  │     14     │    ~200    │    ~7%
Subtitles D-K        │      0     │   ~1,500   │     0%
─────────────────────┼────────────┼────────────┼──────────
TOTAL                │    765     │   ~2,500   │   ~31%
```

**For typical taxpayers**: ~751 sections covering ~90% of what individuals and businesses commonly encounter.

---

## Priority Gaps

### High Priority (Affects Many Taxpayers)

1. **Partnerships (§701-777)** — LLCs are the most popular business entity
2. **Trusts & Estates (§641-692)** — Trust income taxation, inheritance planning
3. **FICA (§3101-3128)** — Affects every employee and employer

### Medium Priority

4. **Natural Resources (§611-638)** — Oil/gas companies, mining
5. **CFCs completion (§957-965)** — International corporations
6. **Withholding (§3401-3512)** — Employer payroll compliance

### Low Priority

7. **Procedure & Admin (§6001+)** — Penalties, audits, collection
8. **Excise Taxes** — Industry-specific taxes

---

## Remaining `sorry` Statements

17 incomplete proofs in complex sections:

| Section | Topic |
|---------|-------|
| §32 | Earned Income Credit (complex phase-outs) |
| §103 | Municipal bond interest |
| §168 | Accelerated depreciation |
| §453 | Installment sales |
| §704 | Partnership allocations |
| §831 | Insurance company rules |
| §951-956 | Controlled foreign corps |
| §1297 | PFIC definitions |
