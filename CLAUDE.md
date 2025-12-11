# US Tax Code Formalization Project

## Mission
Formalize US Internal Revenue Code (Title 26) in Lean 4 using Harmonic Aristotle.

## Primary Source
**Cornell Law**: https://www.law.cornell.edu/uscode/text/26

## Architecture
```
src/           # Lean formalization files
  TaxCode/     # Main tax code modules
  Common/      # Shared definitions (currency, dates, persons, entities)
  Utils/       # Helper functions
docs/          # English descriptions, mapping IRC → Lean
tests/         # Test cases and examples
scripts/       # Aristotle automation
```

## Workflow
1. Select IRC section
2. Write English description in `docs/`
3. Run `aristotle prove-from-file` to generate Lean
4. Review, refine, test
5. Commit formal proof

## Critical Rules
- **Never commit API keys** (.gitignore enforced)
- **Cite IRC sections** in comments (e.g., `-- IRC §61(a)`)
- **Keep definitions atomic** - one concept per definition
- **Use Aristotle English mode** for complex sections
- **Test with real tax scenarios** from IRS publications

## Aristotle Commands
```bash
# Prove from English description
aristotle prove-from-file --api-key $ARISTOTLE_API_KEY docs/section_61.md

# Fill sorries in existing Lean
aristotle prove-from-file --api-key $ARISTOTLE_API_KEY src/TaxCode/Section61.lean
```

## Scoping Strategy
Start small, compound outward:
1. Core definitions (income, deductions, exemptions)
2. Simple sections (IRC §1 - tax rates)
3. Complex interdependencies (AMT, credits)
4. Full formalization

## Simplicity Filters
- ❌ Don't model entire legal system upfront
- ❌ Don't formalize every edge case initially
- ✅ Focus on most common scenarios (90% of taxpayers)
- ✅ Build vocabulary incrementally
- ✅ Prove core theorems first

## Tax-Specific Patterns
```lean
-- Currency amounts
def Currency := ℚ  -- Rationals for exact cents

-- Tax years
structure TaxYear where
  year : ℕ
  deriving DecidableEq

-- Filing status
inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidow
```
