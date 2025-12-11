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
- **🎯 GitHub is Source of Truth** - ALL work tracking, planning, and status MUST be in GitHub (issues, projects, commits). Never rely on local files or external tools for coordination.
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
def Currency := Int  -- CRITICAL: Use Int, not ℚ (see Type Class Rules below)

-- Tax years
structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913  -- First year of modern income tax
  deriving DecidableEq

-- Filing status (IRC §1)
inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower  -- Note: Widow(er) not Widow
```

---

## Aristotle Status Checking

### Quick Status Check
```bash
# Check all Aristotle project statuses
python3 << 'EOF'
import aristotlelib, os, asyncio

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))
    projects = await aristotlelib.Project.list_projects()

    if projects and isinstance(projects[0], list):
        active = [p for p in projects[0] if 'status: QUEUED' in p or 'status: IN_PROGRESS' in p]
        complete = [p for p in projects[0] if 'status: COMPLETE' in p]

        print(f"🚀 Active: {len(active)}")
        print(f"✅ Complete: {len(complete)}")

        for p in active:
            file = [l for l in p.split('\n') if 'file name:' in l][0]
            print(f"  {file}")

asyncio.run(main())
EOF
```

### Project States
- `QUEUED`: Waiting to start
- `IN_PROGRESS`: Currently proving (includes % complete)
- `COMPLETE`: Finished (check email for `*-output.lean`)
- `FAILED`: Compilation/proof failed
- `PENDING_RETRY`: Temporary failure, will retry

### Results Location
- **Email**: Primary delivery method (`*-output.lean` attachments)
- **API**: Can poll via `Project.from_id(uuid).refresh()`
- **No Dashboard**: Must use CLI/API or wait for emails

---

## Critical Type Class Rules

### Currency Instances (MUST FOLLOW)

**CRITICAL**: Since `Currency := Int`, ALL arithmetic instances MUST use explicit Int operations to avoid circular references.

```lean
-- ✅ CORRECT - Use explicit Int operations
instance : HAdd Currency Currency Currency where
  hAdd a b := Int.add a b  -- NOT: a + b (circular!)

instance : HDiv Currency Int Currency where
  hDiv a b := Int.tdiv a b  -- NOT: Int.div (deprecated in Lean 4.14)

instance : Max Currency where
  max a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then bi else ai
  -- NOT: Int.max a b (doesn't exist in Lean 4.14.0)
```

**❌ BANNED Patterns**:
- Using `+`, `-`, `*`, `/` in instance body (causes circular reference)
- Using `Int.div` (deprecated → use `Int.tdiv`)
- Using `Int.max` or `Int.min` (don't exist in Lean 4.14)

### Self-Contained Files for Aristotle

Aristotle can't access project modules. Must inline dependencies:

**Workflow**:
1. Write: `src/TaxCode/Section64.lean` with `import Common.Basic`
2. Prepare: `python3 scripts/prepare_aristotle.py 64`
3. Submit: `src/TaxCode/Section64_aristotle.lean` (inlined version)

**NEVER**:
- Submit files with imports to Aristotle
- Manually edit `*_aristotle.lean` files (regenerate from source)

---

## Verified Theorems Tracker

See `PROOFS.md` for complete list. Current count: **3 theorems verified**

Quick check:
```bash
cat PROOFS.md | grep "^#### Theorem" | wc -l
```
