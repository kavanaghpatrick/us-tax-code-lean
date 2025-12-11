# Mass Formalization Strategy - US Tax Code

**Goal**: Formalize ALL 792 IRC sections as executable Lean 4 code for loophole analysis

**NOT**: Prove theorems (that comes later after we find interesting properties)

---

## Why This Approach?

### Original Mistake
We were using **Aristotle** (a theorem prover) to validate formalizations, but:
- Aristotle is for **proving theorems**, not generating/validating code
- We don't need theorems to find loopholes - we need **complete formalization**
- Skeleton sections returned unchanged from Aristotle (no theorems = nothing to prove)

### Correct Approach
1. **Formalize everything** as Lean definitions/functions
2. **Compile locally** to verify syntax
3. **Analyze for**:
   - Contradictions (section X says A, section Y says ¬A)
   - Unintended edge cases (input that's legal but produces absurd result)
   - Loopholes (combinations that minimize tax in unexpected ways)
4. **THEN prove theorems** about interesting properties we discover

---

## Data We Have

**Location**: `data/scraped_sections.json` (792 sections)

**Structure**:
```json
{
  "1": {
    "title": "Tax imposed",
    "text": "There is hereby imposed on the taxable income..."
  },
  "61": {
    "title": "Gross income defined",
    "text": "Except as otherwise provided..."
  }
}
```

---

## Formalization Levels

### Level 1: Structure Only (Fastest)
- Parse section into types/records
- Define function signatures
- Use `sorry` for complex logic
- **Goal**: Complete skeleton of entire tax code in 1-2 days

Example:
```lean
-- § 61: Gross income defined
structure GrossIncome where
  wages : Currency
  interest : Currency
  dividends : Currency
  -- ... more fields
  deriving Repr

def calculateGrossIncome (income : GrossIncome) : Currency :=
  sorry  -- TODO: Implement
```

### Level 2: Executable Logic (Medium)
- Implement actual calculations
- Handle references to other sections
- Parse formulas from text
- **Goal**: All sections executable in 1-2 weeks

Example:
```lean
def calculateGrossIncome (income : GrossIncome) : Currency :=
  income.wages + income.interest + income.dividends +
  income.rents + income.royalties + -- etc
```

### Level 3: Full Formalization (Complete)
- Precise edge cases
- All exemptions/exceptions
- Cross-references resolved
- **Goal**: Publication-ready formalization in 1-2 months

---

## Technical Architecture

### 1. Section Parser (`scripts/parse_section.py`)
- Input: Section text from `scraped_sections.json`
- Output: Lean AST or template
- Uses LLM (Claude/GPT) to convert legal text → Lean code

### 2. Code Generator (`scripts/generate_lean.py`)
- Takes parsed structure
- Generates Lean 4 code with proper imports
- Handles cross-references between sections
- Resolves type dependencies

### 3. Dependency Resolver
- Build dependency graph (which sections reference which)
- Topological sort for compilation order
- Detect circular dependencies (potential issues!)

### 4. Batch Compiler (`scripts/compile_all.sh`)
- Compile all sections with `lean`
- Report errors
- Track progress

### 5. Analysis Engine (`scripts/analyze_code.py`)
- Find contradictions
- Detect loopholes
- Check for edge cases
- Generate report

---

## Workflow

### Phase 1: Mass Generation (2-3 days)
```bash
# Generate all 792 sections at Level 1
python3 scripts/mass_formalize.py --level 1 --all

# Compile to find syntax errors
./scripts/compile_all.sh

# Fix compilation errors
python3 scripts/fix_errors.py

# Iterate until all compile
```

### Phase 2: Executable Code (1-2 weeks)
```bash
# Upgrade sections to Level 2 (batches of 50)
python3 scripts/mass_formalize.py --level 2 --sections 1-50

# Test with example tax scenarios
python3 scripts/test_scenarios.py

# Iterate on problematic sections
```

### Phase 3: Analysis (Ongoing)
```bash
# Find contradictions
python3 scripts/find_contradictions.py > CONTRADICTIONS.md

# Detect loopholes
python3 scripts/find_loopholes.py > LOOPHOLES.md

# Generate dependency graph
python3 scripts/dep_graph.py > deps.dot
dot -Tpng deps.dot -o tax_dependencies.png
```

### Phase 4: Theorem Proving (Future)
```bash
# For interesting properties, THEN use Aristotle
aristotle prove-from-file src/TaxCode/Section1_with_theorem.lean
```

---

## Repository Structure

```
us-tax-code-lean/
├── src/
│   ├── Common/
│   │   ├── Basic.lean          # Currency, FilingStatus, etc.
│   │   ├── Deductions.lean     # Common deduction types
│   │   └── Credits.lean        # Common credit types
│   ├── TaxCode/
│   │   ├── Section1.lean       # Individual sections
│   │   ├── Section61.lean
│   │   ├── ...
│   │   └── Section9834.lean
│   ├── Analysis/
│   │   ├── Contradictions.lean # Detected issues
│   │   └── Loopholes.lean      # Interesting patterns
│   └── TaxCode.lean            # Main import (all sections)
├── data/
│   ├── scraped_sections.json   # Source data
│   ├── dependency_graph.json   # Section dependencies
│   └── compilation_status.json # Which sections compile
├── scripts/
│   ├── parse_section.py        # Parse legal text
│   ├── generate_lean.py        # Generate Lean code
│   ├── mass_formalize.py       # Batch generation
│   ├── compile_all.sh          # Build everything
│   ├── find_contradictions.py  # Analysis
│   └── find_loopholes.py       # Loophole detection
├── tests/
│   └── scenarios/              # Tax scenarios for testing
├── docs/
│   ├── FORMALIZATION_STRATEGY.md  # This file
│   ├── CONTRADICTIONS.md          # Found issues
│   └── LOOPHOLES.md               # Found loopholes
└── lakefile.lean               # Lean build config
```

---

## LLM-Based Code Generation

### Prompt Template
```
Convert this IRC section to Lean 4 code:

Section: {section_number}
Title: {title}
Text: {text}

Requirements:
1. Define all types/structures mentioned
2. Implement calculation functions
3. Use Currency type (Int in cents)
4. Reference other sections as needed
5. Add comments for complex logic
6. Use 'sorry' if logic is too complex (Level 1)

Output only valid Lean 4 code.
```

### LLM Options
- **Claude Opus**: Best for complex sections (trust, AMT)
- **GPT-4**: Good for standard sections
- **Haiku**: Fast for simple sections
- **Batch processing**: Use API for cost efficiency

---

## Success Metrics

### Phase 1 Complete
- [ ] All 792 sections have Lean files
- [ ] All files compile successfully
- [ ] Dependency graph generated
- [ ] Basic types defined

### Phase 2 Complete
- [ ] All sections executable (no `sorry`)
- [ ] Test scenarios run
- [ ] Cross-references resolved
- [ ] Common patterns extracted

### Phase 3 Complete
- [ ] Contradictions documented
- [ ] Loopholes identified
- [ ] Analysis reports generated
- [ ] Interesting theorems identified

### Phase 4 Complete
- [ ] Key theorems proved with Aristotle
- [ ] Publication-ready paper
- [ ] Open-source release

---

## Example: Level 1 → Level 2 → Level 3

### Level 1 (Structure)
```lean
def calculateTax (income : Currency) (status : FilingStatus) : Currency :=
  sorry
```

### Level 2 (Executable)
```lean
def calculateTax (income : Currency) (status : FilingStatus) : Currency :=
  let brackets := getTaxBrackets status
  applyBrackets income brackets
```

### Level 3 (Complete)
```lean
def calculateTax (income : Currency) (status : FilingStatus) (year : TaxYear) : Currency :=
  let agi := calculateAGI income year
  let deductions := standardOrItemized income status year
  let taxableIncome := max 0 (agi - deductions)
  let brackets := getTaxBrackets status year
  let baseTax := applyBrackets taxableIncome brackets
  let credits := applyCredits baseTax status year
  max 0 (baseTax - credits)  -- Tax cannot be negative
```

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| Phase 1 | 2-3 days | All 792 sections compile |
| Phase 2 | 1-2 weeks | All sections executable |
| Phase 3 | 2-4 weeks | Analysis reports ready |
| Phase 4 | Ongoing | Theorems as discovered |

**Start**: Today
**Phase 1 Target**: Dec 14, 2025
**Phase 2 Target**: Jan 1, 2026
**Phase 3 Target**: Feb 1, 2026

---

## Next Steps

1. Build `mass_formalize.py` for batch generation
2. Test on 10 sections to validate approach
3. Scale to all 792 sections
4. Begin analysis for contradictions/loopholes
5. Document findings
6. (Later) Prove interesting theorems with Aristotle

---

**Key Insight**: We don't need theorems to find loopholes. We need complete, executable formalization. Theorems come AFTER we discover interesting properties through analysis.
