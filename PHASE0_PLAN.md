# Phase 0: Validate on 10 Core Sections (SIMPLIFIED)

**Duration**: 1 week (Dec 12-19)
**Goal**: Prove the workflow works, extract patterns

---

## Simplicity First

**What we WON'T build** (over-engineering):
- ❌ GitHub Actions CI/CD (just run `lean` locally)
- ❌ Complex review process (we'll know if it works)
- ❌ Error tracking system (10 sections, manual is fine)
- ❌ Fancy dashboards (overkill)

**What we WILL do** (minimum viable):
- ✅ Pick 10 critical sections
- ✅ Generate code with LLM (Claude API)
- ✅ Compile with `lean` locally
- ✅ Fix errors manually
- ✅ Document what works/doesn't

**Time saved**: ~2 days on infrastructure → More time on actual formalization

---

## 10 Core Sections (Selected)

Based on most-referenced and tax importance:

1. **§1** - Tax imposed (already have this, but will regenerate)
2. **§61** - Gross income defined (fundamental)
3. **§62** - Adjusted gross income (builds on 61)
4. **§63** - Taxable income (builds on 62)
5. **§162** - Trade or business expenses (most common deduction)
6. **§163** - Interest deduction (major deduction)
7. **§170** - Charitable contributions (complex rules)
8. **§1001** - Gain or loss determination (capital gains foundation)
9. **§1221** - Capital asset defined (references 1001)
10. **§1222** - Capital gain/loss terms (references 1221)

**Why these?**:
- Cover income (61-63), deductions (162-163, 170), and capital gains (1001, 1221-1222)
- Already have skeletons for most (from Wave 1)
- Represent different complexity levels
- Form a dependency chain (can test cross-references)

---

## Workflow (Hybrid LLM + Human)

### Step 1: LLM Generation (Claude Opus)
```bash
# For each section:
python3 scripts/generate_section.py --section 61 --level 2
```

**Prompt**: "Convert IRC §61 to executable Lean 4 code with types and functions"

**Output**: `src/TaxCode/Section61.lean` (Level 2 - executable)

### Step 2: Local Compilation
```bash
# Test if it compiles
lean src/TaxCode/Section61.lean
```

**If errors**: Fix manually, document common issues

### Step 3: Commit
```bash
git add src/TaxCode/Section61.lean
git commit -m "Add §61 - Gross income (LLM generated, compiled)"
git push
```

**Total time per section**: 15-30 minutes (including fixes)
**Total for 10 sections**: 3-5 hours of actual work

---

## LLM Prompt Template

```markdown
You are a Lean 4 expert formalizing US Tax Code.

Convert the following IRC section to executable Lean 4 code:

**Section**: {section_number}
**Title**: {title}
**Text**: {text}

Requirements:
1. Define all types/structures mentioned
2. Implement calculation functions (executable, no 'sorry')
3. Use Currency type from Common.Basic (Int in cents)
4. Reference other sections as needed (import statements)
5. Add comments for complex logic
6. Follow Lean 4 best practices

Context:
- Currency type already defined: `def Currency := Int`
- FilingStatus: `Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold`
- TaxYear: `structure TaxYear where year : Nat`

Output ONLY valid Lean 4 code, no explanations.
```

---

## Script to Build (`scripts/generate_section.py`)

```python
#!/usr/bin/env python3
"""
Generate Lean code for a single IRC section using Claude API.
"""

import argparse
import json
import os
from pathlib import Path
from anthropic import Anthropic

def generate_section(section_num: str, level: int = 2):
    """Generate Lean code for a section."""

    # Load scraped data
    data_file = Path(__file__).parent.parent / 'data' / 'scraped_sections.json'
    with open(data_file) as f:
        sections = json.load(f)

    if section_num not in sections:
        print(f"Section {section_num} not found in scraped data")
        return

    section = sections[section_num]

    # Prepare prompt
    prompt = f"""You are a Lean 4 expert formalizing US Tax Code.

Convert the following IRC section to executable Lean 4 code:

**Section**: {section_num}
**Title**: {section['title']}
**Text**: {section['text'][:2000]}...

Requirements:
1. Define all types/structures mentioned
2. Implement calculation functions (executable, no 'sorry')
3. Use Currency type from Common.Basic (Int in cents)
4. Reference other sections as needed (import statements)
5. Add comments for complex logic
6. Follow Lean 4 best practices

Context:
- Currency type already defined: `def Currency := Int`
- FilingStatus: `Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold`
- TaxYear: `structure TaxYear where year : Nat`

Output ONLY valid Lean 4 code, no explanations."""

    # Call Claude API
    client = Anthropic(api_key=os.getenv('ANTHROPIC_API_KEY'))

    print(f"Generating §{section_num} - {section['title']}...")

    response = client.messages.create(
        model="claude-opus-4-20250514",
        max_tokens=4000,
        messages=[{"role": "user", "content": prompt}]
    )

    code = response.content[0].text

    # Save to file
    output_file = Path(__file__).parent.parent / 'src' / 'TaxCode' / f'Section{section_num}.lean'
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as f:
        f.write(code)

    print(f"✓ Generated: {output_file}")
    print(f"  Tokens: {response.usage.input_tokens} in, {response.usage.output_tokens} out")

    return output_file

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate Lean code for IRC section')
    parser.add_argument('--section', required=True, help='Section number (e.g., 61)')
    parser.add_argument('--level', type=int, default=2, help='Generation level (1-3)')

    args = parser.parse_args()
    generate_section(args.section, args.level)
```

---

## Success Criteria (Simple)

**By Dec 19**:
- [ ] 10 sections generated with LLM
- [ ] All 10 compile with `lean`
- [ ] Documented common LLM errors and how to fix
- [ ] Extracted 5+ common patterns
- [ ] Ready to scale to 50 sections

**Metrics**:
- Time per section: Target <30 min
- Compilation success rate: Target >80% on first try
- Common error types: Document top 5

---

## Common Patterns to Extract

Watch for these as we formalize:

1. **Income aggregation** (§61, 62, 63):
   - Pattern: Sum multiple income sources
   - Template: `def total := field1 + field2 + ...`

2. **Phase-outs** (many sections):
   - Pattern: Benefit reduces as income increases
   - Template: `def phaseOut (income : Currency) (limit : Currency) := max 0 (limit - income)`

3. **Brackets** (§1, others):
   - Pattern: Progressive rates
   - Template: Already have in Section1.lean

4. **Limitations** (§162, 163, 170):
   - Pattern: Max deduction based on income %
   - Template: `def limited := min claimed (income * percent)`

5. **Cross-references**:
   - Pattern: "as defined in section X"
   - Template: `import TaxCode.SectionX`

---

## What Could Go Wrong?

**Problem 1**: LLM generates invalid Lean syntax
**Fix**: Keep prompt examples, iterate on prompt

**Problem 2**: LLM hallucinates types/functions
**Fix**: Provide explicit type definitions in prompt

**Problem 3**: Cross-references don't resolve
**Fix**: Generate in dependency order (use topological sort)

**Problem 4**: Taking too long per section
**Fix**: Use GPT-4 instead of Opus for simpler sections

---

## Timeline

**Day 1 (Dec 12)**:
- Build `generate_section.py` script
- Test on §61
- Fix issues, iterate on prompt

**Day 2-3 (Dec 13-14)**:
- Generate remaining 9 sections
- Fix compilation errors
- Document patterns

**Day 4 (Dec 15)**:
- Extract common patterns to library
- Write `PATTERNS.md` documentation
- Clean up code

**Day 5 (Dec 16)**:
- Test cross-references work
- Write simple test scenarios
- Validate dependency chain

**Days 6-7 (Dec 17-19)**:
- Buffer for issues
- Write Phase 0 retrospective
- Plan Phase 1 (50 sections)

---

## Deliverables

1. **Code**: 10 sections in `src/TaxCode/`
2. **Patterns**: `docs/PATTERNS.md` with common structures
3. **Retrospective**: `PHASE0_RETROSPECTIVE.md` (what worked/didn't)
4. **Script**: `scripts/generate_section.py` (reusable for Phase 1)

---

## Next Immediate Step

Build `scripts/generate_section.py` and test on §61 RIGHT NOW.

**Time estimate**: 30 minutes to working script
