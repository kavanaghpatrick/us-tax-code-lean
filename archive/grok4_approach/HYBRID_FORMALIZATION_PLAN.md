# Hybrid Formalization Plan (Grok-Validated)

**Date**: 2025-12-11
**Based On**: Grok's critical review
**Approach**: Hybrid LLM + Human validation
**Scope**: 50-100 priority sections (not all 792)

---

## Grok's Key Insights

1. **All 792 sections**: DOOMED ($100K-$500K, 6-12 months, low success rate)
2. **50-100 priority**: RISKY (but viable with human oversight)
3. **LLMs alone**: Can't formalize tax code correctly
4. **Solution**: Hybrid approach with human experts

---

## Hybrid Queue System Design

### Phase 1: LLM Draft Generation
**Tool**: Claude API (Opus for complex, Sonnet for simple)

**For each section**:
1. Generate initial Lean code from legal text
2. Compile locally to check syntax
3. Save as DRAFT (not final)
4. Flag for human review

**Output**: Draft formalization (unvalidated)

### Phase 2: Human Review & Correction
**Who**: Tax law expert OR you (manual review)

**For each draft**:
1. Review legal accuracy
2. Fix hallucinations/errors
3. Improve types/functions
4. Mark as VALIDATED

**Output**: Validated formalization

### Phase 3: Compilation & Testing
**Tool**: Local `lean` + test suite

**For each validated section**:
1. Compile with dependencies
2. Run test scenarios
3. Check cross-references
4. Mark as COMPLETE

**Output**: Production-ready formalization

---

## Scope: 50-100 Priority Sections

### Selection Criteria
1. **Most Referenced** - Hub sections that others depend on
2. **Highest Impact** - Affect most taxpayers
3. **Known Complexity** - Where loopholes likely exist
4. **Form Chain** - Depend on each other (test dependencies)

### Proposed 50 Priority Sections

**Income (10)**:
- §1 (Tax imposed) ✅ Already done
- §61 (Gross income) ✅ Already done
- §62 (AGI) - Review quality
- §63 (Taxable income) - Review quality
- §71 (Alimony)
- §101 (Life insurance)
- §102 (Gifts/inheritances)
- §103 (Municipal bonds)
- §108 (Discharge of indebtedness)
- §121 (Home sale exclusion)

**Deductions (15)**:
- §162 (Business expenses) ✅ Already done
- §163 (Interest)
- §164 (Taxes)
- §165 (Losses)
- §166 (Bad debts)
- §167 (Depreciation)
- §168 (MACRS)
- §170 (Charitable)
- §174 (R&D)
- §179 (Section 179 expensing)
- §195 (Start-up costs)
- §212 (Investment expenses)
- §213 (Medical)
- §217 (Moving)
- §274 (Entertainment limits)

**Credits (10)**:
- §21 (Child care)
- §24 (Child tax credit) ✅ Already done
- §25A (Education credits)
- §25D (Energy credits)
- §30D (EV credit)
- §31 (Tax withheld)
- §32 (EITC) ✅ Already done
- §38 (General business credit)
- §41 (R&D credit)
- §45 (Renewable energy)

**Capital Gains (10)**:
- §1001 (Gain/loss determination)
- §1011 (Adjusted basis)
- §1012 (Basis - cost)
- §1014 (Basis - inherited)
- §1015 (Basis - gifts)
- §1031 (Like-kind exchange)
- §1202 (QSBS exclusion)
- §1221 (Capital asset defined)
- §1222 (Capital gains terms)
- §1231 (Property used in trade/business)

**Corporate/Partnership (5)**:
- §11 (Corporate tax)
- §301 (Distributions)
- §302 (Stock redemptions)
- §704 (Partnership allocations)
- §721 (Partnership contributions)

**Total**: 50 sections

---

## Queue System Implementation

### Data Structure
```json
{
  "sections": {
    "1": {
      "status": "validated",  // pending, drafted, validated, complete, failed
      "draft_generated": "2025-12-11",
      "human_reviewed": "2025-12-11",
      "quality_score": 9,
      "notes": "Already formalized, high quality"
    },
    "61": {
      "status": "validated",
      ...
    }
  },
  "metrics": {
    "pending": 43,
    "drafted": 0,
    "validated": 7,
    "complete": 7,
    "failed": 0
  }
}
```

### FormalizationQueue Class

```python
class FormalizationQueue:
    def __init__(self):
        self.queue_file = 'data/formalization_queue.json'
        self.load_queue()

    def generate_draft(self, section_num):
        """Generate initial draft with Claude API"""
        # 1. Load legal text
        # 2. Call Claude API with prompt
        # 3. Save draft
        # 4. Try to compile
        # 5. Update status

    def review_section(self, section_num):
        """Human review workflow"""
        # 1. Display draft
        # 2. Get human input/edits
        # 3. Update section
        # 4. Mark as validated

    def process_batch(self, count=10):
        """Process next N sections"""
        # 1. Generate drafts in parallel
        # 2. Queue for human review
        # 3. Track progress

    def get_status(self):
        """Show queue status"""
        # Progress, ETA, costs
```

---

## Cost Estimates (50 Sections)

### LLM API Costs
**Per Section**:
- Input: ~5,000 tokens (legal text + prompt)
- Output: ~2,000 tokens (Lean code)
- Total: ~7,000 tokens per section

**Claude Opus Pricing**:
- Input: $15/M tokens
- Output: $75/M tokens
- Per section: ~$0.23

**50 Sections**: $11.50 (very affordable!)

**With retries/iterations**: ~$50-100 total

### Time Estimates (50 Sections)

**LLM Generation**: ~5 min per section = 4 hours total
**Human Review**: ~30 min per section = 25 hours total
**Testing/Fixes**: ~15 min per section = 12.5 hours total

**Total**: ~40 hours of work spread over 1-2 weeks

---

## Validation Strategy

### Automated Checks
1. ✅ Compiles with `lean`
2. ✅ Has type definitions
3. ✅ Has functions (not just TODO)
4. ✅ Cross-references resolve
5. ✅ Examples run (if present)

### Human Review Checklist
- [ ] Legal accuracy (matches IRC text)
- [ ] Type definitions make sense
- [ ] Functions implement correct logic
- [ ] Cross-references are correct
- [ ] Edge cases considered

---

## Rollout Plan

### Week 1: Pilot (10 sections)
- Generate drafts for 10 priority sections
- Human review and validate
- Identify common LLM errors
- Refine prompts/process

**Deliverable**: 10 validated sections + lessons learned

### Week 2-3: Scale (40 sections)
- Generate remaining 40 drafts
- Human review in batches of 10
- Fix common patterns
- Build test suite

**Deliverable**: 50 validated sections total

### Week 4: Analysis
- Build dependency graph
- Run contradiction detector
- Run loophole finder
- Generate reports

**Deliverable**: Findings on 50 core sections

---

## Success Criteria

**Minimum Viable**:
- 30/50 sections validated and working
- At least 5 contradictions found
- At least 10 loopholes identified
- Publication-ready findings

**Stretch Goal**:
- 50/50 sections validated
- 10+ contradictions
- 20+ loopholes
- Academic paper draft

---

## Risk Mitigation

### If LLM Quality is Bad
- Increase human review time
- Use LLM only for skeleton
- Hand-formalize critical sections

### If Takes Too Long
- Reduce scope to 30 sections
- Focus on high-value areas
- Accept some incomplete sections

### If Analysis Finds Nothing
- Still have formalized core tax code
- Proof of concept for methodology
- Can extend later if promising

---

## Decision Point

**After Pilot (10 sections)**:
- If quality good → Continue to 50
- If quality bad → Reduce scope or pivot
- If cost high → Use cheaper models
- If too slow → Reduce human review

**Grok's Advice**: Treat as research, be ready to abandon

---

**Recommended Next Step**: Build queue system for 10-section pilot, validate approach before scaling.
