# Gap Submission Plan

**Objective**: Formalize the 4 major missing areas of the US Tax Code

## Overview

| Gap | Sections | Priority | Complexity | Impact |
|-----|----------|----------|------------|--------|
| **Partnerships** | §701-777 (77) | 1 - Highest | HIGH | LLCs are #1 business entity |
| **Trusts & Estates** | §641-692 (52) | 2 | MEDIUM | Trust taxation, inheritance |
| **Natural Resources** | §611-638 (28) | 3 | MEDIUM | Oil/gas depletion, mining |
| **FICA** | §3101-3128 (28) | 4 | LOW | Every paycheck |

**Total**: 185 sections

---

## Pipeline

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  1. SCRAPE      │────▶│  2. GENERATE    │────▶│  3. SUBMIT      │────▶│  4. INTEGRATE   │
│  Cornell Law    │     │  Lean Stubs     │     │  Aristotle      │     │  Output Files   │
│  ~3 min/gap     │     │  ~5 min/gap     │     │  ~2-4 hrs/gap   │     │  Automatic      │
└─────────────────┘     └─────────────────┘     └─────────────────┘     └─────────────────┘
```

### Step 1: Scrape from Cornell Law
- Fetches legal text from https://www.law.cornell.edu/uscode/text/26
- Rate-limited: 1 request/second
- Outputs to: `data/sections.json`

### Step 2: Generate Lean Stubs
- Uses Claude Sonnet to create initial Lean 4 code
- Creates type definitions, function signatures
- Outputs to: `src/TaxCode/SectionXXX.lean`

### Step 3: Submit to Aristotle
- Batches of 5 sections (Aristotle limit)
- Uses INFORMAL mode for proof search
- Polls every 60 seconds for completion

### Step 4: Integrate Results
- Copies proven files to: `src/TaxCode/SectionXXX_aristotle_output.lean`
- Automatically triggered on completion

---

## Time Estimates

| Phase | Partnerships | Trusts | Resources | FICA | Total |
|-------|--------------|--------|-----------|------|-------|
| Scrape | 1.5 min | 1 min | 0.5 min | 0.5 min | ~4 min |
| Generate | 5 min | 3 min | 2 min | 2 min | ~12 min |
| Aristotle | 2-4 hrs | 1-2 hrs | 1 hr | 1 hr | ~6-10 hrs |
| **Total** | ~4 hrs | ~2 hrs | ~1.5 hrs | ~1.5 hrs | **~9 hrs** |

**Note**: Aristotle processing is the bottleneck. Each batch of 5 sections takes 20-60 minutes depending on complexity.

---

## Commands

```bash
# Check current status
python scripts/gap_submission_plan.py status

# Show execution plan
python scripts/gap_submission_plan.py plan

# Run individual phases
python scripts/gap_submission_plan.py scrape partnerships
python scripts/gap_submission_plan.py generate partnerships
python scripts/gap_submission_plan.py submit partnerships

# Run full pipeline for one gap
python scripts/gap_submission_plan.py run partnerships

# Run full pipeline for all gaps (recommended)
python scripts/gap_submission_plan.py run all

# Dry run (show what would be done)
python scripts/gap_submission_plan.py run all --dry-run
```

---

## Execution Order (Recommended)

### Phase 1: FICA (Priority: Start Here)
**Why**: Lowest complexity, quick win, validates the pipeline

```bash
python scripts/gap_submission_plan.py run fica
```

Expected outcome:
- 28 new sections formalized
- ~1.5 hours total time
- Validates scraping and submission work

### Phase 2: Natural Resources
**Why**: Medium complexity, oil/gas industry relevance

```bash
python scripts/gap_submission_plan.py run natural_resources
```

Expected outcome:
- 28 new sections formalized
- Depletion allowance rules
- Percentage depletion calculations

### Phase 3: Trusts & Estates
**Why**: High impact for estate planning, builds on existing grantor trust rules (§671-679)

```bash
python scripts/gap_submission_plan.py run trusts
```

Expected outcome:
- 52 new sections formalized (we already have §671-679)
- Trust income distribution rules
- Simple trust vs complex trust distinctions

### Phase 4: Partnerships (Most Complex)
**Why**: Highest impact but most complex - do last

```bash
python scripts/gap_submission_plan.py run partnerships
```

Expected outcome:
- 77 new sections formalized (we already have §704)
- Partnership allocations
- Basis adjustments
- Distributions and liquidations

---

## Monitoring

### Check Aristotle Queue
```bash
python3 << 'EOF'
import aristotlelib, os, asyncio

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))
    projects = await aristotlelib.Project.list_projects()

    if isinstance(projects, tuple):
        projects = projects[0]

    for p in projects:
        print(f"{p.status.name:12} {p.percent_complete or 0:3}% {p.file_name}")

asyncio.run(main())
EOF
```

### Check Logs
```bash
tail -f logs/gap_submission.log
```

### Check Integration Status
```bash
python scripts/gap_submission_plan.py status
```

---

## Troubleshooting

### "5 projects in progress"
Aristotle limits concurrent submissions. The script waits automatically.

### Scraping fails
Check Cornell Law is accessible. Rate limiting may require longer delays.

### Claude API errors
Ensure `ANTHROPIC_API_KEY` is set. Check rate limits.

### Aristotle timeout
Some complex sections take longer. Max wait is 2 hours per batch.

### Large files rejected
Files >45KB are truncated. Editorial notes are removed automatically.

---

## Expected Results

After completing all 4 gaps:

| Metric | Current | After |
|--------|---------|-------|
| Total Sections | 765 | 950 |
| Subtitle A Coverage | 93% | ~98% |
| Partnerships | 1% | 100% |
| Trusts/Estates | 17% | 100% |
| Natural Resources | 0% | 100% |
| FICA | 0% | 100% |

---

## Post-Completion

After all submissions complete:

1. **Verify builds**: `lake build`
2. **Run loophole finder**: `python tools/safe_loophole_finder.py`
3. **Update README**: Reflect new coverage stats
4. **Commit and push**: Save all new formalizations

---

## Files

| File | Purpose |
|------|---------|
| `scripts/gap_submission_plan.py` | Main orchestration script |
| `scripts/scrape_cornell.py` | Cornell Law scraper |
| `data/sections.json` | Scraped section data |
| `logs/gap_submission.log` | Execution log |
