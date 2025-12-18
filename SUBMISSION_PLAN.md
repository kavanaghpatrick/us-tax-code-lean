# Gap Submission Plan

**Objective**: Formalize the 4 major missing areas using existing infrastructure.

## The 4 Gaps (185 sections)

| Priority | Gap | Sections | Complexity |
|----------|-----|----------|------------|
| 1 | **Partnerships** | §701-777 (77) | HIGH |
| 2 | **Trusts/Estates** | §641-692 (52) | MEDIUM |
| 3 | **Natural Resources** | §611-638 (28) | MEDIUM |
| 4 | **FICA** | §3101-3128 (28) | LOW |

---

## Execution Plan (Using Existing Scripts)

### Phase 1: Scrape from Cornell Law

```bash
# Scrape each gap range
python3 scripts/scrape_cornell.py --range 701-777   # Partnerships
python3 scripts/scrape_cornell.py --range 641-692   # Trusts/Estates
python3 scripts/scrape_cornell.py --range 611-638   # Natural Resources
python3 scripts/scrape_cornell.py --range 3101-3128 # FICA
```

Or use the merge script to add to existing data:
```bash
python3 scripts/scrape_and_merge.py 701 777
python3 scripts/scrape_and_merge.py 641 692
python3 scripts/scrape_and_merge.py 611 638
python3 scripts/scrape_and_merge.py 3101 3128
```

### Phase 2: Generate Stubs & Submit

**Option A: Use batch_formalize.py** (creates skeletons + prepares + submits)
```bash
# Generate section list
FICA="3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117,3118,3119,3120,3121,3122,3123,3124,3125,3126,3127,3128"

# Dry run first
python3 scripts/batch_formalize.py --sections $FICA --dry-run

# Then submit
python3 scripts/batch_formalize.py --sections $FICA --submit
```

**Option B: Use aristotle_formalization_queue.py** (INFORMAL mode with natural language)
```bash
python3 scripts/aristotle_formalization_queue.py --sections "3101,3102,3103,3104,3105"
```

**Option C: Use process_remaining_stubs.py** (for existing stub files)
```bash
python3 scripts/process_remaining_stubs.py
```

---

## Recommended Order

### Step 1: Start with FICA (easiest, validates pipeline)
```bash
# Scrape
python3 scripts/scrape_and_merge.py 3101 3128

# Submit via INFORMAL mode
python3 scripts/aristotle_formalization_queue.py \
  --sections "3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117,3118,3119,3120,3121,3122,3123,3124,3125,3126,3127,3128"
```

### Step 2: Natural Resources
```bash
python3 scripts/scrape_and_merge.py 611 638
python3 scripts/aristotle_formalization_queue.py \
  --sections "611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638"
```

### Step 3: Trusts & Estates
```bash
python3 scripts/scrape_and_merge.py 641 692
# Submit in batches (large range)
python3 scripts/aristotle_formalization_queue.py \
  --sections "641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660"
python3 scripts/aristotle_formalization_queue.py \
  --sections "661,662,663,664,665,666,667,668,669,670,681,682,683,684,685,686,687,688,689,690,691,692"
```

### Step 4: Partnerships (most complex)
```bash
python3 scripts/scrape_and_merge.py 701 777
# Submit in multiple batches
python3 scripts/aristotle_formalization_queue.py \
  --sections "701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720"
# ... continue with remaining sections
```

---

## Monitoring

### Check Aristotle Queue Status
```bash
python3 scripts/aristotle_status.py
```

Or directly:
```bash
python3 << 'EOF'
import aristotlelib, os, asyncio

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))
    result = await aristotlelib.Project.list_projects()
    projects = result[0] if isinstance(result, tuple) else result

    for p in projects:
        pct = p.percent_complete or 0
        print(f"{p.status.name:12} {pct:3}% {p.file_name}")

asyncio.run(main())
EOF
```

### Check Batch Progress
```bash
python3 scripts/batch_formalize.py --status
```

---

## Time Estimates

| Phase | Scraping | Aristotle Processing |
|-------|----------|---------------------|
| FICA (28) | ~30s | ~1-2 hours |
| Natural Resources (28) | ~30s | ~1-2 hours |
| Trusts (52) | ~1 min | ~2-4 hours |
| Partnerships (77) | ~1.5 min | ~4-6 hours |

**Total**: ~3 minutes scraping + ~8-14 hours Aristotle processing

---

## Existing Scripts Reference

| Script | Purpose |
|--------|---------|
| `scripts/scrape_cornell.py` | Scrape IRC text from Cornell Law |
| `scripts/scrape_and_merge.py` | Scrape and merge with existing data |
| `scripts/batch_formalize.py` | Create skeletons + prepare + submit |
| `scripts/aristotle_formalization_queue.py` | INFORMAL mode submission |
| `scripts/process_remaining_stubs.py` | Process existing stub files |
| `scripts/aristotle_status.py` | Check Aristotle queue status |
| `scripts/prepare_aristotle.py` | Prepare file for Aristotle (inline deps) |

---

## Quick Start (One-Liner per Gap)

```bash
# FICA - Start here
python3 scripts/scrape_and_merge.py 3101 3128 && \
python3 scripts/aristotle_formalization_queue.py --sections "$(seq -s, 3101 3128)"

# Natural Resources
python3 scripts/scrape_and_merge.py 611 638 && \
python3 scripts/aristotle_formalization_queue.py --sections "$(seq -s, 611 638)"

# Trusts/Estates
python3 scripts/scrape_and_merge.py 641 692 && \
python3 scripts/aristotle_formalization_queue.py --sections "$(seq -s, 641 692)"

# Partnerships
python3 scripts/scrape_and_merge.py 701 777 && \
python3 scripts/aristotle_formalization_queue.py --sections "$(seq -s, 701 777)"
```
