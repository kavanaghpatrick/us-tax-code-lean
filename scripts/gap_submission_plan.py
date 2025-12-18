#!/usr/bin/env python3
"""
Gap Submission Plan - Formalize the 4 major missing areas:
1. Partnerships (§701-777) - 77 sections
2. Trusts/Estates (§641-692) - 52 sections
3. Natural Resources (§611-638) - 28 sections
4. FICA (§3101-3128) - 28 sections

Total: 185 sections

Pipeline:
1. Scrape from Cornell Law → data/sections.json
2. Generate Lean stubs (Claude) → src/TaxCode/SectionXXX.lean
3. Submit to Aristotle (batches of 5) → Proves theorems
4. Integrate results → src/TaxCode/SectionXXX_aristotle_output.lean
"""

import asyncio
import json
import os
import re
import shutil
import sys
import time
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Optional

# Add scripts to path for imports
sys.path.insert(0, str(Path(__file__).parent))

try:
    import aristotlelib
    from scrape_cornell import CornellScraper
except ImportError as e:
    print(f"Import error: {e}")
    print("Make sure aristotlelib and beautifulsoup4 are installed")
    sys.exit(1)

try:
    from anthropic import Anthropic
    CLAUDE_AVAILABLE = True
except ImportError:
    CLAUDE_AVAILABLE = False
    print("Warning: anthropic not installed, stub generation will be skipped")


# Configuration
GAPS = {
    "partnerships": {
        "name": "Partnerships",
        "range": (701, 777),
        "priority": 1,
        "description": "LLCs, investment partnerships, hedge funds",
        "complexity": "HIGH - complex allocation rules",
    },
    "trusts": {
        "name": "Trusts & Estates",
        "range": (641, 692),
        "priority": 2,
        "description": "Trust income taxation, inheritance",
        "complexity": "MEDIUM - fiduciary rules",
    },
    "natural_resources": {
        "name": "Natural Resources",
        "range": (611, 638),
        "priority": 3,
        "description": "Oil/gas depletion, mining",
        "complexity": "MEDIUM - percentage depletion",
    },
    "fica": {
        "name": "FICA",
        "range": (3101, 3128),
        "priority": 4,
        "description": "Social Security/Medicare taxes",
        "complexity": "LOW - straightforward calculations",
    },
}

# Paths
PROJECT_ROOT = Path(__file__).parent.parent
DATA_DIR = PROJECT_ROOT / "data"
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"
LOG_DIR = PROJECT_ROOT / "logs"

# Aristotle limits
BATCH_SIZE = 5
POLL_INTERVAL = 60
MAX_FILE_SIZE = 45000

# Common type definitions (inline for Aristotle)
COMMON_DEFS = '''
def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq

inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited
'''


def log(msg: str, level: str = "INFO"):
    """Log message with timestamp."""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{timestamp}] [{level}] {msg}"
    print(line)

    LOG_DIR.mkdir(exist_ok=True)
    with open(LOG_DIR / "gap_submission.log", "a") as f:
        f.write(line + "\n")


def load_sections_data() -> Dict[int, Dict]:
    """Load existing scraped sections."""
    sections_file = DATA_DIR / "sections.json"
    if not sections_file.exists():
        return {}

    with open(sections_file) as f:
        sections_list = json.load(f)

    result = {}
    for s in sections_list:
        num = s.get("section")
        if isinstance(num, int):
            result[num] = s
        elif isinstance(num, str) and num.isdigit():
            result[int(num)] = s
    return result


def save_sections_data(sections: Dict[int, Dict]):
    """Save sections data back to file."""
    sections_list = [sections[num] for num in sorted(sections.keys())]
    with open(DATA_DIR / "sections.json", "w") as f:
        json.dump(sections_list, f, indent=2)


def get_gap_sections(gap_key: str) -> List[int]:
    """Get list of section numbers for a gap."""
    gap = GAPS[gap_key]
    start, end = gap["range"]
    return list(range(start, end + 1))


def analyze_gaps() -> Dict[str, Dict]:
    """Analyze current state of all gaps."""
    existing_sections = load_sections_data()
    existing_files = {
        int(re.search(r"Section(\d+)", f.name).group(1))
        for f in TAXCODE_DIR.glob("Section*.lean")
        if re.search(r"Section(\d+)", f.name) and "_backup" not in f.name
    }

    analysis = {}
    for key, gap in GAPS.items():
        sections = get_gap_sections(key)
        scraped = [s for s in sections if s in existing_sections]
        has_stub = [s for s in sections if s in existing_files]
        has_output = [
            s for s in sections
            if (TAXCODE_DIR / f"Section{s}_aristotle_output.lean").exists()
        ]

        analysis[key] = {
            "total": len(sections),
            "scraped": len(scraped),
            "need_scrape": [s for s in sections if s not in existing_sections],
            "has_stub": len(has_stub),
            "need_stub": [s for s in scraped if s not in existing_files],
            "has_output": len(has_output),
            "need_aristotle": [
                s for s in has_stub
                if not (TAXCODE_DIR / f"Section{s}_aristotle_output.lean").exists()
            ],
        }

    return analysis


def print_analysis(analysis: Dict[str, Dict]):
    """Print analysis in readable format."""
    print("\n" + "=" * 70)
    print("GAP SUBMISSION PLAN - CURRENT STATUS")
    print("=" * 70)

    total_sections = 0
    total_scraped = 0
    total_stubs = 0
    total_outputs = 0

    for key, gap in GAPS.items():
        a = analysis[key]
        total_sections += a["total"]
        total_scraped += a["scraped"]
        total_stubs += a["has_stub"]
        total_outputs += a["has_output"]

        print(f"\n{gap['name']} (§{gap['range'][0]}-{gap['range'][1]})")
        print(f"  Priority: {gap['priority']} | Complexity: {gap['complexity']}")
        print(f"  Description: {gap['description']}")
        print(f"  ─────────────────────────────────────────")
        print(f"  Total sections:     {a['total']:3}")
        print(f"  Scraped:            {a['scraped']:3} ({len(a['need_scrape'])} need scraping)")
        print(f"  Have stub:          {a['has_stub']:3} ({len(a['need_stub'])} need generation)")
        print(f"  Have Aristotle:     {a['has_output']:3} ({len(a['need_aristotle'])} need submission)")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total sections to formalize: {total_sections}")
    print(f"Already scraped:             {total_scraped}")
    print(f"Already have stubs:          {total_stubs}")
    print(f"Already have outputs:        {total_outputs}")
    print(f"Remaining work:              {total_sections - total_outputs} sections")
    print("=" * 70)


# ============================================================================
# STEP 1: SCRAPING
# ============================================================================

def scrape_gap(gap_key: str, dry_run: bool = False) -> int:
    """Scrape all missing sections for a gap."""
    analysis = analyze_gaps()
    need_scrape = analysis[gap_key]["need_scrape"]

    if not need_scrape:
        log(f"No sections need scraping for {gap_key}")
        return 0

    log(f"Scraping {len(need_scrape)} sections for {gap_key}")

    if dry_run:
        log(f"DRY RUN: Would scrape sections {need_scrape[:10]}...")
        return len(need_scrape)

    scraper = CornellScraper(delay=1.0)
    sections_data = load_sections_data()
    scraped_count = 0

    for section_num in need_scrape:
        try:
            section_data = scraper.scrape_section(str(section_num))
            if section_data:
                sections_data[section_num] = section_data
                scraped_count += 1
                log(f"  ✓ Scraped §{section_num}")
            else:
                log(f"  ✗ No data for §{section_num}", "WARN")
        except Exception as e:
            log(f"  ✗ Error scraping §{section_num}: {e}", "ERROR")

        time.sleep(1.0)  # Rate limiting

    save_sections_data(sections_data)
    log(f"Scraped {scraped_count}/{len(need_scrape)} sections for {gap_key}")
    return scraped_count


# ============================================================================
# STEP 2: STUB GENERATION
# ============================================================================

def generate_stub(section_num: int, section_data: Dict) -> Optional[Path]:
    """Generate a Lean stub for a section using Claude."""
    if not CLAUDE_AVAILABLE:
        log("Claude API not available", "ERROR")
        return None

    # Truncate text for prompt
    text = section_data.get("text", "")[:4000]
    title = section_data.get("title", f"Section {section_num}")

    prompt = f"""You are formalizing US Tax Code in Lean 4.

Create a Lean 4 stub file for IRC Section {section_num}: {title}

The stub should:
1. Start with: import TaxCode.Common.Basic
2. Define relevant structures for entities mentioned
3. Create function signatures with 'sorry' placeholders for proofs
4. Use Currency (Int) for monetary amounts
5. Add comments citing the IRC section
6. Be syntactically valid Lean 4

Section text:
{text}

Output ONLY valid Lean 4 code."""

    try:
        client = Anthropic()
        response = client.messages.create(
            model="claude-sonnet-4-20250514",
            max_tokens=4000,
            messages=[{"role": "user", "content": prompt}]
        )

        code = response.content[0].text

        # Clean up code (remove markdown fences if present)
        code = re.sub(r"^```\w*\n?", "", code)
        code = re.sub(r"\n?```$", "", code)

        # Save to file
        output_file = TAXCODE_DIR / f"Section{section_num}.lean"
        output_file.write_text(code)

        return output_file

    except Exception as e:
        log(f"Error generating stub for §{section_num}: {e}", "ERROR")
        return None


def generate_stubs_for_gap(gap_key: str, dry_run: bool = False) -> int:
    """Generate stubs for all sections in a gap that need them."""
    sections_data = load_sections_data()
    analysis = analyze_gaps()
    need_stub = analysis[gap_key]["need_stub"]

    if not need_stub:
        log(f"No stubs needed for {gap_key}")
        return 0

    log(f"Generating {len(need_stub)} stubs for {gap_key}")

    if dry_run:
        log(f"DRY RUN: Would generate stubs for {need_stub[:10]}...")
        return len(need_stub)

    generated = 0
    for section_num in need_stub:
        section_data = sections_data.get(section_num, {})
        if not section_data:
            log(f"  ⚠ No scraped data for §{section_num}", "WARN")
            continue

        output = generate_stub(section_num, section_data)
        if output:
            log(f"  ✓ Generated stub: {output.name}")
            generated += 1

        time.sleep(0.5)  # Rate limiting

    log(f"Generated {generated}/{len(need_stub)} stubs for {gap_key}")
    return generated


# ============================================================================
# STEP 3: ARISTOTLE SUBMISSION
# ============================================================================

def prepare_for_aristotle(stub_path: Path) -> str:
    """Prepare file content for Aristotle submission."""
    content = stub_path.read_text()

    # Replace import with inline definitions
    content = re.sub(
        r"import\s+(TaxCode\.)?Common\.Basic\s*\n?",
        f"\nimport Mathlib\n{COMMON_DEFS}\n",
        content
    )

    if "import Mathlib" not in content:
        content = "import Mathlib\n" + content

    return content


async def submit_batch_to_aristotle(stubs: List[Path]) -> List[str]:
    """Submit a batch of stubs to Aristotle and wait for completion."""
    active = {}  # project_id -> (section_name, stub_path)

    for stub_path in stubs:
        section_name = stub_path.stem
        content = prepare_for_aristotle(stub_path)

        try:
            result = await aristotlelib.Project.prove_from_file(
                input_content=content,
                wait_for_completion=False
            )

            project_id = result.project_id if hasattr(result, "project_id") else str(result)
            active[project_id] = (section_name, stub_path)
            log(f"  ✓ Submitted {section_name}")

        except Exception as e:
            log(f"  ✗ Submit failed {section_name}: {e}", "ERROR")
            if "5 projects in progress" in str(e):
                log("    Hit concurrent limit, waiting...")
                await asyncio.sleep(60)

    if not active:
        return []

    # Wait for completion
    integrated = []
    max_wait = 7200  # 2 hours max
    waited = 0

    while active and waited < max_wait:
        await asyncio.sleep(POLL_INTERVAL)
        waited += POLL_INTERVAL

        result = await aristotlelib.Project.list_projects()
        projects = result[0] if isinstance(result, tuple) else result
        projects_by_id = {p.project_id: p for p in projects}

        completed = []
        for proj_id, (section_name, stub_path) in list(active.items()):
            if proj_id not in projects_by_id:
                completed.append(proj_id)
                continue

            proj = projects_by_id[proj_id]
            status = proj.status.name

            if status == "COMPLETE":
                try:
                    solution = await proj.get_solution()
                    if solution and solution.exists():
                        output_file = TAXCODE_DIR / f"{section_name}_aristotle_output.lean"
                        shutil.copy(solution, output_file)
                        log(f"  ✅ Integrated {section_name}")
                        integrated.append(section_name)
                except Exception as e:
                    log(f"  ✗ Integration failed {section_name}: {e}", "ERROR")
                completed.append(proj_id)

            elif status == "FAILED":
                log(f"  ✗ Failed {section_name}", "ERROR")
                completed.append(proj_id)

        for proj_id in completed:
            del active[proj_id]

        if active:
            log(f"  ⏳ Waiting for {len(active)} projects...")

    return integrated


async def submit_gap_to_aristotle(gap_key: str, dry_run: bool = False) -> int:
    """Submit all stubs for a gap to Aristotle."""
    analysis = analyze_gaps()
    need_aristotle = analysis[gap_key]["need_aristotle"]

    if not need_aristotle:
        log(f"No sections need Aristotle submission for {gap_key}")
        return 0

    stubs = [TAXCODE_DIR / f"Section{s}.lean" for s in need_aristotle]
    stubs = [s for s in stubs if s.exists()]

    log(f"Submitting {len(stubs)} sections to Aristotle for {gap_key}")

    if dry_run:
        log(f"DRY RUN: Would submit {[s.stem for s in stubs[:10]]}...")
        return len(stubs)

    aristotlelib.set_api_key(os.getenv("ARISTOTLE_API_KEY"))

    total_integrated = 0
    for i in range(0, len(stubs), BATCH_SIZE):
        batch = stubs[i:i + BATCH_SIZE]
        batch_num = i // BATCH_SIZE + 1
        total_batches = (len(stubs) + BATCH_SIZE - 1) // BATCH_SIZE

        log(f"\n--- Batch {batch_num}/{total_batches} ({len(batch)} files) ---")

        integrated = await submit_batch_to_aristotle(batch)
        total_integrated += len(integrated)

        log(f"Batch complete: {len(integrated)} integrated")

        if i + BATCH_SIZE < len(stubs):
            await asyncio.sleep(10)

    log(f"Aristotle submission complete for {gap_key}: {total_integrated}/{len(stubs)}")
    return total_integrated


# ============================================================================
# MAIN COMMANDS
# ============================================================================

def cmd_status():
    """Show current status of all gaps."""
    analysis = analyze_gaps()
    print_analysis(analysis)


def cmd_plan():
    """Show detailed execution plan."""
    analysis = analyze_gaps()
    print_analysis(analysis)

    print("\n" + "=" * 70)
    print("EXECUTION PLAN")
    print("=" * 70)

    for key in ["partnerships", "trusts", "natural_resources", "fica"]:
        gap = GAPS[key]
        a = analysis[key]

        print(f"\nPhase: {gap['name']}")
        print(f"  1. Scrape: {len(a['need_scrape'])} sections from Cornell Law (~{len(a['need_scrape'])}s)")
        print(f"  2. Generate: {len(a['need_stub'])} stubs via Claude (~{len(a['need_stub']) * 3}s)")
        print(f"  3. Submit: {len(a['need_aristotle'])} to Aristotle")
        print(f"     └─ {(len(a['need_aristotle']) + BATCH_SIZE - 1) // BATCH_SIZE} batches of {BATCH_SIZE}")

    print("\n" + "=" * 70)
    print("COMMANDS")
    print("=" * 70)
    print("""
python scripts/gap_submission_plan.py status           # Show current status
python scripts/gap_submission_plan.py plan             # Show this plan
python scripts/gap_submission_plan.py scrape GAPKEY    # Scrape sections
python scripts/gap_submission_plan.py generate GAPKEY  # Generate stubs
python scripts/gap_submission_plan.py submit GAPKEY    # Submit to Aristotle
python scripts/gap_submission_plan.py run GAPKEY       # Run full pipeline

GAPKEY: partnerships | trusts | natural_resources | fica | all
    """)


def cmd_scrape(gap_key: str, dry_run: bool = False):
    """Scrape sections for a gap."""
    if gap_key == "all":
        for key in GAPS:
            scrape_gap(key, dry_run)
    else:
        scrape_gap(gap_key, dry_run)


def cmd_generate(gap_key: str, dry_run: bool = False):
    """Generate stubs for a gap."""
    if gap_key == "all":
        for key in GAPS:
            generate_stubs_for_gap(key, dry_run)
    else:
        generate_stubs_for_gap(gap_key, dry_run)


def cmd_submit(gap_key: str, dry_run: bool = False):
    """Submit stubs to Aristotle."""
    async def run():
        if gap_key == "all":
            for key in GAPS:
                await submit_gap_to_aristotle(key, dry_run)
        else:
            await submit_gap_to_aristotle(gap_key, dry_run)

    asyncio.run(run())


def cmd_run(gap_key: str, dry_run: bool = False):
    """Run full pipeline for a gap."""
    gaps_to_process = list(GAPS.keys()) if gap_key == "all" else [gap_key]

    for key in gaps_to_process:
        log(f"\n{'='*60}")
        log(f"PROCESSING GAP: {GAPS[key]['name']}")
        log(f"{'='*60}")

        # Step 1: Scrape
        scrape_gap(key, dry_run)

        # Step 2: Generate
        generate_stubs_for_gap(key, dry_run)

        # Step 3: Submit
        asyncio.run(submit_gap_to_aristotle(key, dry_run))


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Gap Submission Plan")
    parser.add_argument("command", choices=["status", "plan", "scrape", "generate", "submit", "run"])
    parser.add_argument("gap", nargs="?", default="all",
                        choices=["partnerships", "trusts", "natural_resources", "fica", "all"])
    parser.add_argument("--dry-run", action="store_true", help="Show what would be done")

    args = parser.parse_args()

    if args.command == "status":
        cmd_status()
    elif args.command == "plan":
        cmd_plan()
    elif args.command == "scrape":
        cmd_scrape(args.gap, args.dry_run)
    elif args.command == "generate":
        cmd_generate(args.gap, args.dry_run)
    elif args.command == "submit":
        cmd_submit(args.gap, args.dry_run)
    elif args.command == "run":
        cmd_run(args.gap, args.dry_run)
