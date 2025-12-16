#!/usr/bin/env python3
"""
Process only the remaining 75 stub files through Aristotle.
Submits in batches of 5, waits for completion, then continues.
"""
import asyncio
import os
import re
import shutil
from pathlib import Path
from datetime import datetime
import aristotlelib

# Common definitions to inject (replacing Common.Basic import)
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

LOG_FILE = Path('/tmp/aristotle_stubs.log')
TAXCODE_DIR = Path(__file__).parent.parent / 'src' / 'TaxCode'
BATCH_SIZE = 5
POLL_INTERVAL = 60  # seconds
MAX_FILE_SIZE = 45000  # 45KB max to avoid URL too long errors

def log(msg):
    line = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
    print(line)
    with open(LOG_FILE, 'a') as f:
        f.write(line + '\n')

def get_remaining_stubs():
    """Get list of stub files that need processing."""
    stubs = []
    skipped_large = []
    for f in sorted(TAXCODE_DIR.glob('Section*.lean')):
        if any(x in f.name for x in ['_backup', '_aristotle', '_output']):
            continue
        content = f.read_text()
        if 'TODO: Add type definitions' in content:
            size = f.stat().st_size
            if size > MAX_FILE_SIZE:
                skipped_large.append((f.name, size))
            else:
                stubs.append(f)

    if skipped_large:
        log(f"Skipping {len(skipped_large)} oversized files:")
        for name, size in skipped_large[:10]:
            log(f"  {name}: {size // 1024}KB")
        if len(skipped_large) > 10:
            log(f"  ... and {len(skipped_large) - 10} more")

    return stubs

def prepare_content(stub_path):
    """Prepare file content for Aristotle submission."""
    content = stub_path.read_text()

    # Replace Common.Basic import with inline definitions
    content = re.sub(
        r'import\s+(TaxCode\.)?Common\.Basic\s*\n?',
        f'\nimport Mathlib\n{COMMON_DEFS}\n',
        content
    )

    # Ensure Mathlib is imported
    if 'import Mathlib' not in content:
        content = 'import Mathlib\n' + content

    return content

def extract_section_num(content):
    """Extract section number from content."""
    # Try to find "IRC Section XXX" or "§XXX"
    match = re.search(r'IRC (?:Section |§)(\d+[A-Za-z]*)', content)
    if match:
        return match.group(1)

    # Try "26 U.S. Code § XXX"
    match = re.search(r'26 U\.S\. Code § (\d+[A-Za-z]*)', content)
    if match:
        return match.group(1)

    return None

async def submit_and_wait(stubs_batch):
    """Submit a batch and wait for all to complete."""
    active = {}  # project_id -> (section_name, stub_path)

    # Submit batch
    for stub_path in stubs_batch:
        section_name = stub_path.stem
        content = prepare_content(stub_path)

        try:
            result = await aristotlelib.Project.prove_from_file(
                input_content=content,
                wait_for_completion=False
            )
            # Handle both string (project_id) and Project object returns
            if isinstance(result, str):
                project_id = result
            else:
                project_id = result.project_id if hasattr(result, 'project_id') else str(result)
            active[project_id] = (section_name, stub_path)
            log(f"✓ Submitted {section_name}")
        except Exception as e:
            log(f"✗ Submit failed {section_name}: {e}")
            # If we hit the limit, wait and retry
            if "5 projects in progress" in str(e):
                log("  Hit limit, waiting...")
                await asyncio.sleep(30)

    if not active:
        return []

    # Wait for all to complete
    integrated = []
    max_wait = 3600  # 1 hour max wait
    waited = 0

    while active and waited < max_wait:
        await asyncio.sleep(POLL_INTERVAL)
        waited += POLL_INTERVAL

        # Check status
        result = await aristotlelib.Project.list_projects()
        if isinstance(result, tuple):
            projects, _ = result
        else:
            projects = result

        projects_by_id = {p.project_id: p for p in projects}

        completed = []
        for proj_id, (section_name, stub_path) in list(active.items()):
            if proj_id not in projects_by_id:
                log(f"⚠ {section_name} not found in queue")
                completed.append(proj_id)
                continue

            proj = projects_by_id[proj_id]
            status = proj.status.name

            if status == 'COMPLETE':
                try:
                    solution = await proj.get_solution()
                    if solution and solution.exists():
                        output_file = TAXCODE_DIR / f"{section_name}_aristotle_output.lean"
                        shutil.copy(solution, output_file)
                        log(f"✅ Integrated {section_name}")
                        integrated.append(section_name)
                except Exception as e:
                    log(f"✗ Integration failed {section_name}: {e}")
                completed.append(proj_id)

            elif status == 'FAILED':
                log(f"✗ Failed {section_name}")
                completed.append(proj_id)

            elif status in ('IN_PROGRESS', 'QUEUED'):
                pct = proj.percent_complete or 0
                log(f"  {section_name}: {status} ({pct}%)")

        for proj_id in completed:
            del active[proj_id]

        if active:
            remaining = len(active)
            log(f"📊 Waiting for {remaining} projects...")

    if active:
        log(f"⚠ Timeout waiting for {len(active)} projects")

    return integrated

async def main():
    log("=" * 50)
    log("Starting targeted stub processor")
    log("=" * 50)

    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    # Get remaining stubs
    stubs = get_remaining_stubs()
    log(f"Found {len(stubs)} remaining stubs")

    if not stubs:
        log("No stubs to process!")
        return

    total_integrated = 0

    # Process in batches
    for i in range(0, len(stubs), BATCH_SIZE):
        batch = stubs[i:i + BATCH_SIZE]
        batch_num = i // BATCH_SIZE + 1
        total_batches = (len(stubs) + BATCH_SIZE - 1) // BATCH_SIZE

        log(f"\n--- Batch {batch_num}/{total_batches} ({len(batch)} files) ---")

        integrated = await submit_and_wait(batch)
        total_integrated += len(integrated)

        log(f"Batch complete: {len(integrated)} integrated")
        log(f"Total progress: {total_integrated}/{len(stubs)}")

        # Brief pause between batches
        if i + BATCH_SIZE < len(stubs):
            await asyncio.sleep(5)

    log("\n" + "=" * 50)
    log(f"DONE: {total_integrated}/{len(stubs)} stubs integrated")
    log("=" * 50)

if __name__ == '__main__':
    asyncio.run(main())
