#!/usr/bin/env python3
"""
Process oversized stub files by truncating editorial/historical content.
"""
import asyncio
import os
import re
import shutil
from pathlib import Path
from datetime import datetime
import aristotlelib

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

LOG_FILE = Path('/tmp/aristotle_oversized.log')
TAXCODE_DIR = Path(__file__).parent.parent / 'src' / 'TaxCode'
MAX_FILE_SIZE = 45000  # Target size after truncation
MAX_LINES = 1200  # Maximum lines to keep if still too large
BATCH_SIZE = 5
POLL_INTERVAL = 60

def log(msg):
    line = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
    print(line)
    with open(LOG_FILE, 'a') as f:
        f.write(line + '\n')

def get_oversized_stubs():
    """Get list of oversized stub files."""
    stubs = []
    for f in sorted(TAXCODE_DIR.glob('Section*.lean')):
        if any(x in f.name for x in ['_backup', '_aristotle', '_output']):
            continue
        content = f.read_text()
        if 'TODO: Add type definitions' in content:
            size = f.stat().st_size
            if size > MAX_FILE_SIZE:
                stubs.append(f)
    return stubs

def truncate_content(content):
    """Truncate content by removing editorial notes and history."""
    lines = content.split('\n')

    # Find cutoff points
    cutoff_patterns = [
        r'^\s*Editorial Notes',
        r'^\s*Amendments$',
        r'^\s*Statutory Notes',
        r'^\s*Historical and Revision Notes',
        r'^\s*References in Text',
    ]

    cutoff_line = len(lines)
    for i, line in enumerate(lines):
        for pattern in cutoff_patterns:
            if re.match(pattern, line):
                cutoff_line = min(cutoff_line, i)
                break

    # Take lines up to cutoff
    truncated_lines = lines[:cutoff_line]

    # If still too many lines, take first MAX_LINES
    if len(truncated_lines) > MAX_LINES:
        truncated_lines = truncated_lines[:MAX_LINES]
        truncated_lines.append('\n-- [Content truncated for size]')

    # Ensure TODO markers are preserved at end
    if not any('TODO:' in line for line in truncated_lines[-10:]):
        truncated_lines.extend([
            '',
            '-- TODO: Add type definitions',
            '-- TODO: Add main functions',
            '-- TODO: Add theorems to prove'
        ])

    return '\n'.join(truncated_lines)

def prepare_content(stub_path):
    """Prepare truncated content for Aristotle submission."""
    content = stub_path.read_text()

    # Truncate editorial content
    content = truncate_content(content)

    # Replace Common.Basic import
    content = re.sub(
        r'import\s+(TaxCode\.)?Common\.Basic\s*\n?',
        f'\nimport Mathlib\n{COMMON_DEFS}\n',
        content
    )

    # Ensure Mathlib is imported
    if 'import Mathlib' not in content:
        content = 'import Mathlib\n' + content

    return content

async def submit_and_wait(stubs_batch):
    """Submit a batch and wait for completion."""
    active = {}

    for stub_path in stubs_batch:
        section_name = stub_path.stem
        content = prepare_content(stub_path)
        content_size = len(content.encode('utf-8'))

        if content_size > MAX_FILE_SIZE:
            log(f"⚠ {section_name} still too large after truncation ({content_size // 1024}KB)")
            continue

        try:
            result = await aristotlelib.Project.prove_from_file(
                input_content=content,
                wait_for_completion=False
            )
            project_id = result if isinstance(result, str) else (result.project_id if hasattr(result, 'project_id') else str(result))
            active[project_id] = (section_name, stub_path)
            log(f"✓ Submitted {section_name} ({content_size // 1024}KB)")
        except Exception as e:
            if "5 projects in progress" in str(e):
                log(f"  Hit limit, waiting...")
                await asyncio.sleep(30)
            else:
                log(f"✗ Submit failed {section_name}: {e}")

    if not active:
        return []

    # Wait for completion
    integrated = []
    max_wait = 3600
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
                log(f"⚠ {section_name} not found")
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
            log(f"📊 Waiting for {len(active)} projects...")

    return integrated

async def main():
    log("=" * 50)
    log("Processing oversized stub files")
    log("=" * 50)

    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    stubs = get_oversized_stubs()
    log(f"Found {len(stubs)} oversized stubs")

    if not stubs:
        log("No oversized stubs!")
        return

    # Show size analysis
    for stub in stubs[:5]:
        orig_size = stub.stat().st_size
        content = prepare_content(stub)
        new_size = len(content.encode('utf-8'))
        log(f"  {stub.name}: {orig_size//1024}KB -> {new_size//1024}KB")
    if len(stubs) > 5:
        log(f"  ... and {len(stubs) - 5} more")

    total_integrated = 0

    for i in range(0, len(stubs), BATCH_SIZE):
        batch = stubs[i:i + BATCH_SIZE]
        batch_num = i // BATCH_SIZE + 1
        total_batches = (len(stubs) + BATCH_SIZE - 1) // BATCH_SIZE

        log(f"\n--- Batch {batch_num}/{total_batches} ---")

        integrated = await submit_and_wait(batch)
        total_integrated += len(integrated)

        log(f"Batch complete: {len(integrated)} integrated")

        if i + BATCH_SIZE < len(stubs):
            await asyncio.sleep(5)

    log("\n" + "=" * 50)
    log(f"DONE: {total_integrated}/{len(stubs)} oversized stubs integrated")
    log("=" * 50)

if __name__ == '__main__':
    asyncio.run(main())
