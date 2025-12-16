#!/usr/bin/env python3
"""
Process the final 19 missing files.
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

LOG_FILE = Path('/tmp/aristotle_final19.log')
TAXCODE_DIR = Path(__file__).parent.parent / 'src' / 'TaxCode'
MAX_LINES = 600
BATCH_SIZE = 5
POLL_INTERVAL = 60

MISSING_FILES = [
    'Section125', 'Section1250', 'Section132', 'Section1401', 'Section1402',
    'Section141', 'Section143', 'Section305', 'Section402', 'Section420',
    'Section45', 'Section457', 'Section46', 'Section501', 'Section529',
    'Section594', 'Section832', 'Section852', 'Section897'
]

def log(msg):
    line = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
    print(line)
    with open(LOG_FILE, 'a') as f:
        f.write(line + '\n')

def aggressive_truncate(content):
    lines = content.split('\n')

    cutoff_patterns = [
        r'^\s*Editorial Notes',
        r'^\s*Amendments$',
        r'^\s*Statutory Notes',
        r'^\s*Historical',
        r'^\s*References in Text',
        r'^\s*\(\w+\.\s+\d+',
    ]

    cutoff_line = len(lines)
    for i, line in enumerate(lines):
        for pattern in cutoff_patterns:
            if re.match(pattern, line):
                cutoff_line = min(cutoff_line, i)
                break

    truncated_lines = lines[:cutoff_line]

    if len(truncated_lines) > MAX_LINES:
        truncated_lines = truncated_lines[:MAX_LINES]
        truncated_lines.append('')
        truncated_lines.append('-- [Content truncated]')

    truncated_lines.extend([
        '',
        '-- TODO: Add type definitions',
        '-- TODO: Add main functions',
        '-- TODO: Add theorems to prove'
    ])

    return '\n'.join(truncated_lines)

def prepare_content(stub_path):
    content = stub_path.read_text()
    content = aggressive_truncate(content)

    content = re.sub(
        r'import\s+(TaxCode\.)?Common\.Basic\s*\n?',
        f'\nimport Mathlib\n{COMMON_DEFS}\n',
        content
    )

    if 'import Mathlib' not in content:
        content = 'import Mathlib\n' + content

    return content

async def submit_and_wait(stubs_batch):
    active = {}

    for stub_path in stubs_batch:
        section_name = stub_path.stem
        content = prepare_content(stub_path)
        content_size = len(content.encode('utf-8'))

        log(f"  {section_name}: {content_size // 1024}KB")

        try:
            result = await aristotlelib.Project.prove_from_file(
                input_content=content,
                wait_for_completion=False
            )
            project_id = result if isinstance(result, str) else (result.project_id if hasattr(result, 'project_id') else str(result))
            active[project_id] = (section_name, stub_path)
            log(f"  ✓ Submitted {section_name}")
        except Exception as e:
            if "5 projects" in str(e):
                log(f"  Hit limit, waiting 60s...")
                await asyncio.sleep(60)
                # Retry once
                try:
                    result = await aristotlelib.Project.prove_from_file(
                        input_content=content,
                        wait_for_completion=False
                    )
                    project_id = result if isinstance(result, str) else str(result)
                    active[project_id] = (section_name, stub_path)
                    log(f"  ✓ Submitted {section_name} (retry)")
                except Exception as e2:
                    log(f"  ✗ Failed {section_name}: {e2}")
            else:
                log(f"  ✗ Failed {section_name}: {e}")

    if not active:
        return []

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
                log(f"  ⚠ {section_name} expired")
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
                        log(f"  ✅ {section_name}")
                        integrated.append(section_name)
                except Exception as e:
                    log(f"  ✗ Integration error {section_name}")
                completed.append(proj_id)
            elif status == 'FAILED':
                log(f"  ✗ {section_name} failed")
                completed.append(proj_id)
            elif status in ('IN_PROGRESS', 'QUEUED'):
                pct = proj.percent_complete or 0
                log(f"  {section_name}: {status} ({pct}%)")

        for proj_id in completed:
            del active[proj_id]

        if active:
            log(f"  📊 Waiting for {len(active)}...")

    return integrated

async def main():
    log("=" * 50)
    log("Processing final 19 missing files")
    log("=" * 50)

    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    stubs = []
    for name in MISSING_FILES:
        path = TAXCODE_DIR / f"{name}.lean"
        if path.exists():
            stubs.append(path)

    log(f"Found {len(stubs)} files")

    total_integrated = 0

    for i in range(0, len(stubs), BATCH_SIZE):
        batch = stubs[i:i + BATCH_SIZE]
        batch_num = i // BATCH_SIZE + 1
        total_batches = (len(stubs) + BATCH_SIZE - 1) // BATCH_SIZE

        log(f"\n--- Batch {batch_num}/{total_batches} ---")

        integrated = await submit_and_wait(batch)
        total_integrated += len(integrated)

        if i + BATCH_SIZE < len(stubs):
            await asyncio.sleep(5)

    log("\n" + "=" * 50)
    log(f"DONE: {total_integrated}/{len(stubs)} integrated")
    log("=" * 50)

if __name__ == '__main__':
    asyncio.run(main())
