#!/usr/bin/env python3
"""
Continuous Aristotle processor - maximizes throughput within API limits.
Runs until all stubs are processed or manually stopped.
"""

import aristotlelib
import os
import asyncio
import json
import re
from pathlib import Path
from datetime import datetime

COMMON_BASIC = '''set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
noncomputable section
def Currency := Int
structure TaxYear where year : Nat; h_valid : year ≥ 1913; deriving DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited
'''

MAX_LINES = 3000
MAX_CONCURRENT = 5
POLL_INTERVAL = 30  # seconds

# Track active projects
active_projects = {}  # section -> project_id

def prepare_stub(filepath):
    content = filepath.read_text()
    content = re.sub(r'import\s+Common\.Basic\s*\n?', 'import Mathlib\n', content)
    if 'import Mathlib' in content and 'def Currency' not in content:
        content = content.replace('import Mathlib\n', f'import Mathlib\n{COMMON_BASIC}\n')
    return re.sub(r'#eval\s+.*\n?', '', content)

def get_integrated():
    integrated = set()
    for f in Path('src/TaxCode').glob('Section*_backup.lean'):
        try:
            integrated.add(int(f.name.replace('Section','').replace('_backup.lean','')))
        except:
            pass
    return integrated

def get_stub_sections():
    with open('data/triage_results.json') as f:
        return sorted([f['section'] for f in json.load(f)['files'] if f['category'] == 'STUB'])

async def check_and_integrate(section, project_id):
    """Check if a project is complete and integrate if so."""
    try:
        project = await aristotlelib.Project.from_id(project_id)
        await project.refresh()

        if project.status.name == 'COMPLETE':
            solution_path = await project.get_solution()
            if solution_path and Path(solution_path).exists():
                solution = Path(solution_path).read_text()

                # Save output
                output_file = Path(f'src/TaxCode/Section{section}_aristotle_output.lean')
                output_file.write_text(solution)

                # Backup and replace main file
                main_file = Path(f'src/TaxCode/Section{section}.lean')
                backup_file = Path(f'src/TaxCode/Section{section}_backup.lean')

                if main_file.exists() and not backup_file.exists():
                    backup_file.write_text(main_file.read_text())
                    main_file.write_text(solution)

                sorry_count = solution.count('sorry')
                return True, sorry_count

        return False, None
    except Exception as e:
        return False, None

async def submit_section(section):
    """Submit a section for processing."""
    filepath = Path(f'src/TaxCode/Section{section}.lean')
    if not filepath.exists():
        return None

    content = prepare_stub(filepath)
    if len(content.splitlines()) > MAX_LINES:
        return None

    try:
        project_id = await aristotlelib.Project.prove_from_file(
            input_content=content,
            wait_for_completion=False
        )
        return project_id
    except Exception as e:
        if "5 projects" in str(e):
            return "LIMIT"
        return None

async def run_continuous():
    """Main processing loop."""
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    stubs = get_stub_sections()
    total_processed = 0
    total_zero_sorry = 0

    print(f"=" * 60)
    print(f"CONTINUOUS ARISTOTLE PROCESSOR")
    print(f"=" * 60)
    print(f"Total stub sections: {len(stubs)}")
    print(f"Max concurrent: {MAX_CONCURRENT}")
    print(f"Poll interval: {POLL_INTERVAL}s")
    print(f"=" * 60)

    while True:
        integrated = get_integrated()
        remaining = [s for s in stubs if s not in integrated and s not in active_projects]

        # Check active projects
        completed_sections = []
        for section, project_id in list(active_projects.items()):
            done, sorry_count = await check_and_integrate(section, project_id)
            if done:
                completed_sections.append(section)
                total_processed += 1
                if sorry_count == 0:
                    total_zero_sorry += 1
                print(f"  ✅ Section {section}: {sorry_count} sorries")

        # Remove completed from active
        for section in completed_sections:
            del active_projects[section]

        # Submit new sections up to limit
        slots_available = MAX_CONCURRENT - len(active_projects)

        for section in remaining[:slots_available]:
            result = await submit_section(section)
            if result == "LIMIT":
                break
            elif result:
                active_projects[section] = result
                print(f"  📤 Section {section} submitted")
            await asyncio.sleep(1)

        # Status update
        now = datetime.now().strftime("%H:%M:%S")
        print(f"\n[{now}] Integrated: {len(integrated)} | Active: {len(active_projects)} | Remaining: {len(remaining)} | Success rate: {total_zero_sorry}/{total_processed}")

        # Check if done
        if not active_projects and not remaining:
            print(f"\n🎉 ALL DONE! Processed {total_processed} sections")
            break

        await asyncio.sleep(POLL_INTERVAL)

if __name__ == '__main__':
    asyncio.run(run_continuous())
