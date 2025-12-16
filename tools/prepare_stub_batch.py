#!/usr/bin/env python3
"""
Prepare and submit stub files to Aristotle for formalization.

This script:
1. Reads stub files from triage results
2. Replaces 'import Common.Basic' with 'import Mathlib' + inline definitions
3. Submits them to Aristotle in batches
"""

import os
import json
import asyncio
import re
from pathlib import Path
from datetime import datetime

# Common.Basic inline definitions for Aristotle
COMMON_BASIC_INLINE = '''
set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

-- Common definitions for US Tax Code formalization
def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear
'''

def prepare_stub_for_aristotle(filepath: Path) -> str:
    """Prepare a stub file for Aristotle submission."""
    content = filepath.read_text()

    # Replace import Common.Basic with import Mathlib
    content = re.sub(r'import\s+Common\.Basic\s*\n?', 'import Mathlib\n', content)

    # If file uses Common.Basic types but doesn't have them defined, add them after import
    if 'import Mathlib' in content and 'def Currency' not in content:
        content = content.replace('import Mathlib\n', f'import Mathlib\n{COMMON_BASIC_INLINE}\n')

    # Remove #eval statements (Aristotle doesn't support them)
    content = re.sub(r'#eval\s+.*\n?', '', content)

    # Ensure there's a description for Aristotle
    section_match = re.search(r'Section\s*(\d+)', filepath.name)
    section_num = section_match.group(1) if section_match else "unknown"

    return content


async def submit_stub_batch(stubs: list, dry_run: bool = False):
    """Submit a batch of stub files to Aristotle."""
    import aristotlelib

    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    results = []

    for stub in stubs:
        section = stub['section']
        filepath = Path(f"src/TaxCode/Section{section}.lean")

        if not filepath.exists():
            print(f"  ⚠️  Section {section}: File not found")
            continue

        prepared_content = prepare_stub_for_aristotle(filepath)

        if dry_run:
            # Save to temp file for review
            temp_path = Path(f"temp/Section{section}_prepared.lean")
            temp_path.parent.mkdir(exist_ok=True)
            temp_path.write_text(prepared_content)
            print(f"  📝 Section {section}: Saved to {temp_path} ({len(prepared_content.splitlines())} lines)")
            results.append({'section': section, 'status': 'dry_run', 'path': str(temp_path)})
        else:
            try:
                # Check if file is too large (> 4000 lines)
                line_count = len(prepared_content.splitlines())
                if line_count > 4000:
                    print(f"  ⏭️  Section {section}: Skipped (too large: {line_count} lines)")
                    results.append({'section': section, 'status': 'skipped', 'reason': f'Too large: {line_count} lines'})
                    continue

                # Submit to Aristotle (async, don't wait for completion)
                # Returns project_id string when wait_for_completion=False
                project_id = await aristotlelib.Project.prove_from_file(
                    input_content=prepared_content,
                    wait_for_completion=False
                )

                print(f"  ✅ Section {section}: Submitted as {project_id}")
                results.append({
                    'section': section,
                    'project_id': project_id,
                    'submitted_at': datetime.now().isoformat(),
                    'status': 'submitted'
                })

                # Rate limit
                await asyncio.sleep(2)

            except Exception as e:
                print(f"  ❌ Section {section}: {e}")
                results.append({'section': section, 'status': 'error', 'error': str(e)})

    return results


async def main():
    import argparse

    parser = argparse.ArgumentParser(description='Prepare and submit stub files to Aristotle')
    parser.add_argument('--batch', type=int, default=5, help='Number of files to process')
    parser.add_argument('--priority', type=int, default=1, help='Min priority level to process')
    parser.add_argument('--dry-run', action='store_true', help='Prepare files but do not submit')
    parser.add_argument('--offset', type=int, default=0, help='Skip first N stubs')
    args = parser.parse_args()

    # Load triage results
    triage_path = Path('data/triage_results.json')
    if not triage_path.exists():
        print("❌ Run tools/grok_triage.py first")
        return

    with open(triage_path) as f:
        triage = json.load(f)

    # Get stub files sorted by priority
    stubs = [f for f in triage['files'] if f['category'] == 'STUB']
    stubs_sorted = sorted(stubs, key=lambda x: (x.get('priority', 99), x['section']))

    # Filter by priority
    stubs_filtered = [s for s in stubs_sorted if s.get('priority', 99) <= args.priority]

    # Apply offset and batch limit
    stubs_to_process = stubs_filtered[args.offset:args.offset + args.batch]

    print(f"=" * 60)
    print(f"STUB FILE BATCH SUBMISSION")
    print(f"=" * 60)
    print(f"Total stubs: {len(stubs)}")
    print(f"Filtered by priority <= {args.priority}: {len(stubs_filtered)}")
    print(f"Processing batch: {args.offset} to {args.offset + len(stubs_to_process)}")
    print(f"Dry run: {args.dry_run}")
    print()

    if not stubs_to_process:
        print("No stubs to process!")
        return

    results = await submit_stub_batch(stubs_to_process, dry_run=args.dry_run)

    # Save results
    results_path = Path('data/stub_submission_results.json')
    existing = []
    if results_path.exists():
        with open(results_path) as f:
            existing = json.load(f)

    existing.extend(results)

    with open(results_path, 'w') as f:
        json.dump(existing, f, indent=2)

    print()
    print(f"Results saved to {results_path}")


if __name__ == '__main__':
    asyncio.run(main())
