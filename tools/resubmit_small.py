#!/usr/bin/env python3
"""
Targeted resubmission for small stub files (<10KB) that should succeed.
These are the 15 sections that are small enough to not hit size limits.
"""

import os
import sys
import asyncio
from pathlib import Path
from datetime import datetime

# Small sections that should work
SMALL_SECTIONS = ['515', '586', '165', '170', '302', '561', '591', '502', '594', '385', '46', '892', '472', '473', '305']

SRC_DIR = Path(__file__).parent.parent / 'src' / 'TaxCode'

HEADER = '''import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single | MarriedFilingJointly | MarriedFilingSeparately
  | HeadOfHousehold | QualifyingWidower | Estate | Trust
  deriving Repr, DecidableEq, Inhabited

instance : Add Currency := inferInstanceAs (Add Int)
instance : Sub Currency := inferInstanceAs (Sub Int)
instance : Mul Currency := inferInstanceAs (Mul Int)
instance : Div Currency := inferInstanceAs (Div Int)
instance : LE Currency := inferInstanceAs (LE Int)
instance : LT Currency := inferInstanceAs (LT Int)
instance : DecidableRel ((· ≤ ·) : Currency → Currency → Prop) := inferInstanceAs (DecidableRel (· ≤ · : Int → Int → Prop))
instance (n : Nat) [OfNat Int n] : OfNat Currency n := inferInstanceAs (OfNat Int n)
instance : Repr Currency := inferInstanceAs (Repr Int)
instance : LinearOrder Currency := inferInstanceAs (LinearOrder Int)
instance : Inhabited Currency := inferInstanceAs (Inhabited Int)

'''

def log(msg):
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)

def prepare_file(section):
    """Prepare section file for Aristotle."""
    import re
    filepath = SRC_DIR / f'Section{section}.lean'
    content = filepath.read_text()

    # Clean content
    content = re.sub(r'import\s+\S+\s*\n?', '', content)
    content = re.sub(r'#eval\s+.*\n?', '', content)
    content = re.sub(r'namespace\s+Common\.Basic[\s\S]*?end\s+Common\.Basic\n?', '', content)
    content = re.sub(r'def\s+Currency\s*:?=\s*Int\s*\n?', '', content)

    return HEADER + content.strip()

async def submit_one(section):
    """Submit a single section to Aristotle."""
    import aristotlelib

    content = prepare_file(section)
    log(f"Submitting Section{section} ({len(content)/1024:.1f}KB)...")

    try:
        project = await aristotlelib.Project.create(
            problem=content,
            is_lean_file=True,
            informal_prefix=f"Complete the Lean 4 formalization of IRC Section {section}. Fill in all sorry placeholders with working proofs."
        )
        log(f"  ✓ Section{section} -> {str(project.id)[:8]}...")
        return str(project.id)
    except Exception as e:
        log(f"  ✗ Section{section}: {e}")
        return None

async def check_status():
    """Check status of small sections."""
    import re

    log("=" * 50)
    log("SMALL SECTION STATUS")
    log("=" * 50)

    still_stub = []
    complete = []

    for sec in SMALL_SECTIONS:
        filepath = SRC_DIR / f'Section{sec}.lean'
        if filepath.exists():
            content = filepath.read_text()
            size_kb = filepath.stat().st_size / 1024
            is_stub = '-- TODO: Add type definitions' in content

            if is_stub:
                still_stub.append((sec, size_kb))
            else:
                complete.append((sec, size_kb))

    log(f"Complete: {len(complete)}")
    log(f"Still stubs: {len(still_stub)}")

    if still_stub:
        log("\nStill needing work:")
        for sec, size in sorted(still_stub, key=lambda x: x[1]):
            log(f"  Section{sec}: {size:.1f}KB")

    return still_stub

async def main():
    import aristotlelib

    api_key = os.getenv('ARISTOTLE_API_KEY')
    if not api_key:
        print("ERROR: ARISTOTLE_API_KEY not set")
        sys.exit(1)

    aristotlelib.set_api_key(api_key)

    # Check current status
    still_stub = await check_status()

    if not still_stub:
        log("\nAll small sections complete!")
        return

    # Ask before submitting
    print(f"\nSubmit {len(still_stub)} sections to Aristotle? [y/N]: ", end='')
    response = input().strip().lower()

    if response != 'y':
        log("Aborted.")
        return

    # Submit in batches of 5
    log("\nSubmitting...")
    for i, (sec, _) in enumerate(still_stub):
        if i > 0 and i % 5 == 0:
            log("Waiting 60s for rate limit...")
            await asyncio.sleep(60)

        await submit_one(sec)
        await asyncio.sleep(3)

    log("\nSubmissions complete. Check Aristotle dashboard for results.")

if __name__ == '__main__':
    asyncio.run(main())
