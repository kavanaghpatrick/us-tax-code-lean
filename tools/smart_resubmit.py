#!/usr/bin/env python3
"""
Smart Aristotle Resubmission System

Handles different resubmission types based on Grok triage analysis:
1. LOCAL_FIX: Apply simple tactic fixes without Aristotle
2. ARISTOTLE_PROOF_COMPLETE: Resubmit for proof completion only
3. TRUNCATE_RESUBMIT: Truncate content and resubmit
4. FULL_FORMALIZATION: Submit stubs for full processing

Usage:
    python3 smart_resubmit.py --local-fixes     # Fix simple sorries locally
    python3 smart_resubmit.py --proof-complete  # Submit for proof completion
    python3 smart_resubmit.py --resubmit-failed # Retry failed sections
    python3 smart_resubmit.py --batch N         # Process N stub sections
"""

import argparse
import asyncio
import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional

PROJECT_ROOT = Path(__file__).parent.parent
TAXCODE_DIR = PROJECT_ROOT / "src" / "TaxCode"
QUEUE_FILE = PROJECT_ROOT / "data" / "prioritized_queue.json"
STATUS_FILE = PROJECT_ROOT / "data" / "resubmission_status.json"

# Try to import aristotlelib
try:
    import aristotlelib
    HAS_ARISTOTLE = True
except ImportError:
    HAS_ARISTOTLE = False
    print("WARNING: aristotlelib not installed, Aristotle submissions disabled")


def load_queue() -> Dict:
    """Load the prioritized queue."""
    with open(QUEUE_FILE) as f:
        return json.load(f)


def load_status() -> Dict:
    """Load submission status."""
    if STATUS_FILE.exists():
        with open(STATUS_FILE) as f:
            return json.load(f)
    return {"submitted": {}, "completed": {}, "failed": {}}


def save_status(status: Dict):
    """Save submission status."""
    with open(STATUS_FILE, 'w') as f:
        json.dump(status, f, indent=2)


def fix_sorry_locally(section: int, tactics: str) -> bool:
    """
    Attempt to fix simple sorry proofs locally.
    Returns True if successful.
    """
    filepath = TAXCODE_DIR / f"Section{section}.lean"
    if not filepath.exists():
        print(f"  File not found: {filepath}")
        return False

    content = filepath.read_text()
    original_sorries = content.count('sorry')

    if original_sorries == 0:
        print(f"  Section {section}: No sorries to fix")
        return True

    # Common tactic replacements based on proof context
    fixes = [
        # Simple equality/decidability
        (r'(\s+)sorry(\s*--.*decide)', r'\1decide\2'),
        # Non-negativity proofs
        (r'by\s+sorry\s*--.*simp', 'by simp'),
        (r'by\s+sorry\s*--.*omega', 'by omega'),
        # Reflexivity
        (r'by\s+sorry\s*--.*rfl', 'by rfl'),
        # Native decide
        (r'by\s+sorry\s*--.*native_decide', 'by native_decide'),
    ]

    new_content = content
    for pattern, replacement in fixes:
        new_content = re.sub(pattern, replacement, new_content)

    new_sorries = new_content.count('sorry')
    fixed = original_sorries - new_sorries

    if fixed > 0:
        filepath.write_text(new_content)
        print(f"  Section {section}: Fixed {fixed}/{original_sorries} sorries")
        return new_sorries == 0
    else:
        print(f"  Section {section}: Could not auto-fix {original_sorries} sorries")
        print(f"    Suggested tactics: {tactics}")
        return False


def truncate_for_submission(section: int, max_lines: int = 500) -> str:
    """
    Truncate a large file for Aristotle submission.
    Keep structure, remove verbose legal text.
    """
    filepath = TAXCODE_DIR / f"Section{section}.lean"
    content = filepath.read_text()
    lines = content.split('\n')

    if len(lines) <= max_lines:
        return content

    # Strategy: Keep imports, structure defs, remove long comments/legal text
    output_lines = []
    in_block_comment = False
    legal_text_lines = 0

    for line in lines:
        # Track block comments
        if '/-' in line and '-/' not in line:
            in_block_comment = True
        if '-/' in line:
            in_block_comment = False
            continue

        # Skip lines in block comments (legal text)
        if in_block_comment:
            legal_text_lines += 1
            if legal_text_lines <= 20:  # Keep first 20 lines of legal text
                output_lines.append(line)
            elif legal_text_lines == 21:
                output_lines.append("  [Legal text truncated for Aristotle submission]")
            continue

        # Keep code lines
        output_lines.append(line)

        if len(output_lines) >= max_lines:
            output_lines.append("\n-- [File truncated for Aristotle submission]")
            break

    return '\n'.join(output_lines)


async def submit_to_aristotle(section: int, content: str, mode: str = "formalize") -> Optional[str]:
    """
    Submit content to Aristotle API.
    Returns project_id if successful.
    """
    if not HAS_ARISTOTLE:
        print(f"  Cannot submit Section {section}: aristotlelib not installed")
        return None

    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        print("  ERROR: ARISTOTLE_API_KEY not set")
        return None

    aristotlelib.set_api_key(api_key)

    try:
        if mode == "proof_complete":
            # Submit for proof completion
            project = await aristotlelib.Project.prove_from_code(
                content,
                file_name=f"Section{section}.lean"
            )
        else:
            # Submit for full formalization
            project = await aristotlelib.Project.prove_from_code(
                content,
                file_name=f"Section{section}.lean"
            )

        print(f"  Section {section}: Submitted as project {project.id}")
        return str(project.id)

    except Exception as e:
        print(f"  Section {section}: Submission failed - {e}")
        return None


def run_local_fixes():
    """Run local fixes for simple sorry cases."""
    queue = load_queue()
    local_fixes = queue.get("priority_1_local_fixes", {}).get("sections", [])

    print("="*60)
    print("LOCAL FIXES (no Aristotle needed)")
    print("="*60)

    fixed = 0
    for item in local_fixes:
        if item.get("action") == "SKIP":
            print(f"  Section {item['section']}: SKIPPED - {item.get('reason', '')}")
            continue

        if fix_sorry_locally(item["section"], item.get("tactic", "")):
            fixed += 1

    print(f"\nFixed {fixed}/{len(local_fixes)} sections locally")


async def run_proof_complete():
    """Submit sections for Aristotle proof completion."""
    queue = load_queue()
    status = load_status()

    sections = queue.get("priority_2_aristotle_proof_complete", {}).get("sections", [])

    print("="*60)
    print("ARISTOTLE PROOF COMPLETION")
    print("="*60)

    for item in sections:
        section = item["section"]

        if str(section) in status.get("submitted", {}):
            print(f"  Section {section}: Already submitted")
            continue

        filepath = TAXCODE_DIR / f"Section{section}.lean"
        content = filepath.read_text()

        project_id = await submit_to_aristotle(section, content, "proof_complete")

        if project_id:
            status.setdefault("submitted", {})[str(section)] = {
                "project_id": project_id,
                "submitted_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "mode": "proof_complete"
            }
            save_status(status)


async def run_resubmit_failed():
    """Retry previously failed submissions."""
    queue = load_queue()
    status = load_status()

    sections = queue.get("priority_3_aristotle_resubmit", {}).get("sections", [])

    print("="*60)
    print("RESUBMIT FAILED SECTIONS")
    print("="*60)

    for item in sections:
        section = item["section"]
        action = item["action"]

        if str(section) in status.get("submitted", {}):
            print(f"  Section {section}: Already resubmitted")
            continue

        if action == "TRUNCATE_RESUBMIT":
            print(f"  Section {section}: Truncating from {item['lines']} lines...")
            content = truncate_for_submission(section)
        else:
            filepath = TAXCODE_DIR / f"Section{section}.lean"
            content = filepath.read_text()

        project_id = await submit_to_aristotle(section, content, "formalize")

        if project_id:
            status.setdefault("submitted", {})[str(section)] = {
                "project_id": project_id,
                "submitted_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "mode": "resubmit",
                "action": action
            }
            save_status(status)

        # Rate limit
        await asyncio.sleep(2)


async def run_batch(batch_size: int):
    """Process a batch of stub sections."""
    queue = load_queue()
    status = load_status()
    triage_file = PROJECT_ROOT / "data" / "triage_results.json"

    if not triage_file.exists():
        print("ERROR: Run grok_triage.py first to identify stub sections")
        return

    with open(triage_file) as f:
        triage = json.load(f)

    stub_files = triage.get("categories", {}).get("STUB", [])

    print("="*60)
    print(f"BATCH PROCESSING ({batch_size} sections)")
    print("="*60)
    print(f"Total stubs: {len(stub_files)}")

    # Sort by priority (section number as proxy)
    stub_files.sort(key=lambda x: int(re.search(r'Section(\d+)', x).group(1)))

    submitted = 0
    for filename in stub_files:
        if submitted >= batch_size:
            break

        match = re.search(r'Section(\d+)', filename)
        if not match:
            continue

        section = int(match.group(1))

        if str(section) in status.get("submitted", {}):
            continue

        filepath = TAXCODE_DIR / filename
        content = filepath.read_text()

        project_id = await submit_to_aristotle(section, content, "formalize")

        if project_id:
            status.setdefault("submitted", {})[str(section)] = {
                "project_id": project_id,
                "submitted_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "mode": "full_formalization"
            }
            save_status(status)
            submitted += 1
            print(f"  Progress: {submitted}/{batch_size}")

        # Rate limit - Aristotle has 5 concurrent project limit
        await asyncio.sleep(5)

    print(f"\nSubmitted {submitted} sections")


def main():
    parser = argparse.ArgumentParser(description="Smart Aristotle resubmission")
    parser.add_argument("--local-fixes", action="store_true",
                        help="Apply local sorry fixes")
    parser.add_argument("--proof-complete", action="store_true",
                        help="Submit for proof completion")
    parser.add_argument("--resubmit-failed", action="store_true",
                        help="Retry failed submissions")
    parser.add_argument("--batch", type=int, default=0,
                        help="Process N stub sections")
    parser.add_argument("--status", action="store_true",
                        help="Show current status")

    args = parser.parse_args()

    if args.status:
        status = load_status()
        print(f"Submitted: {len(status.get('submitted', {}))}")
        print(f"Completed: {len(status.get('completed', {}))}")
        print(f"Failed: {len(status.get('failed', {}))}")
        return

    if args.local_fixes:
        run_local_fixes()
    elif args.proof_complete:
        asyncio.run(run_proof_complete())
    elif args.resubmit_failed:
        asyncio.run(run_resubmit_failed())
    elif args.batch > 0:
        asyncio.run(run_batch(args.batch))
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
