#!/usr/bin/env python3
"""
Sorry Remediation Queue for Aristotle INFORMAL Mode

Identifies sections with 'sorry' placeholders and resubmits them to Aristotle
with targeted prompts to complete the proofs.

Usage:
    python scripts/sorry_remediation_queue.py --scan           # Scan for sorries
    python scripts/sorry_remediation_queue.py --prepare        # Prepare _aristotle.lean files
    python scripts/sorry_remediation_queue.py --submit         # Submit to Aristotle
    python scripts/sorry_remediation_queue.py --status         # Check queue status
"""

import argparse
import asyncio
import json
import os
import re
import subprocess
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import Dict, List, Optional
import time

# Try to import aristotlelib (may not be available in all environments)
try:
    import aristotlelib
    ARISTOTLE_AVAILABLE = True
except ImportError:
    ARISTOTLE_AVAILABLE = False
    print("Warning: aristotlelib not available. Submission will be disabled.")


@dataclass
class SorryInfo:
    """Information about a sorry statement"""
    file: str
    section: str
    line: int
    theorem_name: str
    context: str  # surrounding lines for context


@dataclass
class RemediationTask:
    """A section queued for remediation"""
    section: str
    sorries: List[Dict]  # List of SorryInfo as dicts
    status: str  # pending, prepared, submitted, complete, failed
    project_id: Optional[str] = None
    submitted_at: Optional[str] = None
    completed_at: Optional[str] = None
    error: Optional[str] = None


class SorryRemediationQueue:
    """Queue manager for sorry remediation via Aristotle"""

    def __init__(self):
        self.project_root = Path(__file__).parent.parent
        self.taxcode_dir = self.project_root / 'src' / 'TaxCode'
        self.queue_file = self.project_root / 'data' / 'sorry_remediation_queue.json'
        self.queue: Dict[str, RemediationTask] = {}
        self.load_queue()

    def load_queue(self):
        """Load queue state from disk"""
        if self.queue_file.exists():
            try:
                with open(self.queue_file) as f:
                    data = json.load(f)
                    for section, task_data in data.get('tasks', {}).items():
                        self.queue[section] = RemediationTask(**task_data)
            except (json.JSONDecodeError, IOError) as e:
                print(f"Warning: Failed to load queue: {e}")

    def save_queue(self):
        """Save queue state to disk"""
        self.queue_file.parent.mkdir(parents=True, exist_ok=True)
        with open(self.queue_file, 'w') as f:
            json.dump({
                'tasks': {s: asdict(t) for s, t in self.queue.items()},
                'last_updated': time.strftime('%Y-%m-%d %H:%M:%S')
            }, f, indent=2)

    def scan_for_sorries(self) -> Dict[str, List[SorryInfo]]:
        """Scan all .lean files for sorry statements"""
        sorry_map: Dict[str, List[SorryInfo]] = {}

        for lean_file in self.taxcode_dir.glob('Section*.lean'):
            # Skip backup and aristotle files
            if '_backup' in lean_file.name or '_aristotle' in lean_file.name or '_output' in lean_file.name:
                continue

            content = lean_file.read_text()
            lines = content.split('\n')

            # Find lines with sorry
            for i, line in enumerate(lines):
                # Match actual sorry usage, not just comments mentioning it
                if re.search(r'\bsorry\b', line) and not line.strip().startswith('--'):
                    # Skip if it's just a comment about not using sorry
                    if 'without' in line.lower() and 'sorry' in line.lower():
                        continue

                    # Extract section number from filename
                    section_match = re.search(r'Section(\d+(?:_\d+)?)', lean_file.name)
                    if not section_match:
                        continue
                    section = section_match.group(1)

                    # Find the theorem/lemma name (search backwards)
                    theorem_name = "unknown"
                    for j in range(i, max(0, i-20), -1):
                        match = re.search(r'(?:theorem|lemma)\s+(\w+)', lines[j])
                        if match:
                            theorem_name = match.group(1)
                            break

                    # Get context (5 lines before and after)
                    start = max(0, i - 5)
                    end = min(len(lines), i + 6)
                    context = '\n'.join(lines[start:end])

                    sorry_info = SorryInfo(
                        file=lean_file.name,
                        section=section,
                        line=i + 1,
                        theorem_name=theorem_name,
                        context=context
                    )

                    if section not in sorry_map:
                        sorry_map[section] = []
                    sorry_map[section].append(sorry_info)

        return sorry_map

    def create_enhanced_prompt(self, section: str, sorries: List[SorryInfo]) -> str:
        """Create targeted prompt for Aristotle to complete specific proofs"""
        theorem_list = '\n'.join([f"  - {s.theorem_name} (line {s.line})" for s in sorries])

        # Categorize the sorry types for targeted guidance
        fold_proofs = [s for s in sorries if 'fold' in s.context.lower() or 'foldl' in s.context.lower()]
        arithmetic_proofs = [s for s in sorries if any(x in s.context.lower() for x in ['arithmetic', 'div', 'floor', 'mod'])]
        mathlib_proofs = [s for s in sorries if any(x in s.context.lower() for x in ['max_le', 'le_max', 'mathlib'])]

        hints = []
        if fold_proofs:
            hints.append("""
For fold/list proofs:
- Use List.foldl_append for additivity
- For monotonicity, prove by induction on the list
- Consider using Nat.fold_succ_last or similar lemmas
- For non-negativity, show accumulator stays non-negative at each step""")

        if arithmetic_proofs:
            hints.append("""
For arithmetic proofs:
- Use omega tactic for linear arithmetic
- Use Int.ediv_nonneg, Int.emod_nonneg for division
- Consider native_decide for concrete computations""")

        if mathlib_proofs:
            hints.append("""
For max/min proofs:
- Import Mathlib.Order.MinMax if needed
- Use le_max_left, le_max_right, max_le
- These may be in different namespaces in Lean 4.27""")

        hints_text = '\n'.join(hints) if hints else ''

        return f"""Complete all proofs in IRC Section {section}.

CRITICAL: The following theorems have 'sorry' placeholders that MUST be proven:
{theorem_list}

REQUIREMENTS:
1. Replace ALL 'sorry' with complete proofs
2. Do not use 'exact?' - find the actual proof term
3. Ensure all theorems type-check
4. Preserve existing definitions and structure
{hints_text}

PROOF STRATEGIES:
- For simple goals: try simp, rfl, decide, omega
- For conditional goals: use split, by_cases, or cases
- For list proofs: use induction or List lemmas
- For arithmetic: omega handles most linear arithmetic

This is a REMEDIATION submission to complete previously incomplete proofs.
Focus only on filling in the sorry placeholders with valid proofs.
"""

    def prepare_sections(self, sections: Optional[List[str]] = None):
        """Prepare _aristotle.lean files for specified sections"""
        sorry_map = self.scan_for_sorries()

        if sections:
            sorry_map = {s: v for s, v in sorry_map.items() if s in sections}

        print(f"\nPreparing {len(sorry_map)} sections for Aristotle remediation...\n")

        for section, sorries in sorry_map.items():
            print(f"Section {section}: {len(sorries)} sorry statements")
            for sorry in sorries:
                print(f"  - {sorry.theorem_name} (line {sorry.line})")

            # Create task
            self.queue[section] = RemediationTask(
                section=section,
                sorries=[asdict(s) for s in sorries],
                status='pending'
            )

            # Run prepare_aristotle.py
            result = subprocess.run(
                ['python3', 'scripts/prepare_aristotle.py', section],
                cwd=self.project_root,
                capture_output=True,
                text=True
            )

            if result.returncode == 0:
                self.queue[section].status = 'prepared'
                print(f"  ✓ Prepared Section{section}_aristotle.lean")
            else:
                self.queue[section].status = 'failed'
                self.queue[section].error = result.stderr
                print(f"  ✗ Failed to prepare: {result.stderr}")

        self.save_queue()
        print(f"\n✓ Prepared {sum(1 for t in self.queue.values() if t.status == 'prepared')} sections")

    async def submit_section(self, section: str) -> bool:
        """Submit a single section to Aristotle"""
        if not ARISTOTLE_AVAILABLE:
            print(f"  ✗ aristotlelib not available")
            return False

        task = self.queue.get(section)
        if not task:
            print(f"  ✗ Section {section} not in queue")
            return False

        if task.status != 'prepared':
            print(f"  ✗ Section {section} not prepared (status: {task.status})")
            return False

        aristotle_file = self.taxcode_dir / f'Section{section}_aristotle.lean'
        if not aristotle_file.exists():
            print(f"  ✗ {aristotle_file.name} not found")
            return False

        try:
            # Create enhanced prompt
            sorries = [SorryInfo(**s) for s in task.sorries]
            prompt = self.create_enhanced_prompt(section, sorries)

            # Read the current file content
            file_content = aristotle_file.read_text()

            # Create Aristotle project
            print(f"  [Aristotle] Creating INFORMAL project for Section {section}...")
            project = await aristotlelib.Project.create(
                project_input_type=aristotlelib.ProjectInputType.INFORMAL,
                validate_lean_project_root=False
            )

            # Combine prompt with file content
            full_input = f"{prompt}\n\n--- CURRENT FILE CONTENT ---\n{file_content}"

            # Submit
            print(f"  [Aristotle] Submitting remediation request...")
            await project.solve(input_content=full_input)

            task.status = 'submitted'
            task.project_id = project.project_id
            task.submitted_at = time.strftime('%Y-%m-%d %H:%M:%S')
            self.save_queue()

            print(f"  ✓ Submitted: project_id={project.project_id}")
            return True

        except Exception as e:
            task.status = 'failed'
            task.error = str(e)
            self.save_queue()
            print(f"  ✗ Failed: {e}")
            return False

    async def submit_all(self, max_concurrent: int = 3):
        """Submit all prepared sections to Aristotle"""
        prepared = [s for s, t in self.queue.items() if t.status == 'prepared']

        if not prepared:
            print("No prepared sections to submit")
            return

        print(f"\nSubmitting {len(prepared)} sections to Aristotle...\n")

        # Submit with rate limiting
        for i, section in enumerate(prepared):
            print(f"[{i+1}/{len(prepared)}] Section {section}")
            await self.submit_section(section)

            # Rate limit: wait between submissions
            if i < len(prepared) - 1:
                print("  Waiting 5s before next submission...")
                await asyncio.sleep(5)

        submitted = sum(1 for t in self.queue.values() if t.status == 'submitted')
        print(f"\n✓ Submitted {submitted} sections to Aristotle")

    def print_status(self):
        """Print current queue status"""
        print("\n=== Sorry Remediation Queue Status ===\n")

        if not self.queue:
            # Scan for sorries even if queue is empty
            sorry_map = self.scan_for_sorries()
            print(f"Found {len(sorry_map)} sections with sorry statements:\n")
            total_sorries = 0
            for section in sorted(sorry_map.keys(), key=lambda x: int(x.split('_')[0])):
                sorries = sorry_map[section]
                total_sorries += len(sorries)
                print(f"  Section {section}: {len(sorries)} sorries")
                for s in sorries:
                    print(f"    - {s.theorem_name} (line {s.line})")
            print(f"\nTotal: {total_sorries} sorry statements to remediate")
            return

        # Show queue status
        status_counts = {'pending': 0, 'prepared': 0, 'submitted': 0, 'complete': 0, 'failed': 0}
        for task in self.queue.values():
            status_counts[task.status] = status_counts.get(task.status, 0) + 1

        print("Queue Status:")
        for status, count in status_counts.items():
            if count > 0:
                print(f"  {status}: {count}")

        print("\nDetails:")
        for section in sorted(self.queue.keys(), key=lambda x: int(x.split('_')[0])):
            task = self.queue[section]
            status_icon = {'pending': '⏳', 'prepared': '📦', 'submitted': '🚀', 'complete': '✅', 'failed': '❌'}.get(task.status, '?')
            print(f"  {status_icon} Section {section}: {task.status}")
            if task.project_id:
                print(f"      project_id: {task.project_id}")
            if task.error:
                print(f"      error: {task.error[:50]}...")


def main():
    parser = argparse.ArgumentParser(description='Sorry Remediation Queue for Aristotle')
    parser.add_argument('--scan', action='store_true', help='Scan for sorry statements')
    parser.add_argument('--prepare', action='store_true', help='Prepare _aristotle.lean files')
    parser.add_argument('--submit', action='store_true', help='Submit to Aristotle')
    parser.add_argument('--status', action='store_true', help='Show queue status')
    parser.add_argument('--sections', type=str, help='Comma-separated section numbers (optional)')

    args = parser.parse_args()

    # Check API key for submission
    if args.submit and ARISTOTLE_AVAILABLE:
        api_key = os.getenv('ARISTOTLE_API_KEY')
        if not api_key:
            print("Error: ARISTOTLE_API_KEY environment variable not set")
            return 1
        aristotlelib.set_api_key(api_key)

    queue = SorryRemediationQueue()

    sections = None
    if args.sections:
        sections = [s.strip() for s in args.sections.split(',')]

    if args.scan or args.status:
        queue.print_status()
    elif args.prepare:
        queue.prepare_sections(sections)
    elif args.submit:
        asyncio.run(queue.submit_all())
    else:
        # Default: show status
        queue.print_status()

    return 0


if __name__ == '__main__':
    import sys
    sys.exit(main())
