#!/usr/bin/env python3
"""
Aristotle INFORMAL Mode Rerun Queue System

Reruns failed sections with improved prompts based on failure analysis.
Specifically designed for:
- Section 1: Timeout - needs 2024 TCJA-compliant tax brackets
- Section 103: Incomplete proofs - needs proof completion

Uses enhanced prompts to avoid previous failures.
"""

import argparse
import asyncio
import json
import os
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass
import time
import aristotlelib

@dataclass
class FormalizationResult:
    """Result from Aristotle formalization"""
    section_num: str
    status: str  # SUCCESS, FAILED, TIMEOUT
    project_id: str
    solution_path: Optional[Path]
    time_taken: float
    error: Optional[str] = None

class AristotleRerunQueue:
    """Queue manager for Aristotle INFORMAL mode reruns with enhanced prompts"""

    # Enhanced prompts for problematic sections
    ENHANCED_PROMPTS = {
        "1": """
Formalize IRC Section 1 (Tax Tables) in Lean 4.

CRITICAL REQUIREMENTS:
1. Use 2024 post-TCJA tax brackets (7 brackets total):
   - 10%, 12%, 22%, 24%, 32%, 35%, 37%
2. Include thresholds for all filing statuses:
   - Single
   - Married Filing Jointly
   - Married Filing Separately
   - Head of Household
   - Qualifying Widow(er)
3. Model standard deduction amounts for 2024
4. Complete all proofs (no 'sorry' or 'exact?' placeholders)
5. Include test cases with #eval for verification

AVOID:
- Pre-TCJA tax brackets (15%, 28%, 31%, 36%, 39.6%)
- Outdated standard deduction amounts
- Incomplete theorems

This is a RERUN due to previous timeout. Focus on completeness and current law.
""",
        "103": """
Formalize IRC Section 103 (Interest on State and Local Bonds) in Lean 4.

CRITICAL REQUIREMENTS:
1. Complete ALL proofs - no 'exact?' or 'sorry' placeholders
2. Verify all theorems have complete proof terms
3. Include interest partition logic between taxable and tax-exempt bonds
4. Model private activity bond rules
5. Include test cases with #eval for verification

AVOID:
- Leaving tactical proof searches (exact?) unresolved
- Incomplete theorem statements
- Missing proof completions

This is a RERUN due to incomplete proofs (lines 164, 166 had 'exact?' placeholders).
Ensure ALL theorems are proven completely.
"""
    }

    def __init__(self, max_wait_hours: int = 24, polling_interval: int = 60):
        self.max_wait_hours = max_wait_hours
        self.polling_interval = polling_interval
        self.project_root = Path(__file__).parent.parent
        self.queue_file = self.project_root / 'data' / 'aristotle_rerun_queue.json'
        self.sections_data = self.project_root / 'data' / 'sections.json'
        self.output_dir = self.project_root / 'src' / 'TaxCode'

        # Initialize Aristotle API
        api_key = os.getenv('ARISTOTLE_API_KEY')
        if not api_key:
            raise ValueError("ARISTOTLE_API_KEY environment variable not set")

        aristotlelib.set_api_key(api_key)

        # Load queue state and sections
        self.load_queue()
        self.load_sections()

    def load_queue(self):
        """Load queue state from disk"""
        if self.queue_file.exists():
            try:
                with open(self.queue_file) as f:
                    data = json.load(f)
                    self.queue = data.get('sections', {})
                    self.metrics = data.get('metrics', {})
            except (json.JSONDecodeError, IOError) as e:
                print(f"Warning: Failed to load queue file: {e}")
                print("Starting with empty queue...")
                self.queue = {}
                self.metrics = {
                    'pending': 0,
                    'submitted': 0,
                    'complete': 0,
                    'failed': 0,
                    'timeout': 0
                }
        else:
            self.queue = {}
            self.metrics = {
                'pending': 0,
                'submitted': 0,
                'complete': 0,
                'failed': 0,
                'timeout': 0
            }

    def save_queue(self):
        """Save queue state to disk"""
        self.queue_file.parent.mkdir(parents=True, exist_ok=True)
        with open(self.queue_file, 'w') as f:
            json.dump({
                'sections': self.queue,
                'metrics': self.metrics,
                'last_updated': time.strftime('%Y-%m-%d %H:%M:%S')
            }, f, indent=2)

    def load_sections(self):
        """Load scraped section data"""
        try:
            with open(self.sections_data) as f:
                sections_list = json.load(f)
                self.sections = {str(s['section']): s for s in sections_list}
        except (json.JSONDecodeError, IOError, FileNotFoundError) as e:
            raise RuntimeError(
                f"Failed to load sections data from {self.sections_data}: {e}\n"
                "Please ensure data/sections.json exists and is valid."
            )

    async def formalize_section(self, section_num: str) -> FormalizationResult:
        """Formalize section with enhanced prompt using Aristotle INFORMAL"""
        section_data = self.sections.get(section_num)
        if not section_data:
            raise ValueError(f"Section {section_num} not found in sections.json")

        start_time = time.time()

        # Use enhanced prompt if available
        if section_num in self.ENHANCED_PROMPTS:
            prompt = self.ENHANCED_PROMPTS[section_num]
            print(f"  Using enhanced prompt for Section {section_num}")
        else:
            # Fallback to section text with rerun note
            section_text = section_data.get('text', '')
            prompt = f"Formalize IRC Section {section_num} in Lean 4.\n\nREQUIREMENTS:\n- Complete all proofs (no 'sorry' or 'exact?')\n- Include test cases\n- Verify theorems are proven\n\nSection Text:\n{section_text}"

        # Stage 1: Create Aristotle INFORMAL project
        print(f"  [Aristotle] Creating INFORMAL project...")
        project = await aristotlelib.Project.create(
            project_input_type=aristotlelib.ProjectInputType.INFORMAL,
            validate_lean_project_root=False
        )

        print(f"  [Aristotle] Project created: {project.project_id}")

        # Stage 2: Submit formalization request
        print(f"  [Aristotle] Submitting formalization request...")
        await project.solve(input_content=prompt)
        print(f"  [Aristotle] Status: {project.status.name}")

        # Stage 3: Wait for completion
        max_wait_seconds = self.max_wait_hours * 3600

        print(f"  [Aristotle] Waiting for completion (max {self.max_wait_hours}h)...")

        while True:
            elapsed = time.time() - start_time

            if elapsed > max_wait_seconds:
                return FormalizationResult(
                    section_num=section_num,
                    status='TIMEOUT',
                    project_id=project.project_id,
                    solution_path=None,
                    time_taken=elapsed,
                    error=f'Exceeded max wait time of {self.max_wait_hours} hours'
                )

            # Refresh project status
            await project.refresh()

            # Log status
            status_str = f"  [{int(elapsed/60):3d}m] Status: {project.status.name}"
            if project.percent_complete:
                status_str += f" ({project.percent_complete}%)"
            print(status_str)

            if project.status == aristotlelib.ProjectStatus.COMPLETE:
                # Download solution
                solution_path = self.output_dir / f"Section{section_num}.lean"
                solution_path.parent.mkdir(parents=True, exist_ok=True)

                solution = project.solution
                if solution:
                    with open(solution_path, 'w') as f:
                        f.write(solution)

                    print(f"  ✅ Formalization complete!")
                    print(f"  Time taken: {int(elapsed / 60)} minutes")

                    return FormalizationResult(
                        section_num=section_num,
                        status='SUCCESS',
                        project_id=project.project_id,
                        solution_path=solution_path,
                        time_taken=elapsed
                    )
                else:
                    return FormalizationResult(
                        section_num=section_num,
                        status='FAILED',
                        project_id=project.project_id,
                        solution_path=None,
                        time_taken=elapsed,
                        error='Project marked COMPLETE but no solution available'
                    )

            elif project.status == aristotlelib.ProjectStatus.FAILED:
                return FormalizationResult(
                    section_num=section_num,
                    status='FAILED',
                    project_id=project.project_id,
                    solution_path=None,
                    time_taken=elapsed,
                    error=f'Project status: {project.status.name}'
                )

            # Wait before polling again
            await asyncio.sleep(self.polling_interval)

    async def process_sections(self, section_nums: List[str]):
        """Process sections sequentially (since Aristotle can be slow)"""
        print(f"\n{'='*60}")
        print(f"ARISTOTLE RERUN QUEUE - Enhanced Prompts")
        print(f"{'='*60}")
        print(f"Sections to process: {', '.join(section_nums)}")
        print(f"Max wait per section: {self.max_wait_hours} hours")
        print(f"Polling interval: {self.polling_interval} seconds")
        print(f"{'='*60}\n")

        # Initialize queue for new sections
        for num in section_nums:
            if num not in self.queue:
                self.queue[num] = {
                    'status': 'pending',
                    'attempts': 0,
                    'history': []
                }

        # Process sequentially
        for section_num in section_nums:
            if self.queue[section_num]['status'] in ['complete', 'success']:
                print(f"Section {section_num}: Already complete, skipping")
                continue

            print(f"\n{'='*60}")
            print(f"Processing Section {section_num}")
            print(f"{'='*60}")

            try:
                # Formalize with Aristotle
                result = await self.formalize_section(section_num)

                # Update attempts
                self.queue[section_num]['attempts'] += 1

                # Update queue with result
                if result.status == 'SUCCESS':
                    self.queue[section_num]['status'] = 'complete'
                    self.queue[section_num]['project_id'] = result.project_id
                    self.queue[section_num]['solution_path'] = str(result.solution_path)
                    self.queue[section_num]['completed_at'] = time.strftime('%Y-%m-%d %H:%M:%S')
                    self.queue[section_num]['time_taken_seconds'] = int(result.time_taken)
                    print(f"  ✅ Section {section_num} completed successfully!")
                    print(f"  Solution: {result.solution_path}")
                    print(f"  Time: {int(result.time_taken / 60)} minutes")
                elif result.status == 'TIMEOUT':
                    self.queue[section_num]['status'] = 'timeout'
                    self.queue[section_num]['project_id'] = result.project_id
                    self.queue[section_num]['error'] = result.error
                    self.queue[section_num]['timeout_at'] = time.strftime('%Y-%m-%d %H:%M:%S')
                    print(f"  ⏱️  Section {section_num} timed out after {self.max_wait_hours} hours")
                else:
                    self.queue[section_num]['status'] = 'failed'
                    self.queue[section_num]['project_id'] = result.project_id
                    self.queue[section_num]['error'] = result.error
                    self.queue[section_num]['failed_at'] = time.strftime('%Y-%m-%d %H:%M:%S')
                    print(f"  ❌ Section {section_num} failed: {result.error}")

                self.queue[section_num]['history'].append({
                    'attempt': self.queue[section_num]['attempts'],
                    'project_id': result.project_id,
                    'status': result.status,
                    'time_taken': int(result.time_taken),
                    'timestamp': time.strftime('%Y-%m-%d %H:%M:%S')
                })

                self.save_queue()

            except Exception as e:
                print(f"  ❌ Error processing Section {section_num}: {e}")
                self.queue[section_num]['status'] = 'failed'
                self.queue[section_num]['error'] = str(e)
                self.save_queue()

        print(f"\n{'='*60}")
        print(f"RERUN QUEUE COMPLETE")
        print(f"{'='*60}")
        self.print_summary()

    def print_summary(self):
        """Print summary of queue status"""
        complete = sum(1 for v in self.queue.values() if v['status'] == 'complete')
        failed = sum(1 for v in self.queue.values() if v['status'] == 'failed')
        timeout = sum(1 for v in self.queue.values() if v['status'] == 'timeout')
        pending = sum(1 for v in self.queue.values() if v['status'] == 'pending')

        print(f"Complete: {complete}")
        print(f"Failed: {failed}")
        print(f"Timeout: {timeout}")
        print(f"Pending: {pending}")
        print(f"Total: {len(self.queue)}")

async def main():
    parser = argparse.ArgumentParser(description='Aristotle INFORMAL Rerun Queue with Enhanced Prompts')
    parser.add_argument('--sections', type=str, required=True,
                       help='Comma-separated list of section numbers to rerun (e.g., "1,103")')
    parser.add_argument('--max-wait-hours', type=int, default=24,
                       help='Maximum hours to wait per section (default: 24)')
    parser.add_argument('--polling-interval', type=int, default=60,
                       help='Polling interval in seconds (default: 60)')

    args = parser.parse_args()

    # Parse sections
    section_nums = [s.strip() for s in args.sections.split(',')]

    # Create queue and process
    queue = AristotleRerunQueue(
        max_wait_hours=args.max_wait_hours,
        polling_interval=args.polling_interval
    )

    await queue.process_sections(section_nums)

if __name__ == '__main__':
    asyncio.run(main())
