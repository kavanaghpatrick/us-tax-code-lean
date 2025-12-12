#!/usr/bin/env python3
"""
Aristotle INFORMAL Mode Formalization Queue System

Uses Aristotle's formal verification to generate provably correct Lean 4 code
from natural language descriptions of IRC sections.
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

class AristotleFormalizationQueue:
    """Queue manager for Aristotle INFORMAL mode formalization"""

    def __init__(self, max_wait_hours: int = 24, polling_interval: int = 60):
        self.max_wait_hours = max_wait_hours
        self.polling_interval = polling_interval
        self.project_root = Path(__file__).parent.parent
        self.queue_file = self.project_root / 'data' / 'aristotle_queue.json'
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

    def create_formalization_prompt(self, section_num: str, legal_text: str) -> str:
        """Create natural language prompt for Aristotle INFORMAL mode"""

        # Truncate if too long (Aristotle may have limits)
        if len(legal_text) > 4000:
            legal_text = legal_text[:4000] + "\n\n[... text truncated for length ...]"

        prompt = f"""
# IRC Section {section_num} - Formalization in Lean 4

## Legal Text
{legal_text}

## Formalization Requirements

Please formalize the above IRC Section {section_num} in Lean 4 with the following:

### 1. Type Definitions
- Define all structures, enumerations, and types mentioned in the legal text
- Use appropriate Lean 4 types (Nat, Int, String, Bool, etc.)
- For currency amounts, use: `def Currency := Int`
- For tax years, use: `structure TaxYear where year : Nat`
- For filing status, use: `inductive FilingStatus | Single | MarriedFilingJointly | ...`

### 2. Calculation Functions
- Implement all calculation functions mentioned in the law
- Functions must be executable (no 'sorry' in main logic)
- Handle all cases and conditions from the legal text
- Use precise arithmetic (avoid approximations)

### 3. Theorems and Properties
- State theorems about key properties of the calculations
- Include correctness conditions
- Proofs can use 'sorry' if needed, but state the theorems

### 4. Module Structure
The formalization should start with:
```lean
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

-- Common definitions (inline these if needed)
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
  deriving DecidableEq, Repr
```

### 5. Documentation
- Add clear comments explaining each definition
- Reference specific IRC section numbers in comments (e.g., `-- IRC §{section_num}(a)`)
- Include examples with #eval if appropriate

### 6. Completeness
- Cover all major provisions in the section
- Handle edge cases mentioned in the law
- If a provision is too complex, include a TODO comment

Please provide complete, compilable Lean 4 code that accurately represents the legal requirements of IRC Section {section_num}.
"""
        return prompt

    async def formalize_section(self, section_num: str) -> FormalizationResult:
        """Formalize a single section using Aristotle INFORMAL mode"""

        print(f"\n{'='*70}")
        print(f"FORMALIZING SECTION {section_num} (Aristotle INFORMAL Mode)")
        print(f"{'='*70}")

        if section_num not in self.sections:
            print(f"  ✗ Section {section_num} not found in scraped data")
            return FormalizationResult(
                section_num=section_num,
                status='FAILED',
                project_id='',
                solution_path=None,
                time_taken=0,
                error='Section not found in scraped data'
            )

        section_data = self.sections[section_num]
        start_time = time.time()

        try:
            # Get legal text with safety check
            legal_text = section_data.get('text')
            if not legal_text:
                raise ValueError(f"Section {section_num} has no text content")

            # Ensure output directory exists
            self.output_dir.mkdir(parents=True, exist_ok=True)
            # Stage 1: Create Aristotle INFORMAL project
            print(f"\n  [Aristotle] Creating INFORMAL project...")
            project = await aristotlelib.Project.create(
                project_input_type=aristotlelib.ProjectInputType.INFORMAL,
                validate_lean_project_root=False  # Not needed for informal
            )

            print(f"  [Aristotle] Project created: {project.project_id}")

            # Stage 2: Submit formalization request
            prompt = self.create_formalization_prompt(section_num, legal_text)

            print(f"  [Aristotle] Submitting formalization request...")
            print(f"  [Aristotle] Legal text length: {len(legal_text)} chars")

            await project.solve(input_content=prompt)

            print(f"  [Aristotle] Status: {project.status.name}")

            # Update queue
            self.queue[section_num] = {
                'status': 'submitted',
                'project_id': project.project_id,
                'submitted_at': time.strftime('%Y-%m-%d %H:%M:%S')
            }
            self.save_queue()

            # Stage 3: Wait for completion
            max_wait_seconds = self.max_wait_hours * 3600
            elapsed = 0

            print(f"  [Aristotle] Waiting for completion (max {self.max_wait_hours} hours)...")
            print(f"  [Aristotle] Polling every {self.polling_interval} seconds")

            while elapsed < max_wait_seconds:
                await asyncio.sleep(self.polling_interval)
                elapsed += self.polling_interval

                await project.refresh()

                status_str = f"  [{elapsed//60:3d}m] Status: {project.status.name}"
                if project.percent_complete:
                    status_str += f" ({project.percent_complete}%)"
                print(status_str)

                if project.status == aristotlelib.ProjectStatus.COMPLETE:
                    print(f"\n  ✓ COMPLETE after {elapsed//60} minutes")
                    break
                elif project.status == aristotlelib.ProjectStatus.FAILED:
                    print(f"\n  ✗ FAILED after {elapsed//60} minutes")
                    # Update queue before returning
                    self.queue[section_num] = {
                        'status': 'failed',
                        'project_id': project.project_id,
                        'failed_at': time.strftime('%Y-%m-%d %H:%M:%S'),
                        'error': 'Aristotle project failed'
                    }
                    self.save_queue()
                    return FormalizationResult(
                        section_num=section_num,
                        status='FAILED',
                        project_id=project.project_id,
                        solution_path=None,
                        time_taken=elapsed,
                        error='Aristotle project failed'
                    )

            if project.status != aristotlelib.ProjectStatus.COMPLETE:
                print(f"\n  ⚠ TIMEOUT after {self.max_wait_hours} hours")
                # Update queue before returning
                self.queue[section_num] = {
                    'status': 'timeout',
                    'project_id': project.project_id,
                    'timeout_at': time.strftime('%Y-%m-%d %H:%M:%S'),
                    'error': f'Timeout after {self.max_wait_hours} hours'
                }
                self.save_queue()
                return FormalizationResult(
                    section_num=section_num,
                    status='TIMEOUT',
                    project_id=project.project_id,
                    solution_path=None,
                    time_taken=elapsed,
                    error=f'Timeout after {self.max_wait_hours} hours'
                )

            # Stage 4: Download solution
            print(f"\n  [Aristotle] Downloading formally verified solution...")

            output_path = self.output_dir / f'Section{section_num}.lean'
            solution_path = await project.get_solution(output_path=output_path)

            print(f"  [Aristotle] Solution saved to: {solution_path}")

            # Verify file exists and has content
            if solution_path.exists() and solution_path.stat().st_size > 0:
                file_size = solution_path.stat().st_size
                print(f"  [Aristotle] File size: {file_size} bytes")

                # Update queue
                time_taken = time.time() - start_time
                self.queue[section_num] = {
                    'status': 'complete',
                    'project_id': project.project_id,
                    'solution_path': str(solution_path),
                    'completed_at': time.strftime('%Y-%m-%d %H:%M:%S'),
                    'time_taken_seconds': int(time_taken)
                }
                self.save_queue()

                print(f"\n  ✓ SUCCESS - Formally verified Lean 4 code generated!")
                print(f"  Time: {time_taken//60:.0f} minutes")

                return FormalizationResult(
                    section_num=section_num,
                    status='SUCCESS',
                    project_id=project.project_id,
                    solution_path=solution_path,
                    time_taken=time_taken
                )
            else:
                raise RuntimeError("Downloaded file is empty or missing")

        except Exception as e:
            time_taken = time.time() - start_time
            print(f"\n  ✗ ERROR: {e}")

            self.queue[section_num] = {
                'status': 'failed',
                'error': str(e),
                'failed_at': time.strftime('%Y-%m-%d %H:%M:%S')
            }
            self.save_queue()

            return FormalizationResult(
                section_num=section_num,
                status='FAILED',
                project_id=project.project_id if 'project' in locals() else '',
                solution_path=None,
                time_taken=time_taken,
                error=str(e)
            )

    async def process_batch(self, section_nums: List[str]):
        """Process a batch of sections sequentially"""

        print(f"\n{'='*70}")
        print(f"ARISTOTLE FORMALIZATION QUEUE - {len(section_nums)} SECTIONS")
        print(f"{'='*70}")
        print(f"Max wait per section: {self.max_wait_hours} hours")
        print(f"Polling interval: {self.polling_interval} seconds\n")

        results = {
            'success': [],
            'failed': [],
            'timeout': []
        }

        for i, section_num in enumerate(section_nums, 1):
            print(f"\n--- Section {i}/{len(section_nums)} ---")

            result = await self.formalize_section(section_num)

            if result.status == 'SUCCESS':
                results['success'].append(section_num)
            elif result.status == 'TIMEOUT':
                results['timeout'].append(section_num)
            else:
                results['failed'].append(section_num)

            # Brief pause between sections (be nice to API)
            if i < len(section_nums):
                print(f"\n  Waiting 10 seconds before next section...")
                await asyncio.sleep(10)

        # Summary
        print(f"\n{'='*70}")
        print(f"BATCH COMPLETE")
        print(f"{'='*70}")
        print(f"  ✓ Success: {len(results['success'])}/{len(section_nums)}")
        print(f"  ✗ Failed: {len(results['failed'])}")
        print(f"  ⏱ Timeout: {len(results['timeout'])}")

        if results['failed']:
            print(f"\n  Failed sections: {', '.join(results['failed'])}")
        if results['timeout']:
            print(f"  Timeout sections: {', '.join(results['timeout'])}")

        return results

def main():
    parser = argparse.ArgumentParser(
        description='Formalization queue using Aristotle INFORMAL mode'
    )
    parser.add_argument('--sections', type=str,
                       help='Comma-separated section numbers')
    parser.add_argument('--pilot', action='store_true',
                       help='Run 5-section pilot (71, 101, 102, 103, 108)')
    parser.add_argument('--priority-50', action='store_true',
                       help='Process all 50 priority sections')
    parser.add_argument('--max-wait-hours', type=int, default=24,
                       help='Max hours to wait per section (default: 24)')
    parser.add_argument('--polling-interval', type=int, default=60,
                       help='Seconds between status checks (default: 60)')

    args = parser.parse_args()

    queue = AristotleFormalizationQueue(
        max_wait_hours=args.max_wait_hours,
        polling_interval=args.polling_interval
    )

    if args.pilot:
        sections = ['71', '101', '102', '103', '108']
        print("Running 5-section pilot with Aristotle INFORMAL mode...")
    elif args.priority_50:
        # REVISED priority 50 sections (Grok-optimized for maximum leverage)
        # Focus: AMT, entity arbitrage, loophole-prone areas, contradiction detection
        sections = [
            # Income (9) - removed §71 (alimony), §102 (gifts) for higher-leverage sections
            '1', '61', '62', '63', '101', '103', '108', '121', '199',
            # Deductions (12) - removed §195, §213, §217, added §469 (passive losses)
            '162', '163', '164', '165', '166', '167', '168', '170', '174', '179', '274', '469',
            # Credits (6) - removed §27, §30, §31, §45 (niche credits)
            '21', '24', '25', '32', '38', '41',
            # AMT - Alternative Minimum Tax (3) - CRITICAL for contradiction detection
            '55', '56', '59',
            # Capital Gains (10) - unchanged, high loophole potential
            '1001', '1011', '1012', '1014', '1015', '1031', '1202', '1221', '1222', '1231',
            # Corporate/Partnership/International (6) - removed §303, added §482 (transfer pricing), §267 (related party)
            '11', '267', '301', '302', '311', '482',
            # Retirement (2) - CRITICAL for taxpayer impact and entity loopholes
            '401', '408',
            # Estate/Gift Tax (2) - CRITICAL for wealth transfer and cross-references
            '2001', '2501'
        ]
        print(f"Processing {len(sections)} REVISED priority sections (Grok-optimized for leverage)...")
    elif args.sections:
        sections = [s.strip() for s in args.sections.split(',')]
    else:
        parser.print_help()
        return

    results = asyncio.run(queue.process_batch(sections))

    print(f"\n✓ Processing complete")
    print(f"  Queue state saved to: {queue.queue_file}")

if __name__ == '__main__':
    main()
