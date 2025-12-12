#!/usr/bin/env python3
"""
Grok-4 Formalization Queue System

Uses Grok-4 for generation and validation, iteration until quality threshold met.
"""

import argparse
import asyncio
import json
import os
import subprocess
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass
import time

@dataclass
class ValidationResult:
    """Result from Grok's validation"""
    legal_accuracy: int  # 1-10
    type_correctness: int  # 1-10
    function_logic: int  # 1-10
    completeness: int  # 1-10
    assessment: str  # REJECT, NEEDS_WORK, ACCEPTABLE, EXCELLENT
    issues: List[str]
    average_score: float

class FormalizationQueue:
    """Queue manager for systematic section formalization"""

    def __init__(self, max_iterations: int = 3):
        self.max_iterations = max_iterations
        self.project_root = Path(__file__).parent.parent
        self.queue_file = self.project_root / 'data' / 'formalization_queue.json'
        self.sections_data = self.project_root / 'data' / 'sections.json'

        # Initialize Grok API
        self.grok_api_key = os.getenv('GROK_API_KEY')
        if not self.grok_api_key:
            raise ValueError("GROK_API_KEY environment variable not set")

        # Load queue state
        self.load_queue()
        self.load_sections()

    def load_queue(self):
        """Load queue state from disk"""
        if self.queue_file.exists():
            with open(self.queue_file) as f:
                data = json.load(f)
                self.queue = data.get('sections', {})
                self.metrics = data.get('metrics', {})
        else:
            self.queue = {}
            self.metrics = {
                'pending': 0,
                'drafted': 0,
                'validated': 0,
                'complete': 0,
                'failed': 0
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
        with open(self.sections_data) as f:
            sections_list = json.load(f)
            # Convert list to dict keyed by section number
            self.sections = {str(s['section']): s for s in sections_list}

    def call_grok(self, prompt: str, temperature: float = 0.3, json_mode: bool = False) -> str:
        """Call Grok-4 API via curl"""
        request = {
            "messages": [{"role": "user", "content": prompt}],
            "model": "grok-4",
            "temperature": temperature,
            "max_tokens": 4000
        }

        if json_mode:
            request["response_format"] = {"type": "json_object"}

        # Use Python to write JSON (handles escaping)
        request_file = '/tmp/grok_request.json'
        with open(request_file, 'w') as f:
            json.dump(request, f)

        # Call Grok API
        result = subprocess.run([
            'curl', '-s', '-X', 'POST',
            'https://api.x.ai/v1/chat/completions',
            '-H', f'Authorization: Bearer {self.grok_api_key}',
            '-H', 'Content-Type: application/json',
            '-d', f'@{request_file}'
        ], capture_output=True, text=True, timeout=300)

        if result.returncode != 0:
            raise RuntimeError(f"Grok API call failed: {result.stderr}")

        response = json.loads(result.stdout)
        if 'error' in response:
            raise RuntimeError(f"Grok API error: {response['error']}")

        return response['choices'][0]['message']['content']

    def generate_with_grok(self, section_num: str, legal_text: str) -> str:
        """Generate Lean code using Grok-4"""

        # Truncate if too long
        if len(legal_text) > 3000:
            legal_text = legal_text[:3000] + "... [truncated]"

        prompt = f"""You are a Lean 4 expert formalizing US Tax Code.

Generate COMPLETE, EXECUTABLE Lean 4 code for:

**IRC Section {section_num}**
**Legal Text**:
{legal_text}

Requirements:
1. Import Common.Basic (Currency, FilingStatus, TaxYear)
2. Define ALL types/structures mentioned in the law
3. Implement ALL calculation functions (executable, NO 'sorry' in main logic)
4. Add theorems about properties (can use 'sorry' in proofs)
5. Include examples with #eval
6. Add clear comments

Output ONLY valid Lean 4 code. Be comprehensive and accurate."""

        print(f"  [Grok-4] Generating code for §{section_num}...")

        code = self.call_grok(prompt, temperature=0.3)

        print(f"  [Grok-4] Generated {len(code)} chars")

        return code

    def validate_with_grok(self, section_num: str, legal_text: str, lean_code: str) -> ValidationResult:
        """Validate code using Grok-4 (critical reviewer mode)"""

        # Truncate for prompt
        if len(legal_text) > 2000:
            legal_text = legal_text[:2000] + "... [truncated]"

        prompt = f"""You are a critical code reviewer for legal formalization.

**Original IRC Section {section_num}**:
{legal_text}

**Generated Lean Code**:
{lean_code}

CRITICAL REVIEW (be harsh):

1. Legal Accuracy (1-10): Does code match legal text?
2. Type Correctness (1-10): Are types appropriate and not hallucinated?
3. Function Logic (1-10): Does logic match legal intent?
4. Completeness (1-10): All provisions covered?

5. Critical Issues:
   - MUST FIX: Blocking errors (list)
   - SHOULD FIX: Important improvements (list)

6. Overall Assessment:
   - REJECT: Too many errors, regenerate
   - NEEDS_WORK: Fix issues and retry
   - ACCEPTABLE: Minor issues, usable
   - EXCELLENT: High quality, ready

Format response as JSON:
{{
  "legal_accuracy": <1-10>,
  "type_correctness": <1-10>,
  "function_logic": <1-10>,
  "completeness": <1-10>,
  "must_fix": ["issue1", "issue2"],
  "should_fix": ["issue1"],
  "assessment": "REJECT|NEEDS_WORK|ACCEPTABLE|EXCELLENT"
}}
"""

        print(f"  [Grok-4] Reviewing code...")

        review_json = json.loads(self.call_grok(prompt, temperature=0.3, json_mode=True))

        # Parse into ValidationResult
        avg_score = (
            review_json['legal_accuracy'] +
            review_json['type_correctness'] +
            review_json['function_logic'] +
            review_json['completeness']
        ) / 4

        validation = ValidationResult(
            legal_accuracy=review_json['legal_accuracy'],
            type_correctness=review_json['type_correctness'],
            function_logic=review_json['function_logic'],
            completeness=review_json['completeness'],
            assessment=review_json['assessment'],
            issues=review_json.get('must_fix', []) + review_json.get('should_fix', []),
            average_score=avg_score
        )

        print(f"  [Grok-4] Assessment: {validation.assessment} (avg {avg_score:.1f}/10)")

        return validation

    def refine_with_grok(self, section_num: str, code: str, issues: List[str]) -> str:
        """Refine code based on validation feedback"""

        issues_text = "\n".join(f"- {issue}" for issue in issues)

        prompt = f"""You are a Lean 4 expert. Fix this code based on review feedback.

**Current Code**:
{code}

**Issues to Fix**:
{issues_text}

Generate IMPROVED code that addresses all issues. Output ONLY valid Lean 4 code."""

        print(f"  [Grok-4] Refining code (fixing {len(issues)} issues)...")

        refined = self.call_grok(prompt, temperature=0.3)
        print(f"  [Grok-4] Refinement complete")

        return refined

    def compile_lean(self, section_num: str, code: str) -> bool:
        """Check if code compiles"""
        temp_file = Path(f'/tmp/Section{section_num}.lean')
        temp_file.write_text(code)

        result = subprocess.run(
            ['lean', str(temp_file)],
            capture_output=True,
            text=True
        )

        success = result.returncode == 0

        if success:
            print(f"  [Lean] ✓ Compiles successfully")
        else:
            print(f"  [Lean] ✗ Compilation error:")
            print(f"    {result.stderr[:200]}")

        return success

    def formalize_section(self, section_num: str) -> bool:
        """Formalize a single section with Grok-4 validation"""

        print(f"\n{'='*60}")
        print(f"FORMALIZING SECTION {section_num}")
        print(f"{'='*60}")

        if section_num not in self.sections:
            print(f"  ✗ Section {section_num} not found in scraped data")
            return False

        section_data = self.sections[section_num]
        legal_text = section_data['text']

        best_code = None
        best_score = 0

        for iteration in range(1, self.max_iterations + 1):
            print(f"\n  Iteration {iteration}/{self.max_iterations}")
            print(f"  {'-'*50}")

            try:
                # Stage 1: Generate code with Grok-4
                lean_code = self.generate_with_grok(section_num, legal_text)

                # Stage 2: Validate with Grok-4 (critical reviewer mode)
                validation = self.validate_with_grok(section_num, legal_text, lean_code)

                # Track best attempt
                if validation.average_score > best_score:
                    best_score = validation.average_score
                    best_code = lean_code

                # Stage 3: Check assessment
                if validation.assessment == "EXCELLENT":
                    print(f"\n  ✓ EXCELLENT quality achieved!")
                    break
                elif validation.assessment == "ACCEPTABLE":
                    print(f"\n  ✓ ACCEPTABLE quality achieved")
                    break
                elif validation.assessment == "REJECT" and iteration < self.max_iterations:
                    print(f"\n  ⚠ REJECTED - Regenerating from scratch...")
                    continue
                elif validation.issues and iteration < self.max_iterations:
                    print(f"\n  ⚠ NEEDS_WORK - Refining...")
                    lean_code = self.refine_with_grok(section_num, lean_code, validation.issues)
                    best_code = lean_code

            except Exception as e:
                print(f"  ✗ Error in iteration {iteration}: {e}")
                if iteration == self.max_iterations:
                    break
                continue

        # Stage 4: Compilation check
        if best_code:
            compiles = self.compile_lean(section_num, best_code)

            if compiles:
                # Save to file
                output_file = self.project_root / 'src' / 'TaxCode' / f'Section{section_num}.lean'
                output_file.write_text(best_code)

                # Update queue
                self.queue[section_num] = {
                    'status': 'complete',
                    'quality_score': best_score,
                    'iterations': iteration,
                    'assessment': validation.assessment if 'validation' in locals() else 'UNKNOWN'
                }
                self.save_queue()

                print(f"\n  ✓ SUCCESS - Saved to {output_file}")
                print(f"  Quality: {best_score:.1f}/10, {iteration} iterations")
                return True

        # Failed
        self.queue[section_num] = {
            'status': 'failed',
            'quality_score': best_score,
            'iterations': iteration
        }
        self.save_queue()

        print(f"\n  ✗ FAILED after {iteration} iterations")
        return False

    def process_batch(self, section_nums: List[str]):
        """Process a batch of sections"""

        print(f"\n{'='*60}")
        print(f"PROCESSING {len(section_nums)} SECTIONS")
        print(f"{'='*60}\n")

        results = {
            'success': [],
            'failed': []
        }

        for section_num in section_nums:
            success = self.formalize_section(section_num)

            if success:
                results['success'].append(section_num)
            else:
                results['failed'].append(section_num)

            # Brief pause between sections
            time.sleep(2)

        # Summary
        print(f"\n{'='*60}")
        print(f"BATCH COMPLETE")
        print(f"{'='*60}")
        print(f"  Success: {len(results['success'])}/{len(section_nums)}")
        print(f"  Failed: {len(results['failed'])}")

        if results['failed']:
            print(f"  Failed sections: {', '.join(results['failed'])}")

        return results

def main():
    parser = argparse.ArgumentParser(description='Formalization queue with multi-LLM validation')
    parser.add_argument('--sections', type=str, help='Comma-separated section numbers')
    parser.add_argument('--pilot', action='store_true', help='Run 5-section pilot')
    parser.add_argument('--priority-50', action='store_true', help='Process 50 priority sections')
    parser.add_argument('--max-iterations', type=int, default=3, help='Max refinement iterations')

    args = parser.parse_args()

    queue = FormalizationQueue(max_iterations=args.max_iterations)

    if args.pilot:
        # Pilot: 5 sections
        sections = ['71', '101', '102', '103', '108']
        print("Running 5-section pilot...")
    elif args.priority_50:
        # Full list of 50 priority sections (validated against scraped data)
        sections = [
            # Income (10)
            '1', '61', '62', '63', '71', '101', '102', '103', '108', '121',
            # Deductions (15)
            '162', '163', '164', '165', '166', '167', '168', '170', '174', '179',
            '195', '212', '213', '217', '274',
            # Credits (10) - using main sections (25A/25D/30D are subsections of 25/30)
            '21', '24', '25', '27', '30', '31', '32', '38', '41', '45',
            # Capital Gains (10)
            '1001', '1011', '1012', '1014', '1015', '1031', '1202', '1221', '1222', '1231',
            # Corporate/Partnership (5)
            '11', '301', '302', '303', '311'
        ]
        print(f"Processing {len(sections)} priority sections...")
    elif args.sections:
        sections = args.sections.split(',')
    else:
        parser.print_help()
        return

    results = queue.process_batch(sections)

    print(f"\n✓ Processing complete")
    print(f"  Results saved to: {queue.queue_file}")

if __name__ == '__main__':
    main()
