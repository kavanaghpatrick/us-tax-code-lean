#!/usr/bin/env python3
"""
Continues Aristotle formalization of remaining stub files.
"""
import asyncio
import os
import json
import re
from pathlib import Path
from datetime import datetime
import aristotlelib

# Common definitions to inject
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

class FormalizationProcessor:
    def __init__(self, max_concurrent=5, poll_interval=60):
        self.max_concurrent = max_concurrent
        self.poll_interval = poll_interval
        self.active_projects = {}  # project_id -> section_name
        self.project_root = Path(__file__).parent.parent
        self.taxcode_dir = self.project_root / 'src' / 'TaxCode'
        self.log_file = Path('/tmp/aristotle_continue.log')

        api_key = os.getenv('ARISTOTLE_API_KEY')
        if not api_key:
            raise ValueError("ARISTOTLE_API_KEY not set")
        aristotlelib.set_api_key(api_key)

    def log(self, msg):
        timestamp = datetime.now().strftime('%H:%M:%S')
        line = f"[{timestamp}] {msg}"
        print(line)
        with open(self.log_file, 'a') as f:
            f.write(line + '\n')

    def get_stubs(self):
        """Find all stub files"""
        stubs = []
        for f in self.taxcode_dir.glob('Section*.lean'):
            if any(x in f.name for x in ['_backup', '_aristotle', '_output']):
                continue
            content = f.read_text()
            if 'TODO: Add type definitions' in content:
                stubs.append(f)
        return sorted(stubs)

    def prepare_content(self, stub_path):
        """Prepare file content for Aristotle submission"""
        content = stub_path.read_text()

        # Replace Common.Basic import with inline definitions
        if 'import TaxCode.Common.Basic' in content or 'import Common.Basic' in content:
            content = re.sub(
                r'import\s+(TaxCode\.)?Common\.Basic\s*\n?',
                f'\n{COMMON_DEFS}\n',
                content
            )

        return content

    async def submit_stub(self, stub_path):
        """Submit a stub file to Aristotle"""
        section_name = stub_path.stem
        content = self.prepare_content(stub_path)

        try:
            project = await aristotlelib.Project.prove_from_file(
                input_content=content,
                wait_for_completion=False
            )
            project_id = str(project.id) if hasattr(project, 'id') else str(project)
            self.active_projects[project_id] = section_name
            self.log(f"✓ Submitted {section_name}")
            return True
        except Exception as e:
            self.log(f"✗ Submit failed {section_name}: {e}")
            return False

    async def check_and_integrate(self):
        """Check active projects and integrate completed ones"""
        if not self.active_projects:
            return

        result = await aristotlelib.Project.list_projects()
        if isinstance(result, tuple):
            projects, _ = result
        else:
            projects = result

        projects_by_id = {str(p.id): p for p in projects}

        completed = []
        for proj_id, section_name in list(self.active_projects.items()):
            if proj_id not in projects_by_id:
                # Project expired or unknown
                self.log(f"⚠ Project {section_name} ({proj_id[:8]}...) not found")
                completed.append(proj_id)
                continue

            proj = projects_by_id[proj_id]
            status = proj.status.name

            if status == 'COMPLETE':
                # Get and integrate solution
                try:
                    solution_path = await proj.get_solution()
                    if solution_path and solution_path.exists():
                        output_file = self.taxcode_dir / f"{section_name}_aristotle_output.lean"
                        solution_path.rename(output_file)
                        self.log(f"✅ Integrated {section_name}")
                    else:
                        self.log(f"⚠ No solution for {section_name}")
                except Exception as e:
                    self.log(f"✗ Integration failed {section_name}: {e}")
                completed.append(proj_id)

            elif status == 'FAILED':
                self.log(f"✗ Failed {section_name}")
                completed.append(proj_id)

        for proj_id in completed:
            del self.active_projects[proj_id]

    async def run(self):
        """Main processing loop"""
        self.log("=== Starting formalization processor ===")

        while True:
            # Check and integrate completed projects
            await self.check_and_integrate()

            # Get current status
            stubs = self.get_stubs()
            active_count = len(self.active_projects)
            slots = self.max_concurrent - active_count

            self.log(f"📊 {len(stubs)} stubs | {active_count} active")

            if not stubs and not self.active_projects:
                self.log("🎉 All stubs processed!")
                break

            # Submit new stubs if we have capacity
            if slots > 0 and stubs:
                to_submit = stubs[:slots]
                for stub in to_submit:
                    await self.submit_stub(stub)
                    await asyncio.sleep(1)  # Rate limit

            await asyncio.sleep(self.poll_interval)

async def main():
    processor = FormalizationProcessor(max_concurrent=5, poll_interval=60)
    await processor.run()

if __name__ == '__main__':
    asyncio.run(main())
