#!/usr/bin/env python3
"""
Comprehensive Aristotle Status Checker
Maps all projects to sections and shows what was proved.
"""

import asyncio
import os
import re
from pathlib import Path
import aristotlelib

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    print("\n" + "="*80)
    print("COMPREHENSIVE ARISTOTLE STATUS")
    print("="*80 + "\n")

    try:
        projects_raw = await aristotlelib.Project.list_projects()

        if not projects_raw or len(projects_raw) < 1:
            print("No projects found.")
            return

        # Parse project list
        if isinstance(projects_raw[0], list):
            projects = projects_raw[0]
        else:
            projects = [projects_raw[0]]

        print(f"Total projects: {len(projects)}\n")

        # Track results by section
        by_section = {}
        by_status = {}

        for proj in projects:
            # Projects are Project objects
            uuid = proj.project_id
            status = str(proj.status.value) if hasattr(proj.status, 'value') else str(proj.status)
            file_name = proj.file_name or 'unknown'

            # Extract section number from filename
            section_match = re.search(r'Section(\d+)', file_name)
            section_num = section_match.group(1) if section_match else 'unknown'

            # Track by status
            by_status[status] = by_status.get(status, 0) + 1

            # Track by section
            if section_num not in by_section:
                by_section[section_num] = []

            by_section[section_num].append({
                'uuid': uuid,
                'status': status,
                'file': file_name
            })

        # Print status summary
        print("Status Summary:")
        for status in sorted(by_status.keys()):
            count = by_status[status]
            print(f"  {status}: {count}")

        print("\n" + "-"*80)
        print("BY SECTION:")
        print("-"*80 + "\n")

        # Print by section, sorted numerically
        section_nums = []
        for s in by_section.keys():
            if s != 'unknown':
                try:
                    section_nums.append(int(s))
                except:
                    pass

        for section_num in sorted(section_nums):
            section = str(section_num)
            projects = by_section[section]

            print(f"§{section}:")
            for proj in projects:
                status_icon = "✓" if proj['status'] == 'COMPLETE' else "⏳" if proj['status'] in ['QUEUED', 'IN_PROGRESS'] else "✗"
                print(f"  {status_icon} [{proj['status']}] {proj['uuid'][:8]}...")

                # If completed, try to get the result
                if proj['status'] == 'COMPLETE':
                    downloads_dir = Path.home() / 'Downloads'
                    result_file = downloads_dir / f"{proj['uuid']}-output.lean"

                    if result_file.exists():
                        content = result_file.read_text()

                        if 'The following was proved by Aristotle:' in content:
                            # Extract theorems
                            proved_section = content.split('The following was proved by Aristotle:')[1]
                            proved_section = proved_section.split('-/')[0]

                            theorems = re.findall(r'- theorem (\w+)', proved_section)
                            if theorems:
                                print(f"      PROVED: {', '.join(theorems)}")
                        elif 'failed to load' in content:
                            # Extract error
                            error_match = re.search(r'failed to load[^.]*\.\s*([^\n]+)', content)
                            if error_match:
                                error = error_match.group(1).strip()
                                print(f"      ERROR: {error}")
                    else:
                        print(f"      (Result file not found)")
            print()

        # Unknown sections
        if 'unknown' in by_section:
            print("Unknown/Other Files:")
            for proj in by_section['unknown']:
                print(f"  [{proj['status']}] {proj['file']}")
                print(f"      UUID: {proj['uuid'][:8]}...")
            print()

        print("="*80)

        # Summary stats
        completed = sum(1 for projects in by_section.values() for p in projects if p['status'] == 'COMPLETE')
        total_sections = len([s for s in by_section.keys() if s != 'unknown'])

        print(f"\nTotal IRC Sections: {total_sections}")
        print(f"Completed Projects: {completed}/{len(projects)}")
        print(f"Active Slots: {by_status.get('QUEUED', 0) + by_status.get('IN_PROGRESS', 0)}/5")
        print()

    except Exception as e:
        print(f"✗ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == '__main__':
    asyncio.run(main())
