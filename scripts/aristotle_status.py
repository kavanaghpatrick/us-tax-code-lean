#!/usr/bin/env python3
"""
Check status of Aristotle projects.

Lists all projects and their current status (QUEUED, IN_PROGRESS, COMPLETE, FAILED).
"""

import aristotlelib
import os
import asyncio
import sys
from datetime import datetime


async def main():
    """Fetch and display Aristotle project status."""
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    print("Fetching Aristotle projects...\n")
    projects_raw = await aristotlelib.Project.list_projects()

    # Parse the nested structure (first element contains project list)
    if not projects_raw or len(projects_raw) < 1:
        print("No projects found")
        return

    # Split the first element by newline blocks
    project_data = str(projects_raw[0]).split('\n\n')

    projects = []
    for block in project_data:
        if 'Project ' in block:
            lines = block.split('\n')
            proj = {}
            for line in lines:
                if line.startswith('Project '):
                    proj['uuid'] = line.replace('Project ', '').strip()
                elif line.startswith('file name: '):
                    proj['file'] = line.replace('file name: ', '').strip()
                elif line.startswith('status: '):
                    proj['status'] = line.replace('status: ', '').strip()
                elif line.startswith('created: '):
                    proj['created'] = line.replace('created: ', '').strip()
                elif line.startswith('last updated: '):
                    proj['updated'] = line.replace('last updated: ', '').strip()
                elif line.startswith('percent complete: '):
                    proj['percent'] = line.replace('percent complete: ', '').strip()
            if proj:
                projects.append(proj)

    # Categorize
    active = [p for p in projects if p.get('status') in ['QUEUED', 'IN_PROGRESS', 'PENDING_RETRY']]
    complete = [p for p in projects if p.get('status') == 'COMPLETE']
    failed = [p for p in projects if p.get('status') == 'FAILED']

    print(f"{'='*80}")
    print(f"ARISTOTLE PROJECT STATUS")
    print(f"{'='*80}\n")

    print(f"📊 SUMMARY:")
    print(f"  Active:   {len(active)}")
    print(f"  Complete: {len(complete)}")
    print(f"  Failed:   {len(failed)}")
    print(f"  Total:    {len(projects)}\n")

    if active:
        print(f"{'='*80}")
        print(f"🚀 ACTIVE PROJECTS ({len(active)})")
        print(f"{'='*80}\n")
        for p in active:
            print(f"UUID:    {p.get('uuid', 'N/A')}")
            print(f"File:    {p.get('file', 'N/A')}")
            print(f"Status:  {p.get('status', 'N/A')}")
            if 'percent' in p:
                print(f"Progress: {p['percent']}%")
            print(f"Created: {p.get('created', 'N/A')}")
            print(f"Updated: {p.get('updated', 'N/A')}")
            print("-" * 80)

    if failed:
        print(f"\n{'='*80}")
        print(f"❌ FAILED PROJECTS ({len(failed)})")
        print(f"{'='*80}\n")
        for p in failed:
            print(f"UUID:    {p.get('uuid', 'N/A')}")
            print(f"File:    {p.get('file', 'N/A')}")
            print(f"Created: {p.get('created', 'N/A')}")
            print("-" * 80)

    if '--show-complete' in sys.argv and complete:
        print(f"\n{'='*80}")
        print(f"✅ RECENTLY COMPLETED ({min(10, len(complete))} of {len(complete)})")
        print(f"{'='*80}\n")
        for p in complete[:10]:
            print(f"UUID: {p.get('uuid', 'N/A')}")
            print(f"File: {p.get('file', 'N/A')}")
            print(f"Updated: {p.get('updated', 'N/A')}")
            print("-" * 80)


if __name__ == '__main__':
    asyncio.run(main())
