#!/usr/bin/env python3
"""
Quick Aristotle API status checker.
Shows all active projects and their statuses.
"""

import asyncio
import os
import aristotlelib

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    print("\n" + "="*80)
    print("ARISTOTLE PROJECT STATUS")
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

        # Count by status
        status_counts = {}
        active_projects = []

        for proj_str in projects:
            if isinstance(proj_str, str):
                # Extract UUID and status
                lines = proj_str.split('\n')
                uuid = lines[0].replace('Project ', '').strip()

                status = "UNKNOWN"
                file_name = "unknown"

                for line in lines:
                    if line.startswith('status:'):
                        status = line.replace('status:', '').strip()
                    elif line.startswith('file name:'):
                        file_name = line.replace('file name:', '').strip()

                status_counts[status] = status_counts.get(status, 0) + 1

                # Track active projects
                if status in ['QUEUED', 'IN_PROGRESS']:
                    active_projects.append({
                        'uuid': uuid,
                        'status': status,
                        'file': file_name
                    })

        # Print status summary
        print("Status Summary:")
        for status, count in sorted(status_counts.items()):
            print(f"  {status}: {count}")

        # Print active projects
        if active_projects:
            print(f"\nActive Projects ({len(active_projects)}):")
            for proj in active_projects:
                print(f"  [{proj['status']}] {proj['file']}")
                print(f"      UUID: {proj['uuid'][:8]}...")
        else:
            print("\n✓ No active projects (all slots available)")

        print("\n" + "="*80)

    except Exception as e:
        print(f"✗ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == '__main__':
    asyncio.run(main())
