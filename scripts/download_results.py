#!/usr/bin/env python3
"""
Download results for all completed Aristotle projects.
"""

import asyncio
import os
from pathlib import Path
import aristotlelib

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    print("\n" + "="*80)
    print("DOWNLOADING ARISTOTLE RESULTS")
    print("="*80 + "\n")

    downloads_dir = Path.home() / 'Downloads'
    downloads_dir.mkdir(exist_ok=True)

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

        completed = [p for p in projects if str(p.status.value if hasattr(p.status, 'value') else p.status) == 'COMPLETE']

        print(f"Found {len(completed)} completed projects\n")

        for proj in completed:
            uuid = proj.project_id
            file_name = proj.file_name or 'unknown'
            result_file = downloads_dir / f"{uuid}-output.lean"

            if result_file.exists():
                print(f"  ✓ Already have {file_name} ({uuid[:8]}...)")
            else:
                print(f"  ⬇️  Downloading {file_name} ({uuid[:8]}...)")
                try:
                    # Use the project object we already have
                    result = await proj.get_solution()

                    if result:
                        # Result might be a Path object or string
                        if isinstance(result, Path):
                            result = result.read_text()
                        elif not isinstance(result, str):
                            result = str(result)

                        result_file.write_text(result)
                        print(f"      ✓ Saved to {result_file.name}")
                    else:
                        print(f"      ⚠️  No output available yet")

                except Exception as e:
                    print(f"      ✗ Error: {e}")

        print("\n" + "="*80)
        print("DOWNLOAD COMPLETE")
        print("="*80 + "\n")

    except Exception as e:
        print(f"✗ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == '__main__':
    asyncio.run(main())
