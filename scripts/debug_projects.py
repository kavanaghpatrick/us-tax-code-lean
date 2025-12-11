#!/usr/bin/env python3
"""Debug project structure"""

import asyncio
import os
import aristotlelib

async def main():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    projects_raw = await aristotlelib.Project.list_projects()

    print(f"Type: {type(projects_raw)}")
    print(f"Length: {len(projects_raw)}")

    if len(projects_raw) > 0:
        print(f"\nFirst element type: {type(projects_raw[0])}")
        if isinstance(projects_raw[0], list):
            print(f"First element length: {len(projects_raw[0])}")
            if len(projects_raw[0]) > 0:
                print(f"\nFirst project:")
                print(repr(projects_raw[0][0]))
                print("\nFormatted:")
                print(projects_raw[0][0])

if __name__ == '__main__':
    asyncio.run(main())
