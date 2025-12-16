#!/usr/bin/env python3
"""Simple monitor for Aristotle queue status."""
import asyncio
import os
from datetime import datetime
from pathlib import Path
import shutil
import aristotlelib

LOG_FILE = Path('/tmp/aristotle_monitor.log')
TAXCODE_DIR = Path(__file__).parent.parent / 'src' / 'TaxCode'

def log(msg):
    line = f"[{datetime.now().strftime('%H:%M')}] {msg}"
    print(line)
    with open(LOG_FILE, 'a') as f:
        f.write(line + '\n')

async def monitor_cycle():
    aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

    result = await aristotlelib.Project.list_projects()
    if isinstance(result, tuple):
        projects, _ = result
    else:
        projects = result

    by_status = {}
    for p in projects:
        by_status[p.status.name] = by_status.get(p.status.name, 0) + 1

    # Count stubs
    stubs = len([f for f in TAXCODE_DIR.glob('Section*.lean')
                 if 'TODO: Add type definitions' in f.read_text()
                 and '_backup' not in f.name and '_aristotle' not in f.name])

    integrated = len(list(TAXCODE_DIR.glob('Section*_aristotle_output.lean')))

    ns = by_status.get('NOT_STARTED', 0)
    q = by_status.get('QUEUED', 0)
    ip = by_status.get('IN_PROGRESS', 0)
    c = by_status.get('COMPLETE', 0)

    log(f"📊 Stubs:{stubs} Int:{integrated} | Queue: NS:{ns} Q:{q} IP:{ip} C:{c}")

    # Integrate completed
    complete = [p for p in projects if p.status.name == 'COMPLETE']
    for p in complete:
        try:
            solution = await p.get_solution()
            if solution and solution.exists():
                content = solution.read_text()
                # Extract section name from content (look for IRC Section comment)
                import re
                match = re.search(r'IRC Section (\d+[A-Za-z]*)', content)
                if match:
                    section_num = match.group(1)
                    name = f"Section{section_num}"
                else:
                    # Fallback: try to find Section in filename
                    name = None
                    for f in TAXCODE_DIR.glob('Section*.lean'):
                        if '_' in f.name:
                            continue
                        stub_content = f.read_text()
                        if 'TODO: Add type definitions' in stub_content:
                            # Check if this stub matches the solution
                            if re.search(rf'Section {f.stem[7:]}', content):
                                name = f.stem
                                break

                if name:
                    output_file = TAXCODE_DIR / f"{name}_aristotle_output.lean"
                    if not output_file.exists():
                        shutil.copy(solution, output_file)
                        log(f"✅ Integrated: {name}")
        except Exception as e:
            log(f"Integration error: {e}")

async def main():
    log("=== Monitor Started ===")
    while True:
        try:
            await monitor_cycle()
        except Exception as e:
            log(f"Error: {e}")
        await asyncio.sleep(120)

if __name__ == '__main__':
    asyncio.run(main())
