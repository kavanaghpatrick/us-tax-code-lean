#!/usr/bin/env python3
"""
Intelligent Aristotle Queue Manager

Monitors Aristotle API for available slots and automatically submits
sections when capacity is available. Respects 5-project concurrent limit.

Usage:
    python scripts/smart_queue.py --sections 1001,1011,1012,1221,1222
    python scripts/smart_queue.py --wave 1
    python scripts/smart_queue.py --resume  # Resume from saved queue
"""

import argparse
import asyncio
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Set, Dict
import aristotlelib


class SmartQueue:
    """Intelligent queue manager for Aristotle submissions."""

    def __init__(self, max_concurrent: int = 5, poll_interval: int = 30):
        self.max_concurrent = max_concurrent
        self.poll_interval = poll_interval
        self.project_root = Path(__file__).parent.parent
        self.queue_file = self.project_root / 'data' / 'smart_queue.json'

        # Initialize API
        aristotlelib.set_api_key(os.getenv('ARISTOTLE_API_KEY'))

        # Load or initialize queue state
        self.load_queue()

    def load_queue(self):
        """Load queue state from disk."""
        if self.queue_file.exists():
            with open(self.queue_file) as f:
                data = json.load(f)
                self.pending = data.get('pending', [])
                self.submitted = data.get('submitted', {})
                self.failed = data.get('failed', [])
        else:
            self.pending = []
            self.submitted = {}
            self.failed = []

    def save_queue(self):
        """Save queue state to disk."""
        self.queue_file.parent.mkdir(parents=True, exist_ok=True)
        with open(self.queue_file, 'w') as f:
            json.dump({
                'pending': self.pending,
                'submitted': self.submitted,
                'failed': self.failed,
                'last_updated': time.strftime('%Y-%m-%d %H:%M:%S')
            }, f, indent=2)

    def add_sections(self, sections: List[str]):
        """Add sections to the queue."""
        for section in sections:
            if section not in self.pending and section not in self.submitted:
                self.pending.append(section)
        self.save_queue()
        print(f"✓ Added {len(sections)} sections to queue")
        print(f"  Pending: {len(self.pending)}")
        print(f"  Submitted: {len(self.submitted)}")

    async def get_active_count(self) -> int:
        """Get count of currently active (QUEUED/IN_PROGRESS) projects."""
        try:
            projects_raw = await aristotlelib.Project.list_projects()

            if not projects_raw or len(projects_raw) < 1:
                return 0

            # Parse project list
            if isinstance(projects_raw[0], list):
                projects = projects_raw[0]
            else:
                projects = [projects_raw[0]]

            # Count active projects
            active_count = 0
            for proj_str in projects:
                if isinstance(proj_str, str):
                    if 'status: QUEUED' in proj_str or 'status: IN_PROGRESS' in proj_str:
                        active_count += 1

            return active_count

        except Exception as e:
            print(f"⚠️  Error checking status: {e}")
            return self.max_concurrent  # Assume full on error (be conservative)

    def submit_section(self, section: str) -> str:
        """
        Submit a single section to Aristotle.

        Returns:
            'success': Submitted successfully
            'rate_limit': Hit rate limit, retry later
            'failed': Permanent failure
        """
        aristotle_file = self.project_root / 'src' / 'TaxCode' / f'Section{section}_aristotle.lean'

        if not aristotle_file.exists():
            print(f"  ✗ {aristotle_file.name} not found (permanent failure)")
            self.failed.append(section)
            self.save_queue()
            return 'failed'

        try:
            cmd = [
                'aristotle', 'prove-from-file',
                str(aristotle_file),
                '--no-wait'
            ]

            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

            if result.returncode == 0:
                # Extract project UUID from output
                output = result.stderr + result.stdout
                # Look for "Created project <uuid>" in output
                import re
                match = re.search(r'Created project ([a-f0-9-]{36})', output)
                project_id = match.group(1) if match else 'unknown'

                self.submitted[section] = {
                    'project_id': project_id,
                    'submitted_at': time.strftime('%Y-%m-%d %H:%M:%S')
                }
                self.save_queue()
                print(f"  ✓ Submitted §{section} (project: {project_id[:8]}...)")
                return 'success'
            else:
                output = result.stderr + result.stdout

                # Check if it's a rate limit error
                if '429 Too Many Requests' in output or 'already have 5 projects' in output:
                    print(f"  ⏸️  Rate limit hit for §{section} - will retry")
                    return 'rate_limit'
                else:
                    print(f"  ✗ Failed to submit §{section} (permanent)")
                    print(f"    {result.stderr[:200]}")
                    self.failed.append(section)
                    self.save_queue()
                    return 'failed'

        except Exception as e:
            print(f"  ✗ Error submitting §{section}: {e}")
            # Conservative: treat as rate limit (will retry)
            return 'rate_limit'

    async def process_queue(self):
        """Main queue processing loop."""
        print("\n" + "="*80)
        print("SMART QUEUE MANAGER - STARTED")
        print("="*80)
        print(f"Max concurrent: {self.max_concurrent}")
        print(f"Poll interval: {self.poll_interval}s")
        print(f"Pending sections: {len(self.pending)}")
        print(f"Already submitted: {len(self.submitted)}")
        print("="*80 + "\n")

        iteration = 0

        while self.pending:
            iteration += 1

            # Check current active count
            active_count = await self.get_active_count()
            available_slots = self.max_concurrent - active_count

            print(f"\n[Iteration {iteration}] {time.strftime('%H:%M:%S')}")
            print(f"  Active projects: {active_count}/{self.max_concurrent}")
            print(f"  Available slots: {available_slots}")
            print(f"  Pending in queue: {len(self.pending)}")

            # Submit as many as we have slots for
            submitted_this_round = 0
            rate_limited = False

            while available_slots > 0 and self.pending and not rate_limited:
                section = self.pending[0]  # Peek at next

                print(f"\n  Attempting to submit §{section}...")
                result = self.submit_section(section)

                if result == 'success':
                    self.pending.pop(0)  # Remove from queue
                    submitted_this_round += 1
                    available_slots -= 1
                elif result == 'failed':
                    # Permanent failure - remove from queue (already added to failed list)
                    self.pending.pop(0)
                    # Available slots unchanged (didn't actually submit)
                elif result == 'rate_limit':
                    # Hit rate limit - keep in pending, stop trying this round
                    rate_limited = True
                    print(f"  ⏸️  Stopping submissions this round (rate limited)")
                    break

            if submitted_this_round > 0:
                print(f"\n  ✓ Submitted {submitted_this_round} section(s) this round")

            if rate_limited:
                print(f"  ℹ️  Will retry remaining {len(self.pending)} section(s) next iteration")

            # Check if done
            if not self.pending:
                print("\n" + "="*80)
                print("QUEUE EMPTY - ALL SECTIONS SUBMITTED!")
                print("="*80)
                print(f"Total submitted: {len(self.submitted)}")
                print(f"Total failed: {len(self.failed)}")
                if self.failed:
                    print(f"Failed sections: {', '.join(self.failed)}")
                break

            # Wait before next check
            print(f"\n  ⏳ Waiting {self.poll_interval}s before next check...")
            await asyncio.sleep(self.poll_interval)

    async def run(self):
        """Run the queue manager."""
        try:
            await self.process_queue()
        except KeyboardInterrupt:
            print("\n\n⚠️  Interrupted by user")
            print(f"Queue state saved. Run with --resume to continue.")
            self.save_queue()
        except Exception as e:
            print(f"\n\n✗ Error: {e}")
            import traceback
            traceback.print_exc()
            self.save_queue()


async def main():
    parser = argparse.ArgumentParser(description='Smart Aristotle queue manager')
    parser.add_argument('--sections', type=str, help='Comma-separated section numbers')
    parser.add_argument('--wave', type=int, help='Submit entire wave (1-5)')
    parser.add_argument('--resume', action='store_true', help='Resume from saved queue')
    parser.add_argument('--max-concurrent', type=int, default=4,
                       help='Max concurrent projects (default: 4, leaves 1 slot)')
    parser.add_argument('--poll-interval', type=int, default=30,
                       help='Seconds between status checks (default: 30)')
    parser.add_argument('--status', action='store_true', help='Show queue status and exit')

    args = parser.parse_args()

    queue = SmartQueue(max_concurrent=args.max_concurrent, poll_interval=args.poll_interval)

    if args.status:
        print("\n" + "="*80)
        print("QUEUE STATUS")
        print("="*80)
        print(f"Pending: {len(queue.pending)}")
        if queue.pending:
            print(f"  Next up: {', '.join(queue.pending[:5])}")
            if len(queue.pending) > 5:
                print(f"  ... and {len(queue.pending) - 5} more")
        print(f"\nSubmitted: {len(queue.submitted)}")
        print(f"Failed: {len(queue.failed)}")
        if queue.failed:
            print(f"  {', '.join(queue.failed)}")
        print("="*80 + "\n")
        return 0

    # Add sections to queue
    if args.sections:
        sections = [s.strip() for s in args.sections.split(',')]
        queue.add_sections(sections)
    elif args.wave:
        # Import wave definitions from batch_formalize
        from batch_formalize import WAVES
        if args.wave in WAVES:
            sections = [str(s) for s in WAVES[args.wave]]
            queue.add_sections(sections)
        else:
            print(f"✗ Invalid wave number: {args.wave}")
            return 1
    elif not args.resume:
        parser.print_help()
        return 1

    # Run the queue
    await queue.run()

    return 0


if __name__ == '__main__':
    try:
        exit_code = asyncio.run(main())
        sys.exit(exit_code)
    except KeyboardInterrupt:
        print("\n\nInterrupted by user")
        sys.exit(130)
