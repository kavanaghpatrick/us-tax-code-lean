#!/usr/bin/env python3
"""
Aristotle Batch Processor

Processes multiple IRC sections through Aristotle API in dependency order.

Usage:
    python scripts/aristotle_batch.py --sections 61,62,63
    python scripts/aristotle_batch.py --auto --limit 10
"""

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional


class AristotleBatchProcessor:
    """Batch process Lean files through Aristotle API."""

    def __init__(self, api_key: Optional[str] = None, delay: float = 30.0):
        """
        Initialize batch processor.

        Args:
            api_key: Aristotle API key (defaults to ARISTOTLE_API_KEY env var)
            delay: Delay between API calls in seconds
        """
        self.api_key = api_key or os.getenv('ARISTOTLE_API_KEY')
        if not self.api_key:
            raise ValueError("ARISTOTLE_API_KEY not found in environment")
        self.delay = delay
        self.progress_file = Path('data/aristotle_progress.json')
        self.load_progress()

    def load_progress(self):
        """Load processing progress from file."""
        if self.progress_file.exists():
            with open(self.progress_file) as f:
                self.progress = json.load(f)
        else:
            self.progress = {
                'completed': [],
                'failed': [],
                'project_uuids': {}
            }

    def save_progress(self):
        """Save processing progress to file."""
        self.progress_file.parent.mkdir(parents=True, exist_ok=True)
        with open(self.progress_file, 'w') as f:
            json.dump(self.progress, f, indent=2)

    def process_section(self, section_num: str) -> bool:
        """
        Process a single section through Aristotle.

        Args:
            section_num: IRC section number

        Returns:
            True if successful, False otherwise
        """
        lean_file = Path(f'src/TaxCode/Section{section_num}_aristotle.lean')

        if not lean_file.exists():
            print(f"Error: {lean_file} not found. Generate skeleton first.", file=sys.stderr)
            return False

        print(f"\n{'='*60}")
        print(f"Processing IRC §{section_num}")
        print(f"File: {lean_file}")
        print(f"{'='*60}")

        # Run Aristotle
        cmd = [
            'aristotle',
            'prove-from-file',
            '--api-key', self.api_key,
            str(lean_file)
        ]

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300  # 5 minute timeout
            )

            print(result.stdout)

            if result.returncode != 0:
                print(f"Aristotle failed for §{section_num}:", file=sys.stderr)
                print(result.stderr, file=sys.stderr)
                self.progress['failed'].append(section_num)
                self.save_progress()
                return False

            # Extract project UUID from output
            uuid_match = None
            for line in result.stdout.split('\n'):
                if 'project' in line.lower() and '-' in line:
                    # Try to extract UUID pattern
                    import re
                    uuid_pattern = r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}'
                    match = re.search(uuid_pattern, line)
                    if match:
                        uuid_match = match.group(0)
                        break

            if uuid_match:
                self.progress['project_uuids'][section_num] = uuid_match

            # Mark as completed
            self.progress['completed'].append(section_num)
            self.save_progress()

            # Verify it builds
            print(f"\nVerifying build...")
            build_result = subprocess.run(['lake', 'build'], capture_output=True, text=True)

            if build_result.returncode != 0:
                print(f"Warning: Build failed after processing §{section_num}", file=sys.stderr)
                print(build_result.stderr, file=sys.stderr)
                # Don't mark as failed, just warn
            else:
                print(f"✓ §{section_num} built successfully")

            return True

        except subprocess.TimeoutExpired:
            print(f"Timeout processing §{section_num}", file=sys.stderr)
            self.progress['failed'].append(section_num)
            self.save_progress()
            return False

        except Exception as e:
            print(f"Error processing §{section_num}: {e}", file=sys.stderr)
            self.progress['failed'].append(section_num)
            self.save_progress()
            return False

    def process_batch(self, section_nums: List[str]) -> Dict:
        """
        Process multiple sections.

        Args:
            section_nums: List of section numbers to process

        Returns:
            Dict with success/failure counts
        """
        results = {
            'total': len(section_nums),
            'succeeded': 0,
            'failed': 0,
            'skipped': 0
        }

        for i, section_num in enumerate(section_nums, 1):
            print(f"\n[{i}/{results['total']}] Processing §{section_num}")

            # Skip if already completed
            if section_num in self.progress['completed']:
                print(f"Skipping §{section_num} (already completed)")
                results['skipped'] += 1
                continue

            success = self.process_section(section_num)

            if success:
                results['succeeded'] += 1
            else:
                results['failed'] += 1

            # Rate limiting delay
            if i < len(section_nums):  # Don't delay after last section
                print(f"\nWaiting {self.delay}s before next section...")
                time.sleep(self.delay)

        return results

    def process_auto(self, limit: int = 10) -> Dict:
        """
        Automatically process sections from dependency graph.

        Args:
            limit: Maximum number of sections to process

        Returns:
            Results dict
        """
        dep_graph_file = Path('data/dependency_graph.json')
        if not dep_graph_file.exists():
            print("Error: dependency_graph.json not found. Run build_dependency_graph.py first.", file=sys.stderr)
            return {'error': 'Missing dependency graph'}

        with open(dep_graph_file) as f:
            dep_data = json.load(f)

        topo_order = dep_data['topological_order']

        # Filter out already-completed sections
        remaining = [s for s in topo_order if s not in self.progress['completed']][:limit]

        print(f"Processing next {len(remaining)} sections in dependency order:")
        print(f"  Sections: {remaining}")

        return self.process_batch(remaining)


def main():
    parser = argparse.ArgumentParser(description='Batch process IRC sections through Aristotle')
    parser.add_argument('--sections', type=str, help='Comma-separated section numbers')
    parser.add_argument('--auto', action='store_true', help='Auto-process from dependency graph')
    parser.add_argument('--limit', type=int, default=10, help='Max sections for --auto mode')
    parser.add_argument('--delay', type=float, default=30.0, help='Delay between API calls (seconds)')

    args = parser.parse_args()

    processor = AristotleBatchProcessor(delay=args.delay)

    if args.sections:
        section_nums = [s.strip() for s in args.sections.split(',')]
        results = processor.process_batch(section_nums)

    elif args.auto:
        results = processor.process_auto(limit=args.limit)

    else:
        parser.print_help()
        return 1

    # Print summary
    print(f"\n{'='*60}")
    print(f"Batch Processing Complete")
    print(f"{'='*60}")
    print(f"Total: {results.get('total', 0)}")
    print(f"Succeeded: {results.get('succeeded', 0)}")
    print(f"Failed: {results.get('failed', 0)}")
    print(f"Skipped: {results.get('skipped', 0)}")

    return 0 if results.get('failed', 0) == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
