#!/usr/bin/env python3
"""
Scrape IRC sections and merge with existing data instead of overwriting.
"""
import json
import sys
from pathlib import Path
from scrape_cornell import CornellScraper

def load_existing_sections(output_path: Path) -> dict:
    """Load existing sections, return dict keyed by section number."""
    if not output_path.exists():
        return {}

    with open(output_path) as f:
        sections_list = json.load(f)

    # Convert to dict for easy merging
    return {int(s['section']): s for s in sections_list}

def scrape_and_merge(start: int, end: int, output_path: Path):
    """Scrape sections and merge with existing data."""
    print(f"🔥 SCRAPING AND MERGING §§{start}-{end} 🔥")

    # Load existing sections
    existing = load_existing_sections(output_path)
    print(f"Loaded {len(existing)} existing sections")

    # Scrape new sections
    scraper = CornellScraper()
    new_sections = []

    for section_num in range(start, end + 1):
        section_data = scraper.scrape_section(section_num)
        if section_data:
            new_sections.append(section_data)
            existing[section_num] = section_data  # Merge into dict

    print(f"Scraped {len(new_sections)} new sections")

    # Convert back to list sorted by section number
    merged_list = [existing[num] for num in sorted(existing.keys())]

    # Save merged data
    with open(output_path, 'w') as f:
        json.dump(merged_list, f, indent=2)

    print(f"✅ Total sections in file: {len(merged_list)}")
    return len(merged_list)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: scrape_and_merge.py START END")
        sys.exit(1)

    start = int(sys.argv[1])
    end = int(sys.argv[2])
    output_path = Path(__file__).parent.parent / 'data' / 'sections.json'

    total = scrape_and_merge(start, end, output_path)
    sys.exit(0)
