#!/usr/bin/env python3
"""
Cornell Law USC Title 26 Scraper

Scrapes IRC sections from Cornell Law website and outputs structured JSON.

Usage:
    python scripts/scrape_cornell.py --section 61
    python scripts/scrape_cornell.py --range 1-100
    python scripts/scrape_cornell.py --all
"""

import argparse
import json
import re
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup


class CornellScraper:
    """Scraper for Cornell Law USC Title 26."""

    BASE_URL = "https://www.law.cornell.edu/uscode/text/26"

    def __init__(self, delay: float = 1.0):
        """Initialize scraper with rate limiting delay."""
        self.delay = delay
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'US-Tax-Code-Lean-Formalizer/1.0 (Educational Research)'
        })

    def scrape_section(self, section_num: str) -> Optional[Dict]:
        """
        Scrape a single IRC section.

        Args:
            section_num: Section number (e.g., "61", "1401")

        Returns:
            Dict with section data or None if error
        """
        url = f"{self.BASE_URL}/{section_num}"
        print(f"Scraping §{section_num}: {url}")

        try:
            response = self.session.get(url, timeout=30)
            response.raise_for_status()
        except requests.RequestException as e:
            print(f"Error fetching §{section_num}: {e}", file=sys.stderr)
            return None

        soup = BeautifulSoup(response.content, 'html.parser')

        # Extract section title
        title_elem = soup.find('h1', class_='title')
        title = title_elem.get_text(strip=True) if title_elem else f"Section {section_num}"
        title = title.replace(f"26 U.S. Code § {section_num} - ", "")

        # Extract section text - try multiple selectors
        content_div = (
            soup.find('div', id='documentContent') or
            soup.find('div', class_='field-item') or
            soup.find('article') or
            soup.find('main')
        )

        if not content_div:
            # Try finding any div with substantial text content
            all_divs = soup.find_all('div')
            for div in all_divs:
                text = div.get_text(strip=True)
                if len(text) > 500 and f'§ {section_num}' in text or f'§{section_num}' in text:
                    content_div = div
                    break

        if not content_div:
            print(f"Warning: No content found for §{section_num}", file=sys.stderr)
            # Debug: show what we found
            print(f"Debug: Available divs: {[d.get('class', d.get('id', 'unnamed')) for d in soup.find_all('div')[:10]]}", file=sys.stderr)
            return None

        # Extract subsections
        subsections = self._extract_subsections(content_div)

        # Extract cross-references
        references = self._extract_references(content_div)

        # Build section data
        section_data = {
            'section': section_num,
            'title': title,
            'url': url,
            'subsections': subsections,
            'references': references,
            'text': content_div.get_text(separator='\n', strip=True)
        }

        # Rate limiting
        time.sleep(self.delay)

        return section_data

    def _extract_subsections(self, soup: BeautifulSoup) -> List[Dict]:
        """Extract subsection structure from section HTML."""
        subsections = []

        # Look for subsection markers (a), (b), (c), etc.
        for para in soup.find_all(['p', 'div'], class_=lambda c: c and 'subsection' in c):
            subsec_marker = para.find('span', class_='subsection')
            if subsec_marker:
                marker = subsec_marker.get_text(strip=True)
                text = para.get_text(strip=True)
                subsections.append({
                    'marker': marker,
                    'text': text
                })

        return subsections

    def _extract_references(self, soup: BeautifulSoup) -> List[str]:
        """
        Extract cross-references to other IRC sections.

        Looks for patterns like:
        - "section 62"
        - "§ 1401"
        - "sections 61 and 63"
        """
        text = soup.get_text()
        references = set()

        # Pattern 1: "section NNN"
        for match in re.finditer(r'\bsection\s+(\d+)', text, re.IGNORECASE):
            references.add(match.group(1))

        # Pattern 2: "§ NNN" or "§NNN"
        for match in re.finditer(r'§\s*(\d+)', text):
            references.add(match.group(1))

        # Pattern 3: Links to other sections
        for link in soup.find_all('a', href=True):
            match = re.search(r'/uscode/text/26/(\d+)', link['href'])
            if match:
                references.add(match.group(1))

        return sorted(references, key=int)

    def scrape_range(self, start: int, end: int) -> List[Dict]:
        """Scrape a range of sections."""
        sections = []
        for num in range(start, end + 1):
            section_data = self.scrape_section(str(num))
            if section_data:
                sections.append(section_data)
        return sections

    def scrape_all_subtitles(self) -> Dict[str, List[Dict]]:
        """
        Scrape all subtitles of Title 26.

        WARNING: This will make thousands of requests. Use sparingly.
        """
        # TODO: Implement subtitle-by-subtitle scraping
        # For now, manual ranges based on known structure:
        # Subtitle A: §§ 1-1564 (Income Taxes)
        # Subtitle B: §§ 2001-2801 (Estate/Gift Taxes)
        # etc.
        raise NotImplementedError("Use --range for batch scraping")


def main():
    parser = argparse.ArgumentParser(description='Scrape Cornell Law USC Title 26')
    parser.add_argument('--section', type=str, help='Single section to scrape (e.g., 61)')
    parser.add_argument('--range', type=str, help='Range of sections (e.g., 1-100)')
    parser.add_argument('--all', action='store_true', help='Scrape all sections (USE WITH CAUTION)')
    parser.add_argument('--output', type=str, default='data/sections.json', help='Output JSON file')
    parser.add_argument('--delay', type=float, default=1.0, help='Delay between requests (seconds)')

    args = parser.parse_args()

    scraper = CornellScraper(delay=args.delay)
    sections = []

    if args.section:
        section_data = scraper.scrape_section(args.section)
        if section_data:
            sections = [section_data]

    elif args.range:
        match = re.match(r'(\d+)-(\d+)', args.range)
        if not match:
            print("Error: Range must be in format START-END (e.g., 1-100)", file=sys.stderr)
            return 1
        start, end = int(match.group(1)), int(match.group(2))
        sections = scraper.scrape_range(start, end)

    elif args.all:
        print("Warning: --all will scrape thousands of sections. Use --range instead.", file=sys.stderr)
        return 1

    else:
        parser.print_help()
        return 1

    # Save output
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, 'w') as f:
        json.dump(sections, f, indent=2)

    print(f"\nScraped {len(sections)} sections → {output_path}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
