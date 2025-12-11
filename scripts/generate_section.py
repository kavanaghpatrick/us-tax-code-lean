#!/usr/bin/env python3
"""
Generate Lean code for a single IRC section using Claude API.
"""

import argparse
import json
import os
from pathlib import Path
from anthropic import Anthropic

def generate_section(section_num: str, level: int = 2):
    """Generate Lean code for a section."""

    # Load scraped data
    data_file = Path(__file__).parent.parent / 'data' / 'sections.json'
    with open(data_file) as f:
        sections_list = json.load(f)

    # Find the section (data is a list of dicts)
    section_num_int = int(section_num)
    section = None
    for s in sections_list:
        if s.get('section') == section_num_int:
            section = s
            break

    if not section:
        print(f"Section {section_num} not found in scraped data")
        return

    # Truncate text to fit in prompt (keep first 3000 chars for context)
    text = section['text']
    if len(text) > 3000:
        text = text[:3000] + "... [truncated for length]"

    # Prepare prompt
    prompt = f"""You are a Lean 4 expert formalizing US Tax Code.

Convert the following IRC section to executable Lean 4 code:

**Section**: {section_num}
**Title**: {section['title']}

**Text**:
{text}

Requirements:
1. Import Common.Basic for Currency, FilingStatus, TaxYear types
2. Define structures for any entities mentioned (income types, deductions, etc.)
3. Implement calculation functions (executable, no 'sorry')
4. Use Currency type (Int in cents) for all monetary amounts
5. Reference other sections as needed (e.g., import TaxCode.Section62)
6. Add comments explaining complex logic
7. Follow Lean 4 best practices

Context - Already defined in Common.Basic:
```lean
def Currency := Int  -- Cents
inductive FilingStatus where
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
structure TaxYear where
  year : Nat
```

Output ONLY valid Lean 4 code, no explanations.
Start with imports, then define types, then functions."""

    # Call Claude API
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("ERROR: ANTHROPIC_API_KEY not set")
        return None

    client = Anthropic(api_key=api_key)

    print(f"Generating §{section_num} - {section['title']}...")
    print(f"Using Claude Opus 4...")

    try:
        response = client.messages.create(
            model="claude-opus-4-20250514",
            max_tokens=4000,
            messages=[{"role": "user", "content": prompt}]
        )

        code = response.content[0].text

        # Save to file
        output_file = Path(__file__).parent.parent / 'src' / 'TaxCode' / f'Section{section_num}.lean'
        output_file.parent.mkdir(parents=True, exist_ok=True)

        with open(output_file, 'w') as f:
            f.write(code)

        print(f"✓ Generated: {output_file}")
        print(f"  Tokens: {response.usage.input_tokens} in, {response.usage.output_tokens} out")
        print(f"  Model: {response.model}")

        return output_file

    except Exception as e:
        print(f"✗ Error: {e}")
        return None

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate Lean code for IRC section')
    parser.add_argument('--section', required=True, help='Section number (e.g., 61)')
    parser.add_argument('--level', type=int, default=2, help='Generation level (1-3)')

    args = parser.parse_args()

    output_file = generate_section(args.section, args.level)

    if output_file:
        print(f"\nNext step: Compile with 'lean {output_file}'")
