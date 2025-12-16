#!/usr/bin/env python3
"""
Grok Loophole Investigator

Takes loopholes found by the distributed system and uses Grok to investigate
their real-world implications, abuse potential, and economic impact.
"""

import json
import subprocess
import os
from pathlib import Path
from typing import List, Dict

PROJECT_ROOT = Path(__file__).parent.parent


def investigate_with_grok(loophole: Dict) -> str:
    """Use Grok to investigate a loophole's real-world implications."""

    # Prepare the prompt for Grok
    prompt = f"""REAL-WORLD TAX LOOPHOLE INVESTIGATION

You are a tax law expert investigating potential loopholes in the US Internal Revenue Code.

**LOOPHOLE DETAILS:**
- Section Pair: {loophole['file1']} ↔ {loophole['file2']}
- Confidence: {loophole['confidence']:.2f}
- Type: Potential contradiction or exploitable interaction

**YOUR TASK:**

1. **Identify the Specific Provisions**:
   - What tax rules are in these IRC sections?
   - What do these sections normally govern?

2. **Analyze the Interaction**:
   - How might these sections interact in a real tax scenario?
   - What creates the potential loophole?
   - Is this a true contradiction or an intentional exception?

3. **Real-World Exploitation**:
   - Who could exploit this (individuals, corporations, trusts)?
   - What's a concrete example scenario?
   - What transaction structure would maximize benefit?

4. **Economic Impact**:
   - Potential tax revenue loss per exploit
   - Scale if widely used (thousands of taxpayers)
   - Estimated total annual impact to US Treasury

5. **Legal Status**:
   - Has this been addressed by IRS rulings or court cases?
   - Is this a known planning strategy?
   - Legal vs. illegal exploitation

6. **Real-World Examples** (if known):
   - Has this been used in practice?
   - Any famous cases or public disclosures?
   - Current prevalence in tax planning

**OUTPUT FORMAT:**

# Loophole: {loophole['file1']} ↔ {loophole['file2']}

## Summary
[One paragraph executive summary]

## IRC Sections Involved
- **{loophole['file1']}**: [What it governs]
- **{loophole['file2']}**: [What it governs]

## The Loophole Mechanism
[2-3 paragraphs explaining how it works]

## Exploitation Scenario
[Concrete example with numbers]

## Economic Impact
- Per-taxpayer benefit: $X - $Y
- Estimated users: Z taxpayers
- Annual Treasury loss: $A million - $B million

## Legal Status
[Current legal/regulatory status]

## Real-World Use
[Known cases, prevalence, expert opinion]

## Recommendation
[Close loophole? IRS guidance needed? Already addressed?]

---

Be specific, use actual tax law knowledge, and cite real cases where possible.
Focus on PRACTICAL implications, not theoretical edge cases.
"""

    # Create JSON request for Grok
    request = {
        "messages": [
            {
                "role": "system",
                "content": "You are an expert tax attorney and economist specializing in IRC loopholes and tax planning strategies. Provide specific, actionable analysis with real-world examples."
            },
            {
                "role": "user",
                "content": prompt
            }
        ],
        "model": "grok-2-1212",
        "temperature": 0.1,
        "max_tokens": 4000
    }

    # Write request to temp file
    request_file = '/tmp/grok_loophole_request.json'
    with open(request_file, 'w') as f:
        json.dump(request, f)

    # Call Grok API
    try:
        result = subprocess.run(
            [
                'curl', '-X', 'POST',
                'https://api.x.ai/v1/chat/completions',
                '-H', f'Authorization: Bearer {os.environ.get("GROK_API_KEY")}',
                '-H', 'Content-Type: application/json',
                '-d', f'@{request_file}'
            ],
            capture_output=True,
            text=True,
            timeout=120
        )

        if result.returncode == 0:
            response = json.loads(result.stdout)
            if 'choices' in response and len(response['choices']) > 0:
                return response['choices'][0]['message']['content']
            else:
                return f"ERROR: Unexpected Grok response format: {result.stdout[:500]}"
        else:
            return f"ERROR: Grok API call failed: {result.stderr[:500]}"

    except Exception as e:
        return f"ERROR: {str(e)}"


def main():
    # Load loopholes from the distributed system output
    loophole_file = PROJECT_ROOT / "loopholes_found.json"

    if not loophole_file.exists():
        print("No loopholes file found. Run distributed_loophole_finder.py first.")
        return

    with open(loophole_file) as f:
        data = json.load(f)
        loopholes = data.get('contradictions', [])

    if not loopholes:
        print("No loopholes found to investigate.")
        return

    print(f"Found {len(loopholes)} loopholes to investigate")
    print(f"Investigating top 5 with Grok...")
    print("=" * 60)
    print()

    # Investigate top 5 loopholes
    results = []
    for i, loophole in enumerate(loopholes[:5], 1):
        print(f"[{i}/5] Investigating: {loophole['file1']} ↔ {loophole['file2']}")
        print(f"       Confidence: {loophole['confidence']:.2f}")

        investigation = investigate_with_grok(loophole)

        results.append({
            'loophole': loophole,
            'investigation': investigation
        })

        print(f"       ✓ Complete ({len(investigation)} chars)")
        print()

    # Save results
    output_file = PROJECT_ROOT / "GROK_LOOPHOLE_INVESTIGATIONS.md"
    with open(output_file, 'w') as f:
        f.write("# Grok Real-World Loophole Investigations\n\n")
        f.write(f"**Date**: {subprocess.check_output(['date']).decode().strip()}\n")
        f.write(f"**Investigator**: Grok (xAI)\n")
        f.write(f"**Loopholes Analyzed**: {len(results)}\n\n")
        f.write("---\n\n")

        for i, result in enumerate(results, 1):
            f.write(f"# Investigation {i}/5\n\n")
            f.write(result['investigation'])
            f.write("\n\n---\n\n")

    print(f"✓ Investigations saved to: {output_file}")
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Loopholes investigated:  {len(results)}")
    print(f"Total analysis:          {sum(len(r['investigation']) for r in results):,} characters")
    print(f"Output file:             {output_file}")


if __name__ == '__main__':
    main()
