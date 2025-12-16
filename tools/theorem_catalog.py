#!/usr/bin/env python3
"""
Theorem Catalog Generator
Extracts and catalogs all proven theorems from Lean formalization files.
"""

import os
import re
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass
from typing import Optional

@dataclass
class Theorem:
    name: str
    section: str
    file_path: str
    line_number: int
    signature: str
    category: str
    is_lemma: bool = False

def categorize_theorem(name: str, signature: str) -> str:
    """Categorize theorem by its property type."""
    name_lower = name.lower()
    sig_lower = signature.lower()

    # Non-negativity / Non-positivity
    if any(x in name_lower for x in ['nonneg', 'nonpos', 'positive', 'negative']):
        return "Bounds"
    if '≥ 0' in signature or '>= 0' in signature or '≤ 0' in signature:
        return "Bounds"

    # Monotonicity
    if 'monoton' in name_lower or 'increasing' in name_lower or 'decreasing' in name_lower:
        return "Monotonicity"

    # Eligibility / Validity
    if any(x in name_lower for x in ['eligible', 'valid', 'qualif', 'applies', 'excluded']):
        return "Eligibility"

    # Bounds / Limits
    if any(x in name_lower for x in ['bounded', 'limit', '_le_', '_ge_', 'max', 'min', 'cap']):
        return "Bounds"

    # Equivalence / Equality
    if any(x in name_lower for x in ['_eq_', 'equal', 'equiv', 'same']):
        return "Equivalence"

    # Examples / Calculations
    if any(x in name_lower for x in ['example', 'calc', 'correct', 'value']):
        return "Examples"

    # Zero conditions
    if 'zero' in name_lower or '= 0' in signature:
        return "Zero Conditions"

    # Linear / Additive properties
    if any(x in name_lower for x in ['linear', 'additive', 'additivity']):
        return "Linearity"

    # Implications
    if 'implies' in name_lower or '→' in signature:
        return "Implications"

    return "Other"

def extract_theorems(file_path: Path) -> list[Theorem]:
    """Extract all theorems and lemmas from a Lean file."""
    theorems = []

    # Get section name from filename
    section = file_path.stem
    if section.endswith('_aristotle_output'):
        section = section.replace('_aristotle_output', '')

    try:
        content = file_path.read_text()
    except:
        return []

    lines = content.split('\n')

    # Pattern for theorem/lemma declarations
    theorem_pattern = re.compile(r'^(theorem|lemma)\s+(\w+)\s*(.*?)(?::\s*=|:=|where|\{)', re.MULTILINE | re.DOTALL)

    for i, line in enumerate(lines, 1):
        line_stripped = line.strip()

        # Check for theorem or lemma start
        if line_stripped.startswith('theorem ') or line_stripped.startswith('lemma '):
            is_lemma = line_stripped.startswith('lemma ')

            # Extract name
            match = re.match(r'^(theorem|lemma)\s+(\w+)', line_stripped)
            if match:
                name = match.group(2)

                # Get the signature (rest of declaration)
                # Look for the signature until := or where
                signature_lines = [line_stripped]
                j = i
                while j < len(lines) and ':=' not in signature_lines[-1] and ' := ' not in ' '.join(signature_lines):
                    if j < len(lines):
                        next_line = lines[j].strip()
                        if next_line and not next_line.startswith('--'):
                            signature_lines.append(next_line)
                        if ':=' in next_line or 'where' in next_line:
                            break
                    j += 1

                signature = ' '.join(signature_lines)
                # Truncate at := or where
                signature = re.split(r'\s*:=\s*|\s+where\s+', signature)[0]

                category = categorize_theorem(name, signature)

                theorems.append(Theorem(
                    name=name,
                    section=section,
                    file_path=str(file_path),
                    line_number=i,
                    signature=signature,
                    category=category,
                    is_lemma=is_lemma
                ))

    return theorems

def generate_catalog(src_dir: Path) -> dict:
    """Generate full theorem catalog."""
    all_theorems = []

    # Find all Lean files
    for lean_file in sorted(src_dir.glob('*.lean')):
        # Skip backup and intermediate files
        if '_backup' in lean_file.name or '_aristotle.lean' in lean_file.name:
            continue
        theorems = extract_theorems(lean_file)
        all_theorems.extend(theorems)

    # Organize by category
    by_category = defaultdict(list)
    for t in all_theorems:
        by_category[t.category].append(t)

    # Organize by section
    by_section = defaultdict(list)
    for t in all_theorems:
        by_section[t.section].append(t)

    return {
        'all': all_theorems,
        'by_category': dict(by_category),
        'by_section': dict(by_section),
        'stats': {
            'total_theorems': sum(1 for t in all_theorems if not t.is_lemma),
            'total_lemmas': sum(1 for t in all_theorems if t.is_lemma),
            'categories': {k: len(v) for k, v in by_category.items()},
            'sections_with_theorems': len(by_section)
        }
    }

def generate_markdown(catalog: dict, output_path: Path):
    """Generate THEOREMS.md documentation."""
    lines = []
    stats = catalog['stats']

    lines.append("# Proven Theorems Catalog")
    lines.append("")
    lines.append("Auto-generated catalog of all proven properties in the US Tax Code formalization.")
    lines.append("")

    # Stats section
    lines.append("## Summary Statistics")
    lines.append("")
    lines.append(f"- **Total Theorems**: {stats['total_theorems']}")
    lines.append(f"- **Total Lemmas**: {stats['total_lemmas']}")
    lines.append(f"- **Sections with Proofs**: {stats['sections_with_theorems']}")
    lines.append("")

    # Category breakdown
    lines.append("### By Category")
    lines.append("")
    lines.append("| Category | Count |")
    lines.append("|----------|-------|")
    for cat, count in sorted(stats['categories'].items(), key=lambda x: -x[1]):
        lines.append(f"| {cat} | {count} |")
    lines.append("")

    # Theorems by category
    lines.append("## Theorems by Category")
    lines.append("")

    for category in sorted(catalog['by_category'].keys()):
        theorems = catalog['by_category'][category]
        lines.append(f"### {category} ({len(theorems)})")
        lines.append("")

        for t in sorted(theorems, key=lambda x: x.section):
            kind = "lemma" if t.is_lemma else "theorem"
            # Clean up signature for display
            sig_display = t.signature
            if len(sig_display) > 100:
                sig_display = sig_display[:97] + "..."
            lines.append(f"- **{t.name}** ({t.section})")
            lines.append(f"  - `{sig_display}`")
        lines.append("")

    # Quick reference by section
    lines.append("## Quick Reference by Section")
    lines.append("")
    lines.append("| Section | Theorems | Lemmas |")
    lines.append("|---------|----------|--------|")

    for section in sorted(catalog['by_section'].keys(), key=lambda x: int(re.search(r'\d+', x).group()) if re.search(r'\d+', x) else 0):
        theorems = catalog['by_section'][section]
        t_count = sum(1 for t in theorems if not t.is_lemma)
        l_count = sum(1 for t in theorems if t.is_lemma)
        if t_count > 0 or l_count > 0:
            lines.append(f"| {section} | {t_count} | {l_count} |")
    lines.append("")

    lines.append("---")
    lines.append("*Generated by `tools/theorem_catalog.py`*")

    output_path.write_text('\n'.join(lines))
    print(f"Generated {output_path}")

def main():
    src_dir = Path(__file__).parent.parent / 'src' / 'TaxCode'
    output_path = Path(__file__).parent.parent / 'THEOREMS.md'

    print("Extracting theorems...")
    catalog = generate_catalog(src_dir)

    print(f"Found {catalog['stats']['total_theorems']} theorems and {catalog['stats']['total_lemmas']} lemmas")
    print(f"Across {catalog['stats']['sections_with_theorems']} sections")
    print("\nCategory breakdown:")
    for cat, count in sorted(catalog['stats']['categories'].items(), key=lambda x: -x[1]):
        print(f"  {cat}: {count}")

    print("\nGenerating THEOREMS.md...")
    generate_markdown(catalog, output_path)

if __name__ == '__main__':
    main()
