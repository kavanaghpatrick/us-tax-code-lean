#!/usr/bin/env python3
"""
IRC Section Dependency Analyzer

Parses all formalized IRC sections and builds a dependency graph showing
which sections reference others.

Output:
- dependency_graph.dot (GraphViz format)
- dependency_analysis.md (human-readable report)
"""

import re
from pathlib import Path
from collections import defaultdict, Counter
from typing import Dict, List, Set, Tuple

# Path to the TaxCode directory
TAX_CODE_DIR = Path(__file__).parent.parent / "src" / "TaxCode"


def extract_section_number(filename: str) -> int:
    """Extract section number from filename like 'Section103.lean'"""
    match = re.match(r"Section(\d+)\.lean", filename)
    if match:
        return int(match.group(1))
    return None


def find_section_references(content: str) -> Set[int]:
    """
    Find all IRC section references in the file content.

    Patterns matched:
    - §141, §149(b), §162(f)
    - Section 141, Section 149
    - IRC §141
    """
    references = set()

    # Pattern 1: §XXX or §XXX(...)
    pattern1 = r"§(\d+)(?:\([a-z0-9]+\))?"
    for match in re.finditer(pattern1, content):
        references.add(int(match.group(1)))

    # Pattern 2: Section XXX
    pattern2 = r"Section\s+(\d+)"
    for match in re.finditer(pattern2, content):
        references.add(int(match.group(1)))

    # Pattern 3: IRC §XXX
    pattern3 = r"IRC\s*§(\d+)"
    for match in re.finditer(pattern3, content):
        references.add(int(match.group(1)))

    return references


def build_dependency_graph() -> Tuple[Dict[int, Set[int]], Dict[int, str]]:
    """
    Build dependency graph from all .lean files.

    Returns:
        - graph: Dict mapping section number -> set of referenced sections
        - titles: Dict mapping section number -> section title
    """
    graph = defaultdict(set)
    titles = {}

    for lean_file in TAX_CODE_DIR.glob("Section*.lean"):
        section_num = extract_section_number(lean_file.name)
        if section_num is None:
            continue

        # Read file content
        content = lean_file.read_text()

        # Extract title from header comment (first few lines)
        title_match = re.search(r"IRC Section \d+ - (.+)", content)
        if title_match:
            titles[section_num] = title_match.group(1).strip()
        else:
            titles[section_num] = "Unknown"

        # Find references to other sections
        references = find_section_references(content)

        # Remove self-references
        references.discard(section_num)

        # Add to graph
        graph[section_num] = references

    return dict(graph), titles


def detect_cycles(graph: Dict[int, Set[int]]) -> List[List[int]]:
    """
    Detect circular reference chains using DFS.

    Returns list of cycles, where each cycle is a list of section numbers.
    """
    cycles = []
    visited = set()
    rec_stack = set()
    path = []

    def dfs(node: int) -> bool:
        """Returns True if cycle detected"""
        visited.add(node)
        rec_stack.add(node)
        path.append(node)

        for neighbor in graph.get(node, set()):
            if neighbor not in visited:
                if dfs(neighbor):
                    return True
            elif neighbor in rec_stack:
                # Found cycle - extract it from path
                cycle_start = path.index(neighbor)
                cycle = path[cycle_start:] + [neighbor]
                cycles.append(cycle)
                return True

        path.pop()
        rec_stack.remove(node)
        return False

    for node in graph.keys():
        if node not in visited:
            dfs(node)

    return cycles


def calculate_hub_sections(graph: Dict[int, Set[int]]) -> List[Tuple[int, int]]:
    """
    Calculate in-degree (number of sections referencing each section).

    Returns list of (section_num, in_degree) sorted by in_degree descending.
    """
    in_degree = Counter()

    for section, references in graph.items():
        for ref in references:
            in_degree[ref] += 1

    return in_degree.most_common()


def generate_dot_file(graph: Dict[int, Set[int]], titles: Dict[int, str], output_path: Path):
    """Generate GraphViz DOT file for visualization"""
    # Collect all sections (both formalized and referenced)
    all_sections = set(titles.keys())
    for refs in graph.values():
        all_sections.update(refs)

    with open(output_path, 'w') as f:
        f.write("digraph IRC_Dependencies {\n")
        f.write("  rankdir=LR;\n")
        f.write("  node [shape=box, style=rounded];\n\n")

        # Write nodes with labels
        for section in sorted(all_sections):
            title = titles.get(section, "Not formalized")
            # Truncate long titles
            short_title = title[:40] + "..." if len(title) > 40 else title
            label = f"§{section}\\n{short_title}"

            # Different styling for non-formalized sections
            if section not in titles:
                f.write(f'  s{section} [label="{label}", style="dashed,rounded", color="gray"];\n')
            else:
                f.write(f'  s{section} [label="{label}"];\n')

        f.write("\n")

        # Write edges
        for section, references in sorted(graph.items()):
            for ref in sorted(references):
                f.write(f"  s{section} -> s{ref};\n")

        f.write("}\n")


def generate_analysis_report(
    graph: Dict[int, Set[int]],
    titles: Dict[int, str],
    cycles: List[List[int]],
    hubs: List[Tuple[int, int]],
    output_path: Path
):
    """Generate human-readable analysis report"""
    with open(output_path, 'w') as f:
        f.write("# IRC Section Dependency Analysis\n\n")
        f.write(f"**Total Sections Analyzed**: {len(graph)}\n\n")
        f.write(f"**Total References**: {sum(len(refs) for refs in graph.values())}\n\n")

        # Summary statistics
        f.write("## Summary Statistics\n\n")

        # Sections with no outgoing references
        isolated = [s for s, refs in graph.items() if len(refs) == 0]
        f.write(f"**Sections with no outgoing references**: {len(isolated)}\n")
        if isolated:
            f.write(f"- {', '.join(f'§{s}' for s in sorted(isolated)[:20])}")
            if len(isolated) > 20:
                f.write(f" ... and {len(isolated) - 20} more")
            f.write("\n\n")

        # Sections with most outgoing references
        most_refs = sorted(graph.items(), key=lambda x: len(x[1]), reverse=True)[:10]
        f.write("**Sections with most outgoing references**:\n")
        for section, refs in most_refs:
            f.write(f"- §{section} ({titles.get(section, 'Unknown')}): {len(refs)} references\n")
        f.write("\n")

        # Hub sections (most referenced by others)
        f.write("## Hub Sections (Most Referenced)\n\n")
        f.write("These sections are referenced by many others, indicating they are foundational:\n\n")
        for section, count in hubs[:20]:
            title = titles.get(section, 'Not formalized')
            f.write(f"- **§{section}** ({title}): referenced by {count} sections\n")
        f.write("\n")

        # Circular references
        f.write("## Circular References\n\n")
        if cycles:
            f.write(f"**Warning**: {len(cycles)} circular reference chain(s) detected!\n\n")
            for i, cycle in enumerate(cycles, 1):
                f.write(f"### Cycle {i}\n\n")
                cycle_str = " → ".join(f"§{s}" for s in cycle)
                f.write(f"{cycle_str}\n\n")
                for section in set(cycle):
                    f.write(f"- §{section}: {titles.get(section, 'Unknown')}\n")
                f.write("\n")
        else:
            f.write("**No circular references detected** ✓\n\n")

        # Detailed dependency list
        f.write("## Detailed Dependencies\n\n")
        for section in sorted(graph.keys()):
            refs = graph[section]
            if refs:
                f.write(f"### §{section} - {titles.get(section, 'Unknown')}\n\n")
                f.write("References:\n")
                for ref in sorted(refs):
                    f.write(f"- §{ref}: {titles.get(ref, 'Unknown')}\n")
                f.write("\n")


def main():
    """Main entry point"""
    print("IRC Section Dependency Analyzer")
    print("=" * 50)
    print()

    # Build dependency graph
    print("Parsing .lean files...")
    graph, titles = build_dependency_graph()
    print(f"✓ Found {len(graph)} sections")
    print(f"✓ Found {sum(len(refs) for refs in graph.values())} total references")
    print()

    # Detect circular references
    print("Detecting circular references...")
    cycles = detect_cycles(graph)
    if cycles:
        print(f"⚠ Found {len(cycles)} circular reference chain(s)")
    else:
        print("✓ No circular references detected")
    print()

    # Calculate hub sections
    print("Calculating hub sections...")
    hubs = calculate_hub_sections(graph)
    if hubs:
        top_hub_num, top_hub_count = hubs[0]
        top_hub_title = titles.get(top_hub_num, "Not formalized")
        print(f"✓ Top hub: §{top_hub_num} ({top_hub_title}) - referenced {top_hub_count} times")
    print()

    # Generate outputs
    output_dir = Path(__file__).parent.parent / "analysis"
    output_dir.mkdir(exist_ok=True)

    dot_file = output_dir / "dependency_graph.dot"
    report_file = output_dir / "dependency_analysis.md"

    print("Generating outputs...")
    generate_dot_file(graph, titles, dot_file)
    print(f"✓ Created {dot_file}")

    generate_analysis_report(graph, titles, cycles, hubs, report_file)
    print(f"✓ Created {report_file}")
    print()

    print("Done! To visualize the graph, run:")
    print(f"  dot -Tpng {dot_file} -o dependency_graph.png")
    print(f"  open dependency_graph.png")


if __name__ == "__main__":
    main()
