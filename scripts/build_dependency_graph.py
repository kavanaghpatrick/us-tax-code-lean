#!/usr/bin/env python3
"""
IRC Section Dependency Graph Builder

Analyzes scraped section data to build a directed acyclic graph (DAG)
of dependencies between sections.

Usage:
    python scripts/build_dependency_graph.py
"""

import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Set


class DependencyGraphBuilder:
    """Build dependency graph from scraped IRC sections."""

    def __init__(self, sections: List[Dict]):
        """Initialize with list of section data."""
        self.sections = {s['section']: s for s in sections}
        self.graph = defaultdict(set)  # section -> set of dependencies
        self.reverse_graph = defaultdict(set)  # section -> set of dependents

    def build_graph(self) -> Dict:
        """Build dependency graph from cross-references."""
        for section_num, section_data in self.sections.items():
            # Each referenced section is a dependency
            for ref in section_data.get('references', []):
                if ref in self.sections:
                    self.graph[section_num].add(ref)
                    self.reverse_graph[ref].add(section_num)

        return {
            'forward': {k: list(v) for k, v in self.graph.items()},
            'reverse': {k: list(v) for k, v in self.reverse_graph.items()}
        }

    def topological_sort(self) -> List[str]:
        """
        Perform topological sort to determine formalization order.

        Sections with no dependencies come first.
        Returns list of section numbers in dependency order.
        """
        # Kahn's algorithm
        in_degree = defaultdict(int)
        for section in self.sections:
            in_degree[section] = len(self.graph.get(section, set()))

        queue = [s for s in self.sections if in_degree[s] == 0]
        sorted_sections = []

        while queue:
            # Process sections with no remaining dependencies
            queue.sort(key=lambda s: int(s))  # Process in numerical order within same level
            section = queue.pop(0)
            sorted_sections.append(section)

            # Reduce in-degree for dependent sections
            for dependent in self.reverse_graph.get(section, []):
                in_degree[dependent] -= 1
                if in_degree[dependent] == 0:
                    queue.append(dependent)

        # Check for cycles
        if len(sorted_sections) != len(self.sections):
            print("Warning: Circular dependencies detected!", file=sys.stderr)
            missing = set(self.sections.keys()) - set(sorted_sections)
            print(f"Sections in cycle: {missing}", file=sys.stderr)

        return sorted_sections

    def analyze_dependencies(self) -> Dict:
        """Generate dependency statistics."""
        stats = {
            'total_sections': len(self.sections),
            'sections_with_dependencies': len(self.graph),
            'total_dependency_edges': sum(len(deps) for deps in self.graph.values()),
            'most_dependencies': None,
            'most_dependents': None
        }

        if self.graph:
            most_deps_section = max(self.graph.items(), key=lambda x: len(x[1]))
            stats['most_dependencies'] = {
                'section': most_deps_section[0],
                'count': len(most_deps_section[1]),
                'dependencies': list(most_deps_section[1])
            }

        if self.reverse_graph:
            most_deps_section = max(self.reverse_graph.items(), key=lambda x: len(x[1]))
            stats['most_dependents'] = {
                'section': most_deps_section[0],
                'count': len(most_deps_section[1]),
                'dependents': list(most_deps_section[1])
            }

        return stats


def main():
    # Load scraped sections
    sections_file = Path('data/sections.json')
    if not sections_file.exists():
        print(f"Error: {sections_file} not found. Run scrape_cornell.py first.", file=sys.stderr)
        return 1

    with open(sections_file) as f:
        sections = json.load(f)

    print(f"Loaded {len(sections)} sections")

    # Build dependency graph
    builder = DependencyGraphBuilder(sections)
    graph = builder.build_graph()

    # Topological sort
    sorted_sections = builder.topological_sort()

    # Analyze
    stats = builder.analyze_dependencies()

    # Output
    output = {
        'graph': graph,
        'topological_order': sorted_sections,
        'statistics': stats
    }

    output_file = Path('data/dependency_graph.json')
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\n=== Dependency Graph Statistics ===")
    print(f"Total sections: {stats['total_sections']}")
    print(f"Sections with dependencies: {stats['sections_with_dependencies']}")
    print(f"Total dependency edges: {stats['total_dependency_edges']}")

    if stats['most_dependencies']:
        md = stats['most_dependencies']
        print(f"\nSection with most dependencies: §{md['section']} ({md['count']} deps)")
        print(f"  Depends on: {md['dependencies'][:10]}{'...' if len(md['dependencies']) > 10 else ''}")

    if stats['most_dependents']:
        md = stats['most_dependents']
        print(f"\nMost referenced section: §{md['section']} ({md['count']} refs)")
        print(f"  Referenced by: {md['dependents'][:10]}{'...' if len(md['dependents']) > 10 else ''}")

    print(f"\nTopological order (first 20): {sorted_sections[:20]}")
    print(f"\nSaved to: {output_file}")

    return 0


if __name__ == '__main__':
    sys.exit(main())
