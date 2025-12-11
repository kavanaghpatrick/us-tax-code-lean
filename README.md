# US Tax Code Formalization in Lean 4

Formalizing the US Internal Revenue Code (Title 26) using Lean 4 and Harmonic Aristotle.

## Overview

This project aims to create a machine-verified formalization of US tax law, starting with core definitions and progressively covering more complex tax code sections.

## Primary Source

[Cornell Law - 26 U.S. Code (Internal Revenue Code)](https://www.law.cornell.edu/uscode/text/26)

## Project Structure

```
src/
├── TaxCode/     # Formalized tax code sections
├── Common/      # Common definitions (currency, dates, entities)
└── Utils/       # Helper functions and utilities
docs/            # English descriptions and mappings
tests/           # Test cases and examples
scripts/         # Automation scripts
```

## Setup

1. Install Lean 4: https://leanprover.github.io/lean4/doc/setup.html
2. Install Aristotle: `pip3 install --upgrade aristotlelib`
3. Set API key: `export ARISTOTLE_API_KEY=your_key_here`

## Usage

Generate Lean proofs from English descriptions:

```bash
aristotle prove-from-file docs/your_section.md
```

Fill in proof sorries:

```bash
aristotle prove-from-file src/TaxCode/YourSection.lean
```

## Development Approach

1. **Start Small**: Core definitions (income, deductions, filing status)
2. **Cite Sources**: Every definition links to IRC section
3. **Test with Examples**: Real tax scenarios from IRS publications
4. **Incremental Complexity**: Simple sections → complex interdependencies

## Contributing

See [CLAUDE.md](CLAUDE.md) for development guidelines.

## License

TBD
