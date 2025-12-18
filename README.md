# US Tax Code Formalization in Lean 4

**Complete formalization of the US Internal Revenue Code (Title 26) using Lean 4 and Harmonic Aristotle**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4.14.0-blue)](https://leanprover.github.io/lean4/)
[![Sections](https://img.shields.io/badge/Sections-752-brightgreen)]()
[![Theorems](https://img.shields.io/badge/Theorems-607-blue)]()

## Mission

Create a complete, machine-verified formalization of US tax law enabling:
- Automated tax calculation verification
- Detection of legal inconsistencies and ambiguities
- Formal proofs of tax law properties
- Educational resource for understanding tax law

---

## Current Status (Dec 18, 2025)

### Formalization Progress

**752 IRC sections formalized** covering the core of the US Internal Revenue Code.

| Metric | Value |
|--------|-------|
| **Main Section Files** | 752 |
| **Aristotle Output Files** | 703 |
| **Total Lean Files** | 1,455 |
| **Lines of Lean Code** | 537,400 |
| **Theorems & Lemmas** | 607 |
| **Remaining `sorry`** | 17 |

### Key Achievements

- **Broad IRC Coverage**: 752 sections of Title 26 formalized
- **Formal Proofs**: 607 theorems and lemmas proven
- **Automated Pipeline**: Processed via Aristotle API with batch automation
- **Quality Tooling**: Loophole detection and contradiction analysis tools
- **Near-Complete**: 17 `sorry` statements remain in complex sections

---

## Architecture

```
src/
  TaxCode/                    # 752 formalized IRC sections
    Section1.lean             # Tax rates
    Section1_aristotle_output.lean
    Section61.lean            # Gross income
    Section61_aristotle_output.lean
    ...
  Common/
    Basic.lean                # Core type definitions
    Currency.lean             # Currency handling
  Utils/                      # Helper functions

tools/                        # 20 analysis tools
  safe_loophole_finder.py     # Single-threaded contradiction detector
  loophole_classifier.py      # Pattern classification
  grok_loophole_investigator.py
  contradiction_detector.py
  dependency_analyzer.py

scripts/                      # 22 automation scripts
  process_remaining_stubs.py
  process_oversized_stubs.py
  process_final_19.py
  monitor_queue.py

tests/                        # 5 test files
docs/                         # Documentation
data/                         # Scraped IRC data, queue state
```

---

## Core Types

```lean
-- Currency amounts (IRC calculations)
def Currency := Int

-- Tax years (modern income tax era)
structure TaxYear where
  year : Nat
  h_valid : year >= 1913
  deriving DecidableEq

-- Filing status (IRC Section 1)
inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited
```

---

## Tools

### Loophole Finder

Single-threaded contradiction detector that analyzes all sections:

```bash
# Run full analysis (safe, single-threaded)
python3 tools/safe_loophole_finder.py

# With progress resumption
python3 tools/safe_loophole_finder.py --resume

# Skip pairwise checks (faster)
python3 tools/safe_loophole_finder.py --skip-contradictions
```

**Detection Patterns**:
- Type definition inconsistencies (Currency, FilingStatus, TaxYear)
- Numeric threshold conflicts
- Deprecated function references
- Incomplete implementations (sorry, TODO, admit)
- Overlapping boolean conditions
- isTaxExempt vs isTaxable conflicts

### Dependency Analyzer

```bash
python3 tools/dependency_analyzer.py
```

---

## Quick Start

### Prerequisites

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Install Python dependencies
pip3 install aristotlelib psutil

# Set Aristotle API key (for new formalizations)
export ARISTOTLE_API_KEY=your_key_here
```

### Build

```bash
# Build entire project
lake build

# Check specific section
lake build TaxCode.Section61
```

### Verify

```bash
# Run loophole analysis
python3 tools/safe_loophole_finder.py --skip-contradictions

# Check for incomplete proofs
grep -r "sorry" src/TaxCode/*.lean
```

---

## Statistics

| Category | Count |
|----------|-------|
| IRC Sections Formalized | 752 |
| Lines of Lean Code | 537,400 |
| Proven Theorems/Lemmas | 607 |
| Test Files | 5 |
| Processing Scripts | 22 |
| Analysis Tools | 20 |

---

## Formalization Process

Each IRC section was processed through:

1. **Scraping**: Cornell Law IRC text extracted
2. **Stub Generation**: Lean skeleton with type signatures
3. **Aristotle Submission**: INFORMAL mode proof search
4. **Integration**: Output files merged into project
5. **Build Verification**: `lake build` validation
6. **Quality Analysis**: Loophole finder checks

### Batch Processing

Large files were handled with truncation strategies:
- Editorial Notes removed (non-legal content)
- Amendments sections truncated
- 600-line limit for very large sections
- Retry logic for API failures

---

## Key Sections

### Foundational (Core Tax Concepts)

| Section | Description | Status |
|---------|-------------|--------|
| 1 | Tax Rates & Brackets | Complete |
| 61 | Gross Income Defined | Complete |
| 62 | Adjusted Gross Income | Complete |
| 63 | Taxable Income | Complete |
| 151 | Personal Exemptions | Complete |
| 152 | Dependent Defined | Complete |

### Deductions & Credits

| Section | Description | Status |
|---------|-------------|--------|
| 162 | Business Expenses | Complete |
| 163 | Interest Deductions | Complete |
| 164 | Taxes | Complete |
| 165 | Losses | Complete |
| 167 | Depreciation | Complete |
| 170 | Charitable Contributions | Complete |

### Capital Gains & Property

| Section | Description | Status |
|---------|-------------|--------|
| 1001 | Gain/Loss Calculation | Complete |
| 1012 | Cost Basis | Complete |
| 1221 | Capital Asset Defined | Complete |
| 1231 | Business Property | Complete |

### Corporate & Business

| Section | Description | Status |
|---------|-------------|--------|
| 11 | Corporate Tax Rate | Complete |
| 301 | Corporate Distributions | Complete |
| 401 | Qualified Plans | Complete |
| 482 | Transfer Pricing | Complete |

### Sections with Remaining Work

| Section | Issue |
|---------|-------|
| 103 | Complex municipal bond rules |
| 168 | Accelerated depreciation |
| 453 | Installment sales |
| 704 | Partnership allocations |
| 831 | Insurance company rules |
| 951-956 | Controlled foreign corps |
| 1297 | PFIC definitions |

---

## Resources

### Documentation
- [CLAUDE.md](CLAUDE.md) - Project-specific development rules
- [analysis/](analysis/) - Loophole analysis results

### Primary Sources
- **Legal Text**: [Cornell Law - 26 USC](https://www.law.cornell.edu/uscode/text/26)
- **Tax Brackets**: [IRS Tax Tables](https://www.irs.gov/filing/federal-income-tax-rates-and-brackets)
- **Formalization Tool**: [Harmonic Aristotle](https://aristotle.harmonic.fun)

### Technical
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

---

## Contributing

1. Check [open issues](../../issues) for enhancement opportunities
2. Run `lake build` to verify changes compile
3. Run `safe_loophole_finder.py` to check for new issues
4. Include test cases with `#eval` examples
5. Cite IRC section sources in comments

---

## Acknowledgments

- Built with [Lean 4](https://leanprover.github.io/lean4/)
- Powered by [Harmonic Aristotle](https://harmonic.fun)
- Tax data from [IRS](https://www.irs.gov)
- Legal text from [Cornell Law School LII](https://www.law.cornell.edu/)

---

**Status**: Near-Complete (17 `sorry` remaining)
**Last Updated**: 2025-12-18
**Total Sections**: 752
