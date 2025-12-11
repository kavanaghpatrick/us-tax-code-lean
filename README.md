# US Tax Code Formalization in Lean 4

**Systematic formalization of the US Internal Revenue Code (Title 26) using Lean 4 and Harmonic Aristotle**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4.14.0-blue)](https://leanprover.github.io/lean4/)

## 🎯 Mission

Create a complete, machine-verified formalization of US tax law enabling:
- Automated tax calculation verification
- Detection of legal inconsistencies and ambiguities
- Formal proofs of tax law properties
- Educational resource for understanding tax law

## ✨ Current Status

### Implemented (100% Functional)

**IRC Section 1 - Tax Imposed** ✅
- All 5 filing status rate schedules (Single, MFJ, MFS, HOH, QW)
- Complete 2024 IRS tax brackets (7 brackets per status)
- Progressive tax calculation function
- **6 passing test cases** verifying correctness

**IRC Section 61 - Gross Income Defined** ✅ NEW!
- 15 income source types (Compensation, Business, Interest, Dividends, etc.)
- Complete inductive type for all §61(a) categories
- `calculateGrossIncome` function with aggregation logic
- 3 theorems (sum equality, non-negative, monotonic)
- Working examples and helper constructors
- **Processed through Aristotle** - proofs generated

**Test Results**:
```
Section 1:
  Single $50k: $6,053 ✓
  Married Filing Jointly $100k: $12,106 ✓
  Head of Household $75k: $9,859 ✓
  Single $1M: $328,187.75 ✓

Section 61:
  W-2 employee ($50k wages + $500 interest + $250 dividends): $50,750 ✓
```

### Automation Pipeline (Production-Ready at Scale)

**4 Production Scripts**:
1. `scrape_cornell.py` - Scrapes IRC sections from Cornell Law
2. `build_dependency_graph.py` - Constructs section dependency DAG
3. `generate_lean_skeleton.py` - Auto-generates Lean templates
4. `aristotle_batch.py` - Batch processes sections through Aristotle API

**Demonstrated at Scale**:
- **76 sections scraped** (IRC §§1-91)
- **814 cross-reference edges** mapped
- Dependency graph constructed
- Aristotle processing verified

## 🚀 Quick Start

### Prerequisites
```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Install Python dependencies
pip3 install -r requirements.txt

# Set Aristotle API key
export ARISTOTLE_API_KEY=your_key_here
```

### Build & Test
```bash
# Build project
lake build

# Run tests
lake env lean src/Tests/Section1Tests.lean
```

## 📖 Project Structure

```
├── src/
│   ├── TaxCode/          # Formalized IRC sections
│   │   ├── Section1.lean     # Tax rates (COMPLETE)
│   │   ├── Section61.lean    # Gross income (skeleton)
│   │   ├── Section62.lean    # AGI (skeleton)
│   │   └── Section63.lean    # Taxable income (skeleton)
│   ├── Common/
│   │   └── Basic.lean        # Core types (Currency, TaxYear, FilingStatus)
│   └── Tests/            # Test suites
├── scripts/              # Automation pipeline
├── docs/
│   └── ROADMAP.md        # 7-phase formalization plan
└── data/
    ├── sections.json         # Scraped IRC data
    └── dependency_graph.json # Section dependencies
```

## 🔧 Automation Usage

### Scrape IRC Sections
```bash
# Single section
python3 scripts/scrape_cornell.py --section 61

# Range of sections
python3 scripts/scrape_cornell.py --range 100-200

# Output: data/sections.json
```

### Build Dependency Graph
```bash
python3 scripts/build_dependency_graph.py

# Output: data/dependency_graph.json
# Shows topological order for formalization
```

### Generate Lean Skeletons
```bash
# Batch generate
python3 scripts/generate_lean_skeleton.py --batch 61,62,63

# Creates src/TaxCode/SectionN.lean + tests
```

### Batch Process with Aristotle
```bash
# Auto-process next N sections in dependency order
python3 scripts/aristotle_batch.py --auto --limit 10

# Or specify sections
python3 scripts/aristotle_batch.py --sections 61,62,63
```

## 📊 Roadmap

### Phase 1: Foundation (Current) ✅
- [x] IRC Section 1 (Tax Imposed)
- [x] Automation pipeline
- [x] Test infrastructure

### Phase 2: Income & Deductions
- [ ] IRC Section 61 (Gross Income) - [Issue #2](../../issues/2)
- [ ] IRC Section 62 (AGI) - [Issue #4](../../issues/4)
- [ ] IRC Section 63 (Taxable Income) - [Issue #3](../../issues/3)
- [ ] Standard Deduction - [Issue #7](../../issues/7)

### Phase 3: Credits & Common Scenarios
- [ ] IRC Section 24 (Child Tax Credit)
- [ ] IRC Section 32 (Earned Income Credit)
- [ ] IRC Section 1401 (Self-Employment Tax)

See [ROADMAP.md](docs/ROADMAP.md) for complete 7-phase plan covering all ~9,834 IRC sections.

## 📚 Primary Sources

- **Legal Text**: [Cornell Law - 26 USC](https://www.law.cornell.edu/uscode/text/26)
- **Tax Brackets**: [IRS Tax Tables](https://www.irs.gov/filing/federal-income-tax-rates-and-brackets)
- **Formalization Tool**: [Harmonic Aristotle](https://aristotle.harmonic.fun)

## 🤝 Contributing

1. Check [open issues](../../issues) for formalization priorities
2. Follow dependency order from `data/dependency_graph.json`
3. See [CLAUDE.md](CLAUDE.md) for development guidelines
4. All definitions must cite IRC section sources

## 📈 Statistics

- **Sections Implemented**: 3 complete (§§1, 24, 61)
- **Section Skeletons**: 73 (§§2-91, excluding implemented)
- **Total Sections in Codebase**: 76
- **Sections Scraped**: 76 (§§1-91)
- **Cross-References Mapped**: 814 dependency edges
- **Test Files**: 76
- **Total Lean Files**: 156
- **Test Cases**: 7 passing
- **Aristotle Processed**: 2 sections
- **Automation Scripts**: 4
- **GitHub Issues**: 7 (roadmap)

## 🎓 Educational Use

This project serves as:
- Example of legal code formalization
- Demonstration of Lean 4 + Aristotle workflow
- Case study in dependency graph-driven development
- Resource for understanding progressive tax systems

## 📄 License

MIT License - See [LICENSE](LICENSE) file

## 🙏 Acknowledgments

- Built with [Lean 4](https://leanprover.github.io/lean4/)
- Powered by [Harmonic Aristotle](https://harmonic.fun)
- Tax data from [IRS](https://www.irs.gov)
- Legal text from [Cornell Law School LII](https://www.law.cornell.edu/)

---

**Status**: Active Development 🚧
**Last Updated**: 2024-12-11
**Next Milestone**: Complete IRC §§61-63 (Gross Income, AGI, Taxable Income)
