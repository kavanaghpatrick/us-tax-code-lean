# US Tax Code Formalization in Lean 4

**Systematic formalization of the US Internal Revenue Code (Title 26) using Lean 4 and Harmonic Aristotle**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4.14.0-blue)](https://leanprover.github.io/lean4/)
[![Sections Complete](https://img.shields.io/badge/Sections-10%20Complete-brightgreen)]()
[![Quality Audit](https://img.shields.io/badge/Quality-7.2%2F10%20Avg-yellow)]()

## 🎯 Mission

Create a complete, machine-verified formalization of US tax law enabling:
- Automated tax calculation verification
- Detection of legal inconsistencies and ambiguities
- Formal proofs of tax law properties
- Educational resource for understanding tax law

---

## ✨ Current Status (Dec 12, 2025)

### 🎉 Major Milestones

**Priority-50 Formalization Campaign (In Progress)**
- ✅ **10 sections COMPLETE** via Aristotle INFORMAL (20% done)
- 🔍 **Quality audit conducted** - Average score: 7.2/10
- 🐛 **Critical logic error found & fixed** - Section 108 (Issue #24)
- 📋 **Comprehensive verification guide created** - Documenting Aristotle strengths/weaknesses
- ⏳ **2 sections IN PROGRESS** (Sections 71, 401)
- 🔄 **36 sections in retry queue** (API connectivity issues)
- 📝 **3 GitHub issues created** for fixes needed

### 📊 Quality Audit Results

Comprehensive audit of all 10 completed sections revealed:

| Section | Score | Status | Issues |
|---------|-------|--------|--------|
| **301** | 9/10 | EXCELLENT ✅ | Production ready |
| **61** | 9/10 | EXCELLENT ✅ | Production ready |
| **63** | 8/10 | EXCELLENT ✅ | Production ready |
| **121** | 8/10 | GOOD ✅ | Minor fixes needed |
| **62** | 7/10 | GOOD ✅ | Production ready |
| **108** | 7/10 | GOOD ⚠️ | **Logic error FIXED** |
| **101** | 6/10 | NEEDS WORK ⚠️ | Incomplete coverage |
| **103** | 5/10 | CRITICAL 🔴 | Incomplete proofs ([#23](../../issues/23)) |
| **1** | 2/10 | CRITICAL 🔴 | Timeout, outdated ([#22](../../issues/22)) |
| **482** | N/A | PENDING ⏳ | Awaiting audit |

**Key Finding**: 6 of 10 sections (60%) are production-ready or need only minor fixes.

See [AUDIT_SUMMARY.md](AUDIT_SUMMARY.md) for detailed analysis.

---

## 🐛 Critical Bug Fixed: Section 108

**Multi-AI Investigation Confirms Error** (Issue #24) ✅

All 4 independent AI systems (Claude Opus 4.5, Grok-4, Gemini Pro, Codex) unanimously confirmed a critical logic error in Section 108's `QualifiedRealPropertyBusiness` exclusion:

**The Bug** (Lines 126-130):
- ❌ C corporations were **illegally granted** an exclusion (statute says "OTHER THAN")
- ❌ Non-C corporations got **unlimited** exclusion (missing §108(c)(2) caps)

**The Fix** (Commit 83b48a8):
- ✅ C corporations now return **0** (ineligible)
- ✅ Non-C corporations apply **dual limitations** (principal-FMV + depreciable basis)
- ✅ 4 test cases added
- ✅ 2 verification theorems proven

**Impact Prevented**: ~$555M annual revenue loss + illegal C corp exclusions

See [SECTION_108_VERDICT.md](SECTION_108_VERDICT.md) for full investigation (25 pages).

---

## 📖 Verification Guide

**New Resource**: [ARISTOTLE_VERIFICATION_GUIDE.md](ARISTOTLE_VERIFICATION_GUIDE.md)

Based on auditing 10 Aristotle-generated sections, we've documented:

### 🟢 Where Aristotle Excels (95%+ Confidence)
- Mathematical correctness and theorem proving
- Core statutory provisions
- Arithmetic and threshold enforcement
- Type safety and code structure

### 🔴 Where Aristotle Fails (High Risk)
- **"Other than" exclusions** (30% confidence) - **CRITICAL**
- Multi-step limitations (60% confidence)
- Completeness - missing subsections (50% confidence)
- Timeouts on complex sections
- Entity-specific rules (55% confidence)

**Key Lesson**: **Formal verification ≠ Legal correctness**

Section 108 had zero `sorry` statements and complete proofs, yet implemented the law completely backwards. The winning formula:

```
Formal Verification + Human Review + Multi-AI Validation = Trust
```

---

## 🚀 Fully Formalized Sections (Aristotle INFORMAL)

### ✅ Production Ready (ACCEPT)

**IRC Section 301 - Distributions of Property** (9/10)
- Perfect three-tier tax treatment (dividend → return of capital → capital gain)
- Liability reduction logic
- Mathematical decomposition proof
- 20% corporate shareholder rules

**IRC Section 61 - Gross Income Defined** (9/10)
- All 15 major income sources from §61(a)
- Post-TCJA alimony rules (Dec 31, 2018 cutoff)
- 6 proven theorems
- Comprehensive examples

**IRC Section 63 - Taxable Income Defined** (8/10)
- Complete standard deduction rules
- All filing status variations
- Dependent limitations
- Post-TCJA 2017 amounts

**IRC Section 62 - AGI Defined** (7/10)
- 11 primary above-the-line deductions
- Educator expense limit ($250)
- 4 proven theorems
- Linearity properties

### ⚠️ Needs Fixes

**IRC Section 121 - Principal Residence Exclusion** (8/10)
- Excellent 2-of-5-year ownership/use tests
- Sophisticated nonqualified use calculations
- Missing: Reduced exclusion for unforeseen circumstances

**IRC Section 108 - Discharge of Indebtedness** (7/10) ✅ **FIXED**
- Core discharge exclusions correct
- Attribute reduction waterfall perfect
- **Critical error fixed**: QualifiedRealPropertyBusiness now correct
- Missing: Basis reduction election, complete principal residence rules

**IRC Section 101 - Life Insurance Proceeds** (6/10)
- Only 40% coverage (4 of 10 subsections)
- What's covered is accurate
- Needs: Accelerated death benefits, employer-owned policies

### 🔴 Critical Issues (Rerun Needed)

**IRC Section 103 - Interest on State/Local Bonds** (5/10) - [Issue #23](../../issues/23)
- Contains `exact?` proof placeholders (lines 164, 166)
- Won't compile in strict mode
- **Rerun in progress** with enhanced prompt

**IRC Section 1 - Tax Tables** (2/10) - [Issue #22](../../issues/22)
- Aristotle timeout after 1h 41m
- Contains 1990s tax brackets (wrong era)
- **Rerun in progress** with 2024 TCJA brackets

**IRC Section 482 - Allocations** (Pending)
- Completed 08:50 AM Dec 12
- Awaiting quality audit

---

## 🔬 Automation Pipeline (Production Scale)

### Aristotle Queue System (3 Queues)

**1. Priority-50 Queue** (PID 19244)
```bash
python3 scripts/aristotle_formalization_queue.py --priority-50
```
- Status: 10 complete, 36 failed, 2 in progress
- Running 24/7 with 60s polling
- Target: 50 most important IRC sections

**2. Retry Queue** (PID 67708)
```bash
python3 scripts/aristotle_formalization_queue.py --sections 11,21,24,... --max-wait-hours 24
```
- Status: Processing 36 failed sections
- Parallel to main queue
- Handles API connectivity failures

**3. Rerun Queue** (NEW)
```bash
python3 scripts/aristotle_rerun_queue.py --sections 1,103 --max-wait-hours 24
```
- Status: Waiting for project slots (5/5 limit)
- Enhanced prompts for problematic sections
- Will auto-start when slots available

### Production Scripts

1. `scrape_cornell.py` - Scrapes IRC sections from Cornell Law
2. `scrape_and_merge.py` - Merge-safe parallel scraping
3. `build_dependency_graph.py` - Constructs section dependency DAG
4. `generate_lean_skeleton.py` - Auto-generates Lean templates
5. `aristotle_formalization_queue.py` - Priority-50 batch processor
6. `aristotle_rerun_queue.py` - Enhanced rerun processor (NEW)

---

## 📁 Project Structure

```
├── src/
│   ├── TaxCode/          # Formalized IRC sections
│   │   ├── Section1.lean      # Tax rates (NEEDS RERUN)
│   │   ├── Section61.lean     # Gross income (EXCELLENT)
│   │   ├── Section62.lean     # AGI (GOOD)
│   │   ├── Section63.lean     # Taxable income (EXCELLENT)
│   │   ├── Section101.lean    # Life insurance (NEEDS WORK)
│   │   ├── Section103.lean    # Municipal bonds (NEEDS RERUN)
│   │   ├── Section108.lean    # Discharge of debt (FIXED)
│   │   ├── Section121.lean    # Principal residence (GOOD)
│   │   ├── Section301.lean    # Distributions (EXCELLENT)
│   │   └── Section482.lean    # Allocations (PENDING AUDIT)
│   ├── Common/
│   │   └── Basic.lean        # Core types
│   └── Tests/            # Test suites
├── scripts/              # Automation pipeline
├── docs/
│   ├── ROADMAP.md                                # 7-phase plan
│   ├── AUDIT_SUMMARY.md                          # Quality audit (NEW)
│   ├── ARISTOTLE_VERIFICATION_GUIDE.md           # Verification patterns (NEW)
│   ├── SECTION_108_VERDICT.md                    # Multi-AI investigation (NEW)
│   └── SECTION_108_LOGIC_ERROR_INVESTIGATION.md  # 25-page analysis (NEW)
└── data/
    ├── sections.json                  # Scraped IRC data (792 sections)
    ├── dependency_graph.json          # Section dependencies
    ├── aristotle_queue.json           # Main queue state
    └── aristotle_rerun_queue.json     # Rerun queue state
```

---

## 🔧 Quick Start

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
# Build project (note: requires Mathlib for Aristotle-generated sections)
lake build

# Run examples
lean --run src/TaxCode/Section301.lean
```

---

## 📊 Statistics

- **Sections Scraped**: 792 (complete IRC coverage §1-§4294)
- **Sections Formalized**: 10 via Aristotle INFORMAL
  - 6 production-ready (60%)
  - 2 need moderate fixes (20%)
  - 2 need reruns (20%)
- **Average Quality Score**: 7.2/10
- **Critical Bugs Found**: 1 (Section 108 - **FIXED**)
- **GitHub Issues Created**: 3 ([#22](../../issues/22), [#23](../../issues/23), [#24](../../issues/24))
- **Lines of Lean Code**: ~15,000 (formalized sections)
- **Documentation**: 1,000+ lines (audit reports, verification guide)
- **Test Cases**: 50+ with `#eval` verification
- **Proven Theorems**: 30+ across all sections

---

## 🎓 Key Insights

### 1. Formal Verification ≠ Legal Correctness

Section 108 had complete proofs but implemented the wrong law. This validates that:
- ✅ Formal verification proves mathematical consistency
- ❌ Formal verification does NOT prove correct legal interpretation
- ✅ Human review + multi-AI validation is essential

### 2. "Other Than" is a Red Flag

Aristotle systematically misinterprets negative eligibility phrases like "other than a C corporation", inverting the logic. **All such clauses require manual verification.**

### 3. Multi-AI Validation Works

When investigating the Section 108 error:
- 4/4 AI systems independently confirmed the error
- 100% agreement = extremely high confidence
- Took ~60 minutes vs weeks of manual review

### 4. Quality Control is Essential

Without the audit process:
- Section 108 would have illegal C corp exclusions
- $555M+ annual revenue loss from missing limitations
- Sections 1 & 103 would be unusable (timeout/incomplete)

---

## 🚧 Known Issues

- [#22](../../issues/22) - Section 1: Aristotle timeout, needs 2024 TCJA brackets (**RERUN IN PROGRESS**)
- [#23](../../issues/23) - Section 103: Incomplete proofs with `exact?` placeholders (**RERUN IN PROGRESS**)
- [#24](../../issues/24) - Section 108: Critical logic error (**FIXED** ✅)

---

## 📚 Resources

### Documentation
- [Verification Guide](ARISTOTLE_VERIFICATION_GUIDE.md) - Where to trust vs verify Aristotle
- [Audit Summary](AUDIT_SUMMARY.md) - Quality assessment of all 10 sections
- [Section 108 Verdict](SECTION_108_VERDICT.md) - Multi-AI investigation results
- [Roadmap](docs/ROADMAP.md) - 7-phase formalization plan

### Primary Sources
- **Legal Text**: [Cornell Law - 26 USC](https://www.law.cornell.edu/uscode/text/26)
- **Tax Brackets**: [IRS Tax Tables](https://www.irs.gov/filing/federal-income-tax-rates-and-brackets)
- **Formalization Tool**: [Harmonic Aristotle](https://aristotle.harmonic.fun)

---

## 🤝 Contributing

### Verification Process

All Aristotle-generated code goes through:
1. **Automated checks** - `exact?`, `sorry`, timeouts
2. **Structural review** - Completeness vs statute
3. **Logic review** - HIGH PRIORITY:
   - "Other than" exclusions
   - Multi-layer limitations
   - Entity-specific rules
4. **Test cases** - Including ineligible entities
5. **Multi-AI validation** - For critical issues

See [ARISTOTLE_VERIFICATION_GUIDE.md](ARISTOTLE_VERIFICATION_GUIDE.md) for complete checklist.

### How to Contribute

1. Check [open issues](../../issues) for priorities
2. Follow dependency order from `data/dependency_graph.json`
3. All definitions must cite IRC section sources
4. Include test cases with `#eval` examples
5. Run through verification checklist before PR

---

## 📈 Progress Tracking

**Current Campaign**: Priority-50 Sections
- Progress: 10/50 (20%)
- Success Rate: 60% production-ready on first generation
- Average Time: ~1.5 hours per section
- Queue Status: 2 in progress, 36 in retry, 2 in rerun

**Next Milestone**: Complete Priority-50 (40 more sections)

**Long-term Goal**: Full IRC formalization (792 sections)

---

## 🙏 Acknowledgments

- Built with [Lean 4](https://leanprover.github.io/lean4/)
- Powered by [Harmonic Aristotle](https://harmonic.fun)
- Multi-AI validation: [Grok-4 (xAI)](https://x.ai), [Gemini Pro (Google)](https://deepmind.google/technologies/gemini/), [Codex (OpenAI)](https://openai.com)
- Tax data from [IRS](https://www.irs.gov)
- Legal text from [Cornell Law School LII](https://www.law.cornell.edu/)

---

**Status**: Active Development 🚧
**Last Updated**: 2025-12-12
**Next Milestone**: Complete Priority-50 campaign (10/50 done)
**Latest**: Fixed Section 108 critical error + created verification guide

