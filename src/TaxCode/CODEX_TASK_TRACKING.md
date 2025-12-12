# Codex CLI Task Tracking - GitHub Issues #41-45

**Started**: December 12, 2025
**Branch**: `fix/github-issues-41-45`
**Task ID**: bbb8e83
**Mode**: Full-Auto Autonomous

---

## Task Overview

Codex CLI is working autonomously on **5 GitHub issues** with targeted fixes for IRC tax code sections.

**Command**:
```bash
codex exec --full-auto "$(cat /tmp/codex_fix_all_issues.md)"
```

---

## Issues Being Fixed

### 🔴 HIGH PRIORITY

#### Issue #41: Section 162 - Missing Critical Provisions
- **File**: `Section162.lean`
- **Changes**: Add §162(f) fines/penalties, §162(m) exec compensation, §162(e) lobbying
- **Estimated Time**: 30-45 minutes

#### Issue #42: Section 32 - Eligibility Errors
- **File**: `Section32.lean`
- **Changes**: Add MFS check (§32(d)), add investment income check (§32(i))
- **Estimated Time**: 30-45 minutes

### 🟡 MEDIUM PRIORITY

#### Issue #45: Section 103 - Private Loan Test Bug
- **File**: `Section103.lean`
- **Changes**: Fix loan test to "lesser of $5M or 5%", add federal guarantee check
- **Estimated Time**: 20-30 minutes

#### Issue #44: Section 24 - Outdated TCJA Values
- **File**: `Section24.lean`
- **Changes**: Update to TCJA 2018-2025 values, add year-based parameters
- **Estimated Time**: 30-45 minutes

#### Issue #43: Currency Type Safety (DO LAST)
- **Files**: 7 sections (24, 32, 38, 55, 56, 59, 162)
- **Changes**: Create Common/Currency.lean, migrate to Nat type
- **Estimated Time**: 60-90 minutes

---

## Execution Order

Codex will work in this priority order:
1. Issue #42 (Section 32) - Critical eligibility bugs
2. Issue #41 (Section 162) - Missing provisions
3. Issue #45 (Section 103) - Loan test bug
4. Issue #44 (Section 24) - Outdated values
5. Issue #43 (Currency refactor) - Affects multiple files

**Total Estimated Time**: 2.5-4 hours

---

## Success Criteria

For each issue, Codex should:
- ✅ Read and understand current implementation
- ✅ Make targeted changes as specified
- ✅ Update examples/tests to verify logic
- ✅ Verify file compiles with `lean`
- ✅ Create git commit with descriptive message

**Overall Success**:
- All 5 issues have fixes implemented
- All modified files compile successfully
- Existing theorems still prove
- No regressions introduced

---

## Monitoring

**Check progress**:
```bash
# View Codex output in real-time
tail -f /tmp/claude/tasks/bbb8e83.output

# Get full results when complete
codex exec --task-id bbb8e83
```

**Check git commits**:
```bash
git log --oneline --graph
```

---

## Expected Deliverables

### Git Commits (5 expected)

1. `Fix Section 32 eligibility checks (Issue #42)`
2. `Add missing provisions to Section 162 (Issue #41)`
3. `Fix Section 103 private loan test (Issue #45)`
4. `Update Section 24 to TCJA values (Issue #44)`
5. `Refactor Currency to Nat type (Issue #43)`

### Modified Files (9 expected)

**High Priority**:
- `Section32.lean` - Eligibility fixes
- `Section162.lean` - New expense types

**Medium Priority**:
- `Section103.lean` - Loan test + federal guarantee
- `Section24.lean` - TCJA parameter structure

**Currency Refactor**:
- `Common/Currency.lean` - NEW FILE
- `Section38.lean` - Currency migration
- `Section55.lean` - Currency migration
- `Section56.lean` - Currency migration
- `Section59.lean` - Currency migration

---

## Fallback Plan

If Codex encounters issues:

1. **Compilation Errors**: Codex should fix syntax issues autonomously
2. **Theorem Proof Failures**: Simplify proofs or use `sorry` with TODO
3. **Ambiguous Requirements**: Make best judgment based on audit feedback
4. **File Not Found**: Skip that file and continue with others

If critical failures occur, manual intervention may be needed.

---

## Post-Completion Checklist

Once Codex completes:

1. ✅ Review all git commits
2. ✅ Test compilation: `cd src/TaxCode && lean --version && lean Section*.lean`
3. ✅ Run any `#eval` tests to verify correctness
4. ✅ Update GitHub issues with "Fixed in commit XXX"
5. ✅ Create PR to merge branch into main
6. ✅ Update README.md with fix status

---

## Notes

- Codex is running in **full-auto mode** - no human intervention
- All changes are **targeted and minimal** - no refactoring unrelated code
- Working directory: `/Users/patrickkavanagh/aristotle_legal/src/TaxCode`
- Git branch: `fix/github-issues-41-45`
- Expected completion: 2.5-4 hours (depending on complexity)

**Status**: 🟢 RUNNING

Monitor progress with: `tail -f /tmp/claude/tasks/bbb8e83.output`
