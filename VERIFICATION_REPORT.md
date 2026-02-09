# Verification Report - P≠NP Formalization
## Documentation Accuracy & Code Correspondence

**Generated**: 2025-12-26
**Purpose**: Confirm that documentation mirrors the current Lean codebase after
removing legacy axioms and recording the remaining external inputs.

---

## ✅ Verification Summary

- ✅ There is **1** active axiom in the source tree (`pnp3/`):
  `ThirdPartyFacts.ppoly_circuit_locality`.
- ✅ Documentation (`AXIOM_ANALYSIS_FINAL.md`, `AXIOMS_FINAL_LIST.md`,
  `AXIOM_FEASIBILITY_ANALYSIS.md`, `CRITICAL_REANALYSIS.md`) reflects the same set.
- ✅ Interface theorems `P_subset_Ppoly_proof` and
  `P_ne_NP_of_nonuniform_separation` are imported proofs (no axioms).
- ✅ No stray `sorry`/`admit` in active files.

---

## 📊 Axiom Count Verification

```bash
$ rg "^axiom " -g"*.lean" pnp3
```

**Total**: 1 axiom (matches documentation).

### Per-Module Breakdown

| File | Expected | Found | Notes |
|------|----------|-------|-------|
| `ThirdPartyFacts/PpolyFormula.lean` | 1 | 1 | External NP-hardness axiom |
| `ThirdPartyFacts/Facts_Switching.lean` | 0 | 0 | Switching theorems (witness-backed) |
| **TOTAL** | **1** | **1** | ✅|

Archived modules (`archive/`, `old_attempts/`) contain historical axioms but do
not participate in the build or documentation metrics.

---

## 📚 Documentation Cross-Check

| Document | Status |
|----------|--------|
| `AXIOM_ANALYSIS_FINAL.md` | ✅ Notes 1 axiom, no placeholders in `pnp3/` |
| `AXIOMS_FINAL_LIST.md` | ✅ Updated executive summary for publication |
| `AXIOM_FEASIBILITY_ANALYSIS.md` | ✅ Feasibility reassessment for witness-backed theorems |
| `CRITICAL_REANALYSIS.md` | ✅ Critical-path description matches code |

No mismatches detected.

---

## ⚠️ Legacy Artifacts

- `archive/pnp3/Core/ShrinkageAC0.lean`, `archive/pnp3/ThirdPartyFacts/Depth2_*.lean`,
  and `old_attempts/OldAttempts/NP_separation.lean` keep historical axioms for
  reference. They remain excluded from the `lakefile` build.
- `Facts/PsubsetPpoly/Proof/Complexity/Interfaces.lean` and its bridge
  `Proof/Complexity/PsubsetPpoly.lean` now provide constructive theorems, so the
  exported API does not rely on axioms.

---

## ✅ Final Checklist

- [x] Axiom inventory synchronized across documentation.
- [x] Locations verified with `rg` output.
- [x] Interface theorems confirmed non-axiomatic.
- [x] Legacy files documented as out-of-scope.

---

**Verification Date**: 2025-12-25
**Verified By**: Automated scan + manual review
