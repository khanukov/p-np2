# Verification Report - P≠NP Formalization
## Documentation Accuracy & Code Correspondence

**Generated**: 2025-12-25
**Purpose**: Confirm that documentation mirrors the current Lean codebase after
removing legacy axioms.

---

## ✅ Verification Summary

- ✅ All **2** active axioms are present in the source tree (`pnp3/`).
- ✅ Documentation (`pnp3/Docs/AXIOMS.md`, `AXIOMS_FINAL_LIST.md`,
  `AXIOM_FEASIBILITY_ANALYSIS.md`, `CRITICAL_REANALYSIS.md`) reflects the same set.
- ✅ Interface theorems `P_subset_Ppoly_proof` and
  `P_ne_NP_of_nonuniform_separation` are imported proofs (no axioms).
- ✅ No stray `sorry`/`admit` in active files.

---

## 📊 Axiom Count Verification

```bash
$ rg "^axiom " -g"*.lean" pnp3
pnp3/ThirdPartyFacts/Facts_Switching.lean:142:axiom partial_shrinkage_for_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:301:axiom shrinkage_for_localCircuit
```

**Total**: 2 axioms (matches documentation).

### Per-Module Breakdown

| File | Expected | Found | Notes |
|------|----------|-------|-------|
| `ThirdPartyFacts/Facts_Switching.lean` | 2 | 2 | Switching lemmas |
| **TOTAL** | **2** | **2** | ✅|

Archived modules (`archive/`, `old_attempts/`) contain historical axioms but do
not participate in the build or documentation metrics.

---

## 📚 Documentation Cross-Check

| Document | Status |
|----------|--------|
| `pnp3/Docs/AXIOMS.md` | ✅ Lists the same 2 axioms, notes archived items |
| `AXIOMS_FINAL_LIST.md` | ✅ Updated executive summary for publication |
| `AXIOM_FEASIBILITY_ANALYSIS.md` | ✅ Feasibility reassessment for 2 axioms |
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
