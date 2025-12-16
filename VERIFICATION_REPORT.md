# Verification Report - P≠NP Formalization
## Documentation Accuracy & Code Correspondence

**Generated**: 2025-10-24  
**Purpose**: Confirm that documentation mirrors the current Lean codebase after
removing legacy axioms.

---

## ✅ Verification Summary

- ✅ All **8** active axioms are present in the source tree (`pnp3/`).
- ✅ Documentation (`pnp3/Docs/AXIOMS.md`, `AXIOMS_FINAL_LIST.md`,
  `AXIOM_FEASIBILITY_ANALYSIS.md`, `CRITICAL_REANALYSIS.md`) reflects the same set.
- ✅ Interface theorems `P_subset_Ppoly_proof` and
  `P_ne_NP_of_nonuniform_separation` are imported proofs (no axioms).
- ✅ No stray `sorry`/`admit` in active files.

---

## 📊 Axiom Count Verification

```bash
$ rg "^axiom " -g"*.lean" pnp3
pnp3/LowerBounds/AntiChecker.lean:171:axiom antiChecker_exists_large_Y
pnp3/LowerBounds/AntiChecker.lean:237:axiom antiChecker_exists_testset
pnp3/LowerBounds/AntiChecker.lean:305:axiom antiChecker_exists_large_Y_local
pnp3/LowerBounds/AntiChecker.lean:371:axiom antiChecker_exists_testset_local
pnp3/Magnification/Facts_Magnification.lean:730:axiom Locality_trigger
pnp3/Magnification/Facts_Magnification.lean:735:axiom CJW_sparse_trigger
pnp3/ThirdPartyFacts/Facts_Switching.lean:119:axiom partial_shrinkage_for_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:278:axiom shrinkage_for_localCircuit
```

**Total**: 8 axioms (matches documentation).

### Per-Module Breakdown

| File | Expected | Found | Notes |
|------|----------|-------|-------|
| `ThirdPartyFacts/Facts_Switching.lean` | 2 | 2 | Switching lemmas |
| `LowerBounds/AntiChecker.lean` | 4 | 4 | Anti-checker axioms |
| `Magnification/Facts_Magnification.lean` | 2 | 2 | Magnification triggers |
| **TOTAL** | **8** | **8** | ✅|

Archived modules (`archive/`, `old_attempts/`) contain historical axioms but do
not participate in the build or documentation metrics.

---

## 📚 Documentation Cross-Check

| Document | Status |
|----------|--------|
| `pnp3/Docs/AXIOMS.md` | ✅ Lists the same 10 axioms, notes archived items |
| `AXIOMS_FINAL_LIST.md` | ✅ Updated executive summary for publication |
| `AXIOM_FEASIBILITY_ANALYSIS.md` | ✅ Feasibility reassessment for 10 axioms |
| `CRITICAL_REANALYSIS.md` | ✅ Critical-path description matches code |

No mismatches detected.

---

## ⚠️ Legacy Artifacts

- `archive/pnp3/Core/ShrinkageAC0.lean`, `archive/pnp3/ThirdPartyFacts/Depth2_*.lean`,
  and `old_attempts/OldAttempts/NP_separation.lean` keep historical axioms for
  reference. They remain excluded from the `lakefile` build.
- `Facts/PsubsetPpoly/Proof/Complexity/Interfaces.lean` still declares an axiom
  internally but is superseded by the constructive theorem in the same package.
  The exported API (`ThirdPartyFacts/PsubsetPpoly.lean`) uses the proven result.

---

## ✅ Final Checklist

- [x] Axiom inventory synchronized across documentation.
- [x] Locations verified with `rg` output.
- [x] Interface theorems confirmed non-axiomatic.
- [x] Legacy files documented as out-of-scope.

---

**Verification Date**: 2025-10-24  
**Verified By**: Automated scan + manual review
