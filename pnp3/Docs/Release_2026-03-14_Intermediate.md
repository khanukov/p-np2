# Release Note (Intermediate) — 2026-03-14

Historical note (2026-04-03):
this file is a frozen intermediate release note for the inclusion-side closure.
It is not the current repository-wide release posture. Use `/root/p-np2/RELEASE_RC.md`
for current public wording.

Scope: cleanup and stabilization of the internal `P ⊆ PpolyDAG` route.

## Included

1. Active no-arg closure endpoint is explicit and machine-checked:
   - `proved_P_subset_PpolyDAG_internal`.
2. Final default path uses the no-arg endpoint (`FinalResult`).
3. Explicit wrappers (`with_provider`, `with_barriers`) now use linear
   contract bundle (`PsubsetPpolyCompiledRuntimeLinearOutputContracts`).
4. Legacy/compatibility tails removed from active code paths:
   - iterated compatibility closure chain,
   - legacy aliases in DAG-internal packaging layer,
   - obsolete legacy runtime branch already removed earlier.
5. Conversion-layer proof in `PsubsetPpolyDAG_Internal` is now transparent
   witness repackaging (no local black-box bridge call at that layer).
6. Public straight-line adapter entrypoint added:
   - `Complexity.PpolyDAG_from_StraightLine`
   - active route uses only `StraightLineAdapter` names.

## Verification

Executed successfully on this snapshot:

```bash
lake build
./scripts/check.sh
```

`check.sh` summary:
- full Lean build: pass
- smoke: pass
- hygiene (`axiom/sorry/admit/native_decide`): pass
- barrier audits / axiom-surface dump: pass

## Known non-blocking items

1. Existing Lean linter warnings in `PsubsetPpolyInternal/Simulation.lean`
   (`simpa->simp`, unused simp args, etc.) remain.
2. `NP_not_subset_PpolyDAG` remains an explicit external input
   (separation side), outside inclusion closure scope.

## Documentation pointers

- Current status: `pnp3/Docs/PsubsetPpoly_Internal_TODO.md`
- Auditor checklist: `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`
- Current handoff: `pnp3/Docs/PsubsetPpoly_AUDIT_HANDOFF.md`
