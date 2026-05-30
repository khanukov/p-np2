# Archived pnp3 periphery — 2026-05

This note documents a small, **reversible** archiving step taken during a
periphery-cleanup pass over `pnp3/`. It is separate from the historical
`archive/README.md` (which describes the 2025-10 critical-path reduction).

> **Update (2026-05-30):** the TM-verifier cluster (`GapMCSPVerifier.lean` plus
> the `TuringToolkit/` submodules) was relocated out of
> `Complexity/PsubsetPpolyInternal/` (the `P ⊆ P/poly` internalization) into its
> own namespace `Complexity/TMVerifier/`, since it implements the GapMCSP
> NP-verifier roadmap and is not part of the `P ⊆ P/poly` proof cone. All paths
> in this note already reflect the new `TMVerifier/` home.

## Summary

A dependency sweep flagged 9 `pnp3/` modules as *unimported* (no active Lean
module `import`s them). On closer inspection **7 of those 9 are not dead**:
they are unimported but deliberately referenced by **active or governance
documentation** as trust-root interfaces, roadmap "next work", or audit-ledger
entries. Those 7 were therefore **restored** to active `pnp3/`.

Only the **2 modules below** are genuinely peripheral (no active code *and* no
active/governance doc depends on them), so they remain archived here.

> The 7 restored modules: `Barrier/{Algebrization,NaturalProofs,Relativization}.lean`,
> `Complexity/TMVerifier/GapMCSPVerifier.lean`,
> `Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean`,
> `LowerBounds/DAGUnconditionalBlocker.lean`,
> `Magnification/AsymptoticDAGCollapse.lean`. See git history for the move/restore.

## What stays archived (2 modules)

### 1. `TuringToolkit.lean` — convenience aggregator

| | |
|---|---|
| **Original path** | `pnp3/Complexity/TMVerifier/TuringToolkit.lean` |
| **Archived path** | `archive/pnp3/Complexity/TMVerifier/TuringToolkit.lean` |
| **Role** | Aggregator that merely re-exported all `TuringToolkit.*` submodules (`Foundation`, `BinaryCounter`, `Encoding`, `AtomicPrograms`, `UnaryAtOffset`, `CopyAtOffset`, `CombineAtOffset`, `GateWrappers`, `ConstStatePhasedProgram`, …) via `import`. |
| **Why archived** | 0 exact importers. Every submodule it re-exported **stays in active `pnp3/`**, is imported directly by its consumers, and has its own `Glob.one` entry in `lakefile.lean`. The aggregator was pure convenience with no dependents — removing it changes nothing in the build. |
| **No active/governance doc** references this aggregator path. |

### 2. `RouteNextStep_AcceptedFamily.lean` — accepted-family route alias

| | |
|---|---|
| **Original path** | `pnp3/LowerBounds/RouteNextStep_AcceptedFamily.lean` |
| **Archived path** | `archive/pnp3/LowerBounds/RouteNextStep_AcceptedFamily.lean` |
| **Role** | Forwarding/alias module exposing an "accepted-family" next-step route to `NP_not_subset_PpolyDAG`, conditional on a weak route + bridge + NP witness. |
| **Why archived** | 0 active importers. Referenced only by **historical** material — `outputs/unconditional-next-steps-ru.md`, `outputs/unconditional-proof-handoff-ru.md`, and `seed_packs/**` audit reports — which are point-in-time records, not living governance docs. The conditional DAG endpoints it aliases are themselves proved in active files (`AsymptoticDAGBarrierTheorems.lean`, `DAGStableRestrictionProducer.lean`, `SingletonDensityContradiction.lean`), so no active surface depends on this alias. |

## How to restore either module

```bash
# 1. move the file back into the active tree
git mv archive/pnp3/Complexity/TMVerifier/TuringToolkit.lean \
       pnp3/Complexity/TMVerifier/TuringToolkit.lean
#    (or, for the route alias)
git mv archive/pnp3/LowerBounds/RouteNextStep_AcceptedFamily.lean \
       pnp3/LowerBounds/RouteNextStep_AcceptedFamily.lean

# 2. re-add the corresponding glob to lakefile.lean (PnP3 lib, srcDir "pnp3"):
#      Glob.one `Complexity.TMVerifier.TuringToolkit,
#      Glob.one `LowerBounds.RouteNextStep_AcceptedFamily,

# 3. rebuild + gate
./scripts/check.sh
```

## Correctness / verification

- These two modules are **mathematically sound**; they are archived for tidiness
  only, not because of any error, `sorry`, or axiom regression.
- The proof cone of the public finals is **unaffected** (neither module is in it).
- After this step the full `./scripts/check.sh` (build + smoke + tests + audits)
  passes with exit `0`.
- Files are moved with `git mv`, so history is preserved and the step is fully
  reversible.

## Note on historical references

The two archived modules may still be named in **point-in-time** documents under
`outputs/` and `seed_packs/` (engineering handoffs and parallel-dispatch task
records). Those are intentionally **not** rewritten: they are historical logs,
and editing them would falsify the record rather than improve consistency.

**Date**: 2026-05-29

---

## Doc archiving — 2026-05-30 (superseded `pnp3/Docs/` planning notes)

A documentation-hygiene pass moved **3 superseded planning notes** out of
active `pnp3/Docs/` into `archive/pnp3/Docs/`:

- `Release_2026-03-14_Intermediate.md` — an intermediate release snapshot from
  2026-03-14, long superseded by `STATUS.md` / `RELEASE_RC.md`.
- `UnrestrictedDAG_Blocker_Reassessment_2026-03-30.md` — a point-in-time
  (2026-03-30) blocker reassessment, superseded by the post-PR13 canonical-track
  refutation chain documented in `STATUS.md`.
- `MultiSwitching_NextStep.md` — "next step" planning for the multi-switching
  *contract* route, which is now formally refuted
  (`FormulaSupportBoundsFromMultiSwitchingContract -> False`).  The live
  multi-switching combinatorics modules under `pnp3/AC0/MultiSwitching/` are
  unaffected and remain in the build; only this stale planning note moved.

Selection criterion (consistent with the module pass above): each note is
referenced **only** by a single historical `seed_packs/` audit report
(`phase1_20engineer_parallel_dispatch/audit_reports/A10_partial_legacy_markers_codex.md`),
which itself catalogues legacy markers — i.e. none is a trust-root interface,
active roadmap item, or governance dependency.

- No active/governance doc and **no `scripts/` check** references these files.
- The `MultiSwitching_DepthInduction_TODO.md` note (more recent, 2026-05-28) was
  **kept** in active `pnp3/Docs/`.
- Files are moved with `git mv`, so history is preserved and the step is fully
  reversible.
- As above, the historical `seed_packs/` reference is intentionally **not**
  rewritten.

**Date**: 2026-05-30
