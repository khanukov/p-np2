# PNP3 project: active Lean code

Updated: 2026-05-28

Canonical checklist for unconditional `P != NP`:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`/root/p-np2/RELEASE_RC.md`.

## What lives here

The `pnp3/` directory carries the active pipeline:

`SAL -> Covering-Power -> anti-checker -> magnification -> DAG final wrappers`

## MCSP variant boundary

Active `pnp3/` uses **Partial MCSP only**:

- model: `Models/Model_PartialMCSP.lean`;
- language / promise: `gapPartialMCSP_Language`, `GapPartialMCSPPromise`.

The legacy GapMCSP model and other older branches under `archive/` are
historical context, not the source of the current status.

## Current proof boundary

The repository compiles a substantial DAG / magnification scaffold:

1. the inclusion side is internalised via
   `proved_P_subset_PpolyDAG_internal`;
2. the fixed-slice bridge `PpolyDAG -> PpolyFormula` is in place;
3. asymptotic, Route-B, `_TM`, and support-half wrappers exist;
4. the falsifiability audit for the support-bounds hypotheses is in
   place.

But no unconditional `P != NP` theorem exists in the repository.

## The main problem

The old support-bounds source turned out to be formally false:

```text
FormulaSupportRestrictionBoundsPartial -> False
FormulaSupportBoundsFromMultiSwitchingContract -> False
MagnificationAssumptions -> False
FormulaSupportBoundsPartial_fromPipeline -> False
```

Therefore theorems routed through those hypotheses are vacuous: they
compile, but they use "ex falso quodlibet" mathematically.

Root cause: a truth-table hardwired formula at a fixed slice is a
`PpolyFormula` but has support over all variables.  The old predicates
required polylogarithmic / small support for too broad a class of
formulas.

## FixedParams

The current honest candidate is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

It fixes the AC0 parameters externally and therefore blocks the known
singleton-provider attack.  But this is only the shape of a future
contract, not a proved theorem.

Important: `fixedParams + uniformProvenance` again reduces to the old
false predicate and is therefore inconsistent in the current
formalisation.

## A single file for the remaining gap

The remaining research boundary lives in:

```text
Magnification/UnconditionalResearchGap.lean
```

It defines `ResearchGapWitness` and proves the conditional bridge
`P_ne_NP_of_researchGap`.  A future unconditional breakthrough must
prove the witness in this file and then expose the zero-argument
theorem from it.

## Source of status

The repository-wide status and blockers are checked only against:

- `/root/p-np2/STATUS.md`
- `/root/p-np2/TODO.md`
- `/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`

Local historical notes and old roadmap files are not authoritative if
they diverge from those documents.
