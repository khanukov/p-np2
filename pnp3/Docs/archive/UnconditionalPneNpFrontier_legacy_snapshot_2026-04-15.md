# Archived Frontier Fallback: `UnconditionalPneNpFrontier`

Archived on: 2026-04-15.

This note records the removal of the active Lean module
`pnp3/Frontier/UnconditionalPneNpFrontier.lean` from the main build.

## Why it was archived

That file packaged an older fallback route:

```text
CoreFrontierObligation :=
  ∃ hMag, ∃ n, ∃ hn,
    gapPartialMCSP_supportHalfObligation (hMag.antiChecker.asymptotic.pAt n hn)
```

and then reduced that payload to:

- `ComplexityInterfaces.NP_not_subset_PpolyDAG`,
- `ComplexityInterfaces.P_ne_NP`.

This is no longer the active mainline route.

## What replaced it in the active tree

The default DAG separation is now internalized directly in
`pnp3/Magnification/FinalResultMainline.lean` via:

1. the fixed-slice bridge
   `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`,
2. support bounds from `hMag.switching.multiswitching`,
3. the already-closed fixed-slice collapse consumer.

So the active default path is now:

```text
NP_not_subset_PpolyDAG_final
  (hMag : MagnificationAssumptions)
```

followed by:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
```

## Current blocker after archival

The remaining unconditional blocker is no longer a DAG-side frontier theorem.
It is the residual package argument:

```text
hMag : MagnificationAssumptions
```

on the formula/public final cone.

## Historical status

Keep the old frontier route only as historical provenance.
It must not be cited as part of the active mainline closure path.
