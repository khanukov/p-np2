# Closure Route Policy (canonical)

Updated: 2026-04-15.

This file is a hard policy reference for unconditional-closure planning.
It exists to prevent stale DAG-route language from re-entering status docs.

## One active route

Only one active route is allowed in canonical planning docs:

1. preserve the now-internalized DAG separation route,
2. internalize the formula-side package exposed by
   `NP_not_subset_PpolyFormula_final (hMag : MagnificationAssumptions)`,
3. then remove residual `hMag` from `P_ne_NP_final`.

## Closed/no-go routes

Literal fixed-slice blocker hunt is a closed historical no-go route for
unconditional closure planning.

Relevant no-go modules:

- `pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

## Documentation guardrails

Canonical docs (`STATUS.md`, `TODO.md`,
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`,
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`, and this file)
must satisfy all of the following:

1. explicitly mention fixed-slice no-go status,
2. explicitly mention that DAG separation is already internalized,
3. explicitly mention that residual `MagnificationAssumptions` is the current
   blocker,
4. avoid deprecated phrasing that presents historical DAG-side fallbacks as the
   active route.

This policy is enforced in `scripts/check.sh`.
