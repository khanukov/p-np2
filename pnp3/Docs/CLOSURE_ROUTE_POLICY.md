# Closure Route Policy (canonical)

Updated: 2026-04-04.

This file is a hard policy reference for DAG-side closure planning.
It exists to prevent ambiguous routing language from re-entering status docs.

## One active route

Only one active route is allowed in canonical planning docs:

1. asymptotic/eventual source theorem,
2. length-local bridge assumptions,
3. weak-route class-level payload,
4. internal `ComplexityInterfaces.NP_not_subset_PpolyDAG`,
5. then API cleanup (`hNPDag`, then `hMag`).

## Closed/no-go route

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
2. explicitly mention asymptotic/eventual + length-local active route,
3. avoid deprecated phrasing that presents fixed-slice as the fastest route.

This policy is enforced in `scripts/check.sh`.
