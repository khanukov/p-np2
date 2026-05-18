# L0 hInDag triviality probe — gpt55

## Classification

Infrastructure / audit probe.  This file proves an upper-bound premise used by
a route audit; it is not lower-bound mainline progress toward `P != NP`.

## Lean result

Landed `pnp3/Tests/HInDagTrivialityProbe.lean` with 152 source lines.

The staged file proves the canonical hInDag premise by fixed-slice truth-table
hardwiring:

- `constFalseDag`: one-gate false DAG for off-slice lengths.
- `ttTree` / `ttTree_eval`: recursive tree truth-table construction for an
  arbitrary fixed-length Boolean function.
- `ttDag` / `ttDag_eval`: compilation of that tree truth table through the
  existing straight-line-to-DAG adapter, yielding a `DagCircuit` that computes
  the arbitrary fixed-length function.
- `fixedSlice_gapPartialMCSP_in_PpolyDAG`: for any `GapPartialMCSPParams p`,
  hardwire the sole live slice `partialInputLen p` with `ttDag` and use
  `constFalseDag` elsewhere.
- `hInDag_for_canonicalAsymptoticHAsym`: instantiate the fixed-slice theorem on
  every canonical asymptotic slice.

## Import / hygiene audit

Imports in the staged file:

```lean
import Complexity.Interfaces
import Complexity.PsubsetPpolyInternal.TreeToStraight
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
```

Forbidden import audit:

- No import of `Magnification.LocalityProvider_Partial`.
- No import of `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
- No import under `pnp3/RefutedPredicates/`.
- No refuted-predicate carrier import.

Forbidden-token audit on the staged file found no matches for:

```text
FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions
```

Kernel-hygiene audit on the staged file found no `axiom`, `opaque`, `sorry`,
`admit`, `native_decide`, or `noncomputable def` token.

## Conclusion-side classification

The hInDag premise is now trivial at the canonical instantiation: the fixed
slice can be hardwired by an arbitrary truth-table DAG family.  This does not
settle the downstream iso-strong / promise-YES conclusion.  The L0 construction
only supplies an upper-bound witness for each fixed language slice; it does not
produce a small Lean counterexample to the conclusion and does not discharge the
conclusion structurally.

Therefore the conclusion-side question remains open in this L0 scope and should
be audited separately under the hardwired `hInDag` premise.

## Commands run

- `lake build PnP3` — pass; built the pnp3 library before direct elaboration.
- `lake env lean pnp3/Tests/HInDagTrivialityProbe.lean` — pass.
- `wc -l pnp3/Tests/HInDagTrivialityProbe.lean` — 152 lines.
- `rg -n "sorry|admit|native_decide|axiom|opaque|noncomputable def|FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions" pnp3/Tests/HInDagTrivialityProbe.lean` — no matches.
- `./scripts/check.sh` — pass.

**`RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`**
