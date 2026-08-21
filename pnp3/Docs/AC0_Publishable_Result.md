# AC0 Endpoint Vacuity Audit

Updated: 2026-08-17

The former “publishable AC0 result” wording is withdrawn. The active audit
surface is `pnp3/LowerBounds/AC0_GapMCSP_Final.lean`; the standard-looking
names in `AC0_GapMCSP.lean` are deprecated compatibility aliases.

## Exact proved statement

The canonical certificate is:

```text
false_of_smallAC0Params_and_easyFamilyData
  (params : SmallAC0ParamsPartial p)
  (easy : AC0EasyFamilyDataPartial params.ac0) : False
```

It uses exactly:

- `params.same_n` and the capacity assumption `params.union_small`;
- an AC0-realizable family `easy.F` via `easy.witness`;
- the all-functions-scale lower bound
  `2^(2^params.ac0.n) ≤ easy.F.toFinset.card` via `easy.card_lower`;
- the fixed-slice lower-size condition already stored in
  `p : GapPartialMCSPParams`.

It does not take a solver. Consequently it cannot use solver semantics,
solver correctness, a circuit implementation, or the equation connecting a
circuit to a semantic decider.

`SmallAC0Solver_Partial` stores both `params` and `easyData`, so every value of
that type is refuted by projection alone. The honest public names are:

```text
false_of_enrichedSmallAC0PackagePartial
not_exists_enrichedSmallAC0PackagePartial
EnrichedSmallAC0PackagePartialInconsistent
```

## Limitation

This proves that the repository’s enriched package is inconsistent. It does
not prove that Partial-MCSP is outside standard `AC0`, and it is not an AC0
lower bound or P-vs-NP mainline progress. The historical zero-hypothesis names
such as `gapPartialMCSP_not_in_AC0` are deprecated and must be cited only as
compatibility aliases for the enriched-package inconsistency.
