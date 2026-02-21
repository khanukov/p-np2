# Project Status (current)

This file is the single source of truth for the active state of the repository.

## Active pipeline

- Pipeline: `PNP3` (SAL -> Covering-Power -> anti-checker -> magnification)
- Target language: `gapPartialMCSP_Language`
- Final entrypoint: `pnp3/Magnification/FinalResult.lean`

Current active result family:

- `NP_not_subset_PpolyFormula` (conditional)

The current final theorem family is parameterized by explicit assumptions:

1. `StructuredLocalityProviderPartial`
2. localized bridge goal(s) from `ThirdPartyFacts/PpolyFormula.lean`

## External inputs (active)

Current `axiom` declarations in `pnp3/`: none (`rg "^axiom " -g"*.lean" pnp3` is empty).

External dependencies represented as explicit goal hypotheses:

1. `GapPartialMCSPPpolyRealToPpolyFormulaGoal p` (optional localized bridge layer)

in `pnp3/ThirdPartyFacts/PpolyFormula.lean`.

Additionally, Part A still depends on externally provided shrinkage witnesses
(`partial_shrinkage_for_AC0`, `shrinkage_for_localCircuit`).

For partial locality-lift plumbing:

- explicit `hStable` restriction witness, or
- certificate path via `ShrinkageCertificate.Provider` together with
  `hCardHalf` on the certificate restriction alive set.

## What is already internal

- Anti-checker core and local contradiction are proved in Lean.
- Locality-lift bridge plumbing is proved in Lean (including certificate-to-stability wrapper).
- Magnification glue and OPS-style triggers are proved in Lean.
- Classical bridge `NP ⊄ P/poly` + `P ⊆ P/poly` -> `P ≠ NP` is proved in Lean,
  but is not the active final route until the non-uniform interface is upgraded.

## Immediate constructive target

Two immediate constructive milestones:

1. Close localized embed:

- `ThirdPartyFacts.GapPartialMCSPFormulaizer p`

2. Close certificate cardinality obligation for partial locality-lift instances
   (discharge `hCardHalf` constructively in the intended provider path).

From (1), we get:

- `GapPartialMCSPFormulaRealization p`
- localized embed for `gapPartialMCSP_Language p`
- final theorem variants `..._with_formulaizer`.

## Next docs

- `TODO.md` for the concrete execution plan.
- `AXIOMS_FINAL_LIST.md` for the external input inventory.
