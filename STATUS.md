# Project Status (current)

This file is the authoritative status snapshot.

## Date

- 2026-02-22

## Active result

- Pipeline: `PNP3` (`SAL -> Covering-Power -> anti-checker -> magnification`)
- Active separation target: `NP_not_subset_PpolyFormula` (conditional)
- Main final module: `pnp3/Magnification/FinalResult.lean`

## Verified code hygiene

- Active `axiom` declarations in `pnp3/`: **0**
- Active `sorry`/`admit` in `pnp3/`: **0**
- `lake build` and `./scripts/check.sh` pass on current tree

## Closed items

1. I-1 closed (localized bridge)
- `pnp3/ThirdPartyFacts/PpolyFormula.lean` now has `trivialFormulaizer` and
  `gapPartialMCSP_realization_trivial`.
- Bridge usage is wired through trivial realization variants in
  `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`.

2. I-3 closed at contract/automation layer
- `HalfTableCertificateBound` is wired from certificate providers.
- Auto wrapper exists: `locality_lift_partial_of_certificate_auto`.
- Main certificate route no longer needs manually threaded `hCardHalf`.

## Still external (non-axiomatic)

1. I-4 not closed
- Real multi-switching/shrinkage constructions for target families are still
  external witness/provider inputs.
- Current code has constructive interfaces and wrappers, but not fully internal
  global instances.

2. I-2 not closed
- Structured locality provider can be built from explicit certificate packages,
  but default unconditional provider availability is not internally proved.

3. I-5 not closed
- `P != NP` wrappers still require explicit bridge:
  `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` (`hFormulaToPpoly`).

## Final theorem interpretation

- Current fully machine-checked active claim: conditional
  `NP_not_subset_PpolyFormula`.
- `P != NP` remains conditional until the `hFormulaToPpoly` bridge is internalized.

## Next priority order

1. Finish I-4: construct real certificate providers / multi-switching instances.
2. Use I-4 artifacts to internalize default structured provider path (I-2).
3. Keep `P != NP` as explicitly conditional until I-5 is mathematically closed.
