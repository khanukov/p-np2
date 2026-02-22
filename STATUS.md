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

3. I-4 closed on explicit AC0 path (Path A)
- Constructive common-CCDT multi-switching chain is wired end-to-end for
  explicit CNF/AC0 families (`stage1_6_complete_*_common*`).
- New bridge module:
  `pnp3/Magnification/AC0LocalityBridge.lean`.
- This closes I-4 as an internal constructive engine for AC0-witness inputs
  (no external `henc_small` hypotheses in the active common route).

## Still external (non-axiomatic)

1. Ppoly->AC0 bridge not closed (by design)
- We do **not** claim a general conversion from arbitrary `PpolyFormula`
  witnesses to AC0/CNF families.
- The AC0 bridge is explicit-input only (Path A), which is the mathematically
  correct boundary for I-4.

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

1. Use AC0 I-4 artifacts to internalize default structured provider path (I-2).
2. Keep `P != NP` as explicitly conditional until I-5 is mathematically closed.
3. Add optional stronger bridge assumptions/modules (Option C style) only as
   separate, explicitly-labeled layers.
