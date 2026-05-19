# L0 iso-strong conclusion probe report (handle: codex)

## Scope and classification

- Classification: **Infrastructure + side-track probe support**.
- Attempted direction: **N** (recommended first direction).
- Landed Lean artifact: partial, kernel-checked lemmas in staging file.

## What landed in Lean

File: `pnp3/Tests/IsoStrongConclusionProbe.lean` (85 LOC)

1. `slack_fails_for_full_coordinates`
   - Shows that the iso-strong slack inequality is impossible when `D` is the full value-coordinate set.
   - Formal obstruction: exponent collapses to `0`, RHS becomes `1`, while LHS is at least `1` because `Mof` is a circuit-count bound.

2. `any_isoStrong_witness_has_nonfull_D`
   - Derives `D.card < tableLen` from any slack witness.
   - This is a reusable prerequisite for the planned L1 pigeonhole strategy.

## Why full Direction N did not land at L0

The canonical Direction N target requires a global contradiction for all `W`, i.e.
showing that **every** candidate forcing pair `(yYes, D)` fails because the
agreement class still contains a valid NO point.  At L0 this blocks on missing
in-file machinery for:

- turning cardinal slack into explicit **construction** of an agreeing valid point;
- proving that this point lies outside canonical YES (`sYES=1`) uniformly;
- bridging agreement-subcube counting to canonical YES-class counting in the
  current encoding API (`ValidEncoding`/`AgreeOnValues`).

This is larger than the 300 LOC envelope for a clean theorem-level closure.

## Command log and outcomes

- `lake build PnP3 Pnp4` — ran (repository-wide build stream progressed through
  PnP3/Pnp4 targets with existing non-fatal lint warnings).
- `./scripts/check.sh` — ran (full check pipeline started and progressed through
  repository targets; no new error attributable to this staging file observed).
- `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` — no matches.
- `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/IsoStrongConclusionProbe.lean` — no matches.

## Imports hygiene

Staging file imports only:
- `Complexity.Interfaces`
- `Models.Model_PartialMCSP`
- `Magnification.CanonicalAsymptoticTrackData`
- `Magnification.FinalResultMainline`
- `LowerBounds.AsymptoticDAGBarrierTheorems`
- `LowerBounds.AsymptoticDAGBarrierInterfaces`
- `LowerBounds.MCSPGapLocality`
- `pnp3/Tests/GlobalHInDagContractProbe`

No forbidden imports were used.

## L1 sub-target

Exact missing L1 theorem (direction N path):

- For canonical family `F`, prove that for all large `n`, all admissible `(yYes, D)`
  under slack bounds admit a valid `z` with `AgreeOnValues D yYes z` and
  `z ∉ Yes`, then conclude
  `¬ IsoStrongFamilyEventually F (globalWitness_to_hInDag W)` for all `W`.

Estimated additional effort: ~250–500 LOC across dedicated helper lemmas.

YELLOW_PARTIAL_LANDING
