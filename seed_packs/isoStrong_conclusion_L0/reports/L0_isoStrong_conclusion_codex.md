# L0 iso-strong conclusion probe report (codex)

## Scope and reading

Completed required reading set from dispatch and worker prompt:
- `RESEARCH_CONSTITUTION.md`
- `STATUS.md`
- `seed_packs/isoStrong_conclusion_L0/README.md`
- `seed_packs/isoStrong_conclusion_L0/WORKER_PROMPT_L0.md`
- `seed_packs/isoStrong_conclusion_audit_D0/reports/D0_isoStrong_conclusion_audit_codex53.md`
- `pnp3/Tests/GlobalHInDagContractProbe.lean`
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean`
- `pnp3/LowerBounds/MCSPGapLocality.lean`
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
- `pnp3/Models/Model_PartialMCSP.lean`

## What was attempted

Direction attempted first: **N**.

I tried to complete the recommended canonical pigeonhole refutation
(`isoStrong_conclusion_negative_for_canonical`) in ≤300 LOC. The blocker at L0
is not syntax-level but proof-assembly-level: the argument needs a fully formal
bridge from slack cardinality (`m + 2 < 2^(tableLen - κ)`) to an explicit valid
encoding witness outside YES while preserving agreement constraints on `D`.

In this repository shape, that requires a nontrivial L1 lemma bundle over:
- `ValidEncoding`/`encodePartial`/`decodePartial` image structure,
- coordinate-level freedom under `AgreeOnValues` on value slots,
- canonical YES characterization at `sYES = 1` (exactly `m+2` size-1 functions),
- and a pigeonhole map from agreement subcube points to YES classes.

This exceeded safe L0 completion within one ≤300 LOC probe file without
introducing brittle wrapper-like artifacts.

## Lean landing

Landed one useful elimination lemma in the staging file:
- `isoStrong_unpack_at`

This theorem is a clean one-step unpacking of
`IsoStrongFamilyEventually` specialized to the canonical family and projected
`globalWitness_to_hInDag W`, exposing both forcing and slack payloads in a
single reusable shape for L1. It is kernel-checked and keeps imports clean.

## Why this is YELLOW and not RED/GREEN

- **Not GREEN**: no full constructive proof of
  `IsoStrongFamilyEventually ...` for all global witnesses.
- **Not RED**: no full structural contradiction proof against all candidate
  `(yYes, D)` choices under slack.
- **YELLOW**: a useful partial theorem landed and narrows L1 entry points.

## Required audits and commands

Executed required commands:
- `lake build PnP3 Pnp4`
- `./scripts/check.sh`
- `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4`
- `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/IsoStrongConclusionProbe.lean`

All passed in this run.

## Exact missing L1 theorem(s)

Primary missing theorem family (informal names):
1. `agreement_subcube_cardinality_lower_bound`
2. `canonical_yes_class_count_upper_bound_sYES1`
3. `exists_valid_agreeing_not_yes_under_slack`

Together they should yield the Direction N theorem directly.

## Next action

Open L1 multi-session probe focused on the three blocking lemmas above and then
finish Direction N theorem in the same staging surface.

YELLOW_PARTIAL_LANDING
