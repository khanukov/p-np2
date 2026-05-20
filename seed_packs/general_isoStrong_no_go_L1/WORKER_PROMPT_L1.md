# Worker prompt — general iso-strong no-go L1 (session 1)

Branch: `main`.

Task type: **L1 Lean probe** (session 1 of an expected multi-session
chain mirroring the canonical iso-strong L1 sessions 1–4).

## Goal

Land one Lean file
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean` and register it in
`lakefile.lean` (`Glob.one \`Tests.GeneralIsoStrongNoGoProbe`).

The file must provide two L1 bricks:

1. `exists_label_not_in_trace_image_of_card_lt` — generic finite-image
   pigeonhole: for any `S : Finset (α → Bool)` with
   `S.card < 2 ^ Fintype.card α`, some labeling `α → Bool` lies outside
   `S`.  Parameter-agnostic replacement for the canonical
   `exists_trace_not_size1_of_card_lt` (L1 session 1).

2. `slack_for_D_of_isoStrong_slack_general` — convert iso-strong slack
   on the `(tableLen, κ)` axis to the `D.card` form needed by the
   diagonal step, at general `GapSliceFamilyEventually`.  Compose
   `F.hIndex`, `F.hM`, `F.hT` to align `F.Mof n (F.Tof n β)` with
   `circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1)`,
   then weaken `κv` to `D.card` via `Nat.sub_le_sub_left` and
   `Nat.pow_le_pow_right`.  Parameter-agnostic replacement for the
   canonical `slack_for_D_of_isoStrong_slack` (L1 session 4).

## Constraints

- File-local to `pnp3/Tests/`; non-endpoint.
- Register in `lakefile.lean` so it builds with `lake build PnP3 Pnp4`.
- No endpoint, spec, JSONL, NoGoLog, known_guards, or trust-root
  edits.
- No `axiom` / `opaque` / `sorry` / `admit` / `native_decide`.
- No new `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  or `P ≠ NP` claim.
- Reuse existing L0 bricks from
  `pnp3/Tests/CircuitCountTraceBoundProbe.lean`
  (`circuitCountBound_le_succ`, `circuitCountBound_mono`,
  `circuitCountBound_le_of_le`, `traceCircuitOnRows`,
  `boundedSizeTrace_image_card_le`,
  `boundedSizeTrace_image_card_le_sNO_minus_one`,
  `boundedSizeTrace_image_card_lt_of_slack`).

## Required reading

- `seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md`
- `seed_packs/circuit_count_trace_bound_L0/reports/L0_circuit_count_trace_bound_codex53.md`
- `pnp3/Tests/CircuitCountTraceBoundProbe.lean`
- `pnp3/Tests/IsoStrongConclusionProbe.lean`
  (canonical session 1 & session 4 references)
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean`
  (`GapSliceFamilyEventually` structure with `hIndex`, `hM`, `hT`,
  `tableLen`)

## Commands

```sh
lake build Tests.GeneralIsoStrongNoGoProbe
lake build PnP3 Pnp4
./scripts/check.sh
rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4
```

## Required output format

```
Task: general iso-strong no-go L1 session 1
Handle: <handle>
Commit before: <hash>
Commit after: <hash>
Outcome: L1_LANDED | STRUCTURED_FAILURE
Executive verdict: YELLOW_PARTIAL_GENERAL_L1 | ...
Does it generalize canonical RED: partial | yes | no
Scope violations: none | <list>
```
