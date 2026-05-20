# general_isoStrong_no_go_L1

L1 staging pack for the generalised iso-strong conclusion-side
no-go probe.

Triggering D0 audit:
`seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md`
(verdict `NEEDS_LEAN_PROBE`, next action `open_circuit_count_trace_bound_L0`).

Triggering L0 probe:
`seed_packs/circuit_count_trace_bound_L0/reports/L0_circuit_count_trace_bound_codex53.md`
(verdict `GREEN_COUNTING_BRICKS_LANDED`, next action
`open_general_isoStrong_no_go_L1`).

## Scope of session 1

Land two L1 bricks under `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`:

1. `exists_label_not_in_trace_image_of_card_lt` — parameter-agnostic
   finite-image pigeonhole (generic replacement for the canonical
   `exists_trace_not_size1_of_card_lt` from L1 session 1).
2. `slack_for_D_of_isoStrong_slack_general` — slack conversion from
   the `(tableLen, κ)` axis to the `D.card` form needed by the
   diagonal step, lifted to general `GapSliceFamilyEventually`
   via `F.hIndex` / `F.hM` / `F.hT` composition (generic replacement
   for canonical `slack_for_D_of_isoStrong_slack` from L1 session 4).

Verdict for session 1: `YELLOW_PARTIAL_GENERAL_L1`.

## What remains for L1 session 2

- General not-YES bridge `exists_valid_agreeing_not_yes_under_general_slack`
  replacing the canonical size-1 consistency lemma.
- Final assembly into `isoStrong_conclusion_negative_general` over
  an arbitrary `GapSliceFamilyEventually`.

## Scope policy

- Lean file lives under `pnp3/Tests/` (test-local; non-endpoint).
- No endpoint, spec, JSONL, NoGoLog, known_guards, or trust-root
  edits.
- No `axiom` / `opaque` / `sorry` / `admit` / `native_decide`.
- No new `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  or `P ≠ NP` claim.
