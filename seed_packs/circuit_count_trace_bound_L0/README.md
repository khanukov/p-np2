# circuit_count_trace_bound_L0

Seed pack for the L0 Lean probe landing four counting bricks needed to
generalise the canonical iso-strong conclusion-side refutation.

Triggering D0 audit:
`seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md`
(verdict `NEEDS_LEAN_PROBE`, next action `open_circuit_count_trace_bound_L0`).

Scope:
- Add one Lean file under `pnp3/Tests/` providing the brick set:
  `circuitCountBound_le_succ`, `circuitCountBound_mono`,
  `circuitCountBound_le_of_le`, `traceCircuitOnRows`,
  `boundedSizeTrace_image_card_le`,
  `boundedSizeTrace_image_card_le_sNO_minus_one`, and the optional
  strict-slack wrapper `boundedSizeTrace_image_card_lt_of_slack`.
- Register the module in `lakefile.lean` so it builds as part of the
  `PnP3` library.
- No endpoint, spec, JSONL, NoGoLog, known_guards, or trust-root edits.
  No `axiom` / `opaque` / `sorry` / `admit` / `native_decide`.

Downstream consumer (not in this pack):
`open_general_isoStrong_no_go_L1` — assembles the generalised
diagonal contradiction over arbitrary `IsoStrongFamilyEventually`
using these bricks.
