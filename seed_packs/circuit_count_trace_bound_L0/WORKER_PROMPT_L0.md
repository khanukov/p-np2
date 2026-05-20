# Worker prompt — circuit-count trace bound L0

Branch: `main`.

Task type: **L0 Lean probe**.

## Goal

Land one Lean file `pnp3/Tests/CircuitCountTraceBoundProbe.lean` and
register it in `lakefile.lean`.

The file must provide the four counting bricks specified in the D0
audit (`seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md`,
§8):

1. `circuitCountBound_le_succ` — one-step monotonicity in size.
2. `circuitCountBound_mono` / `circuitCountBound_le_of_le` —
   monotonicity in size.
3. `traceCircuitOnRows` — circuit row-trace on a finite row family.
4. `boundedSizeTrace_image_card_le` — image-cardinality bound for
   bounded-size circuit traces, via existing `circuitsOfSizeAtMost` and
   `card_circuitsOfSizeAtMost_le` in `pnp3/Counting/CircuitCounting.lean`.
5. `boundedSizeTrace_image_card_le_sNO_minus_one` — `gap_ok`
   wrapper lifting `sYES` traces to the `sNO - 1` budget.

Optional: `boundedSizeTrace_image_card_lt_of_slack` — strict-slack
packaging useful for direct L1 consumption.

## Constraints

- No endpoint, spec, JSONL, NoGoLog, known_guards, or trust-root
  edits.
- No `axiom` / `opaque` / `sorry` / `admit` / `native_decide`.
- No new `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  or `P ≠ NP` claim.
- Reuse existing enumeration `circuitsOfSizeAtMost` and the cardinality
  lemma `card_circuitsOfSizeAtMost_le`; do not reimplement.
- Register the new module in `lakefile.lean` (`Glob.one
  \`Tests.CircuitCountTraceBoundProbe`) so it builds as part of `PnP3`.

## Required reading

- `seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md`
- `pnp3/Counting/CircuitCounting.lean`
  (`circuitsOfSizeAtMost`, `card_circuitsOfSizeAtMost_le`,
   `circuitCountBound`)
- `pnp3/Models/Model_PartialMCSP.lean`
  (`GapPartialMCSPParams.gap_ok`, `Partial.tableLen`)

## Commands

```sh
lake env lean pnp3/Tests/CircuitCountTraceBoundProbe.lean
lake build PnP3 Pnp4
./scripts/check.sh
rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4
```

## Required output format

```
Task: circuit-count trace bound L0
Handle: <handle>
Commit before: <hash>
Commit after: <hash>
Outcome: L0_LANDED | STRUCTURED_FAILURE
Executive verdict: GREEN_COUNTING_BRICKS_LANDED | ...
Does it unlock general iso-strong L1: yes | partial | no
Scope violations: none | <list>
```
