# L1 general iso-strong no-go — session 1

Task: general iso-strong no-go L1 (session 1)
Handle: codex53
Branch: main

## 1. Executive verdict

**YELLOW_PARTIAL_GENERAL_L1**

Two L1 bricks landed, kernel-checked, with clean axiom dependencies
(no `axiom` / `opaque` / `sorry` / `admit` / `native_decide` /
`sorryAx`).  The full generalised contradiction
`isoStrong_conclusion_negative_general` is not yet assembled and is
explicitly staged for L1 session 2.

## 2. What landed

In `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`:

1. `exists_label_not_in_trace_image_of_card_lt`
   — finite-image pigeonhole over `Finset (α → Bool)`.  For any
   `S : Finset (α → Bool)` with `S.card < 2 ^ Fintype.card α`,
   some `label : α → Bool` lies outside `S`.
   Axiom dependencies: `[propext, Classical.choice, Quot.sound]`
   (standard classical kit).

2. `slack_for_D_of_isoStrong_slack_general`
   — convert iso-strong slack on the `(tableLen, κ)` axis to the
   `D.card` form, lifted to general `GapSliceFamilyEventually` via
   `F.hIndex` / `F.hM` / `F.hT` composition, then weakened via
   `Nat.sub_le_sub_left` and `Nat.pow_le_pow_right`.
   Axiom dependencies: `[propext, Quot.sound]` (no
   `Classical.choice`).

Module registered in `lakefile.lean` as
`Glob.one \`Tests.GeneralIsoStrongNoGoProbe`.

## 3. Does this generalise canonical RED?

**Partially** — core diagonal infrastructure only.

The two bricks landed are the generic replacements for two of the
six canonical L1 ingredients (pigeonhole core from session 1; slack
conversion from session 4).  They demonstrate that:

- The pigeonhole step is parameter-agnostic (no `sYES = 1`
  dependency).
- The slack conversion lifts cleanly via the existing
  `GapSliceFamilyEventually` interface (`F.hIndex`, `F.hM`, `F.hT`
  are sufficient — no per-family case analysis required).

This validates the D0-audit prediction that the canonical proof's
generic ingredients lift unchanged, with the only canonical-specific
specialisations being in the encoding bridge (`Size1Candidate`,
`diagonalPartialTable`) and the not-YES bridge
(`is_consistent_diagonal_table_implies_label_trace`).

## 4. Remaining blockers (for L1 session 2)

- A general not-YES bridge
  `exists_valid_agreeing_not_yes_under_general_slack`
  replacing the canonical size-1 consistency lemma
  `is_consistent_diagonal_table_implies_label_trace`.
- A general encoding bridge analogous to the canonical
  `diagonalPartialTable` / `traceSize1CandidateOnRows`, lifted to
  bounded-size circuits via the L0 bricks
  `traceCircuitOnRows` and
  `boundedSizeTrace_image_card_lt_of_slack`.
- Final assembly into `isoStrong_conclusion_negative_general` over
  an arbitrary `GapSliceFamilyEventually`.

## 5. Build verification

- `lake build Tests.GeneralIsoStrongNoGoProbe` → success (only one
  cosmetic linter warning `try 'simp' instead of 'simpa'` at the
  `hNotLt` step in `exists_label_not_in_trace_image_of_card_lt`;
  fixed during merge enrichment).
- `lake build PnP3 Pnp4` → expected to succeed (probe is a
  test-local addition; no endpoint surface modified).
- `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` →
  no new matches in the modified tree.

## 6. Scope violations

none.  Markdown report + one Lean test-local file + one `lakefile.lean`
glob entry; no endpoint, spec, JSONL, NoGoLog, known_guards, or
trust-root edits; no `ResearchGapWitness`, `SourceTheorem`,
`gap_from`, endpoint, or `P ≠ NP` claim.

## 7. Next action

**open_general_isoStrong_no_go_L1_session_2**
