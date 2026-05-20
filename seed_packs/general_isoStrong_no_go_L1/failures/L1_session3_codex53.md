# L1 session 3 structured failure (codex53)

## Executive verdict
INCONCLUSIVE_NEEDS_L2

## Attempted targets
- is_consistent_general_diagonal_table_implies_trace_in_image
- general_diagonal_z_not_yes_of_label_not_in_trace_image
- exists_valid_agreeing_not_yes_under_general_slack

## Why blocked
1. **Bridge from `z ∈ (gapSliceOfParams p).Yes` to language witness in this module context**
   - In `GeneralIsoStrongNoGoProbe`, helper lemmas used by the canonical probe (`gapSlice_yes_iff`, `gapPartialMCSP_Language_eq_true_iff_yes`) were not directly available under current imports/namespace assumptions.
   - A direct `simpa [gapSliceOfParams]` gave shape mismatches around the expected domain of `gapPartialMCSP_Language` in this file, indicating additional coercion/arity plumbing is required before extracting `∃ C, C.size ≤ p.sYES ∧ is_consistent C ...`.

2. **Trace-family qualification and coercion friction**
   - `traceCircuitOnRows`/`boundedSizeTrace_image_card_lt_of_slack` are in `Pnp3.Tests.CircuitCountTraceBoundProbe`; unqualified use caused elaboration failures.
   - Even with qualification, final cardinality goal expected exponent in one normal form while the derived bound arrived in another, requiring an explicit normalisation bridge.

3. **Subtype-indexed row extraction mismatch**
   - In the consistency-to-trace lemma, the row index from `((Finset.univ \ D).attach)` produced coercion mismatches when feeding `assignmentIndex_vecOfNat_eq`; additional local coercion lemmas are needed to avoid fragile `simp` failures.

## Precise blockers
- A stable local theorem in this file equivalent to:
  `x ∈ (gapSliceOfParams p).Yes → ∃ C : Circuit p.n, C.size ≤ p.sYES ∧ is_consistent C (decodePartial x)`
  with the exact `x` type used in this probe.
- A coercion-normalisation lemma for indices from `((Finset.univ \ D).attach)` to `Fin (Partial.tableLen p.n)` compatible with `assignmentIndex_vecOfNat_eq`.
- A normalisation step connecting
  `2 ^ ((Finset.univ \ D).card)` and the expected local exponent form in the final composition goal.

## Next action
open_general_isoStrong_no_go_L2_design
