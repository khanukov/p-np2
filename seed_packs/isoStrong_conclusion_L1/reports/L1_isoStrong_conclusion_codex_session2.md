# L1 iso-strong conclusion — session 2 (codex)

## 1. Executive verdict

YELLOW_ONE_OF_THREE_LANDED

## 2. What landed

- `traceSize1CandidateOnRows`
- `exists_label_not_in_finite_trace_family`
- `diagonalPartialTable`
- `diagonal_z_valid`
- `diagonal_z_agrees_on_D`

## 3. Corrected trace argument

The session now separates two notions of trace:

- **Variable-index trace** (`Fin n` coordinates), suitable for one-hot assignment embeddings.
- **Row-trace on truth-table rows** (`Fin (Partial.tableLen n)` coordinates), which is the correct object for partial truth-table diagonalisation.

`traceSize1CandidateOnRows` evaluates size-1 candidates directly on row indices:

- constants map to constant labels;
- projection `input i` maps row `r` to `Nat.testBit r.val i.val`.

This fixes the prior mismatch where embedding free coordinates into `Fin n` could accidentally treat truth-table rows as variable indices.

## 4. Remaining blockers

Main blocker to full session goal:

- Missing bridge lemma from YES-witness circuits (`Circuit n`) with `size ≤ 1` to `Size1Candidate n`, plus consistency transport to row-trace equality on `(Finset.univ \ D).attach`.

Concretely still unlanded:

- `diagonal_z_not_yes_of_label_not_trace`
- `exists_valid_agreeing_not_yes_under_slack`

The current file has valid/agreeing construction pieces, but not the final `¬ z ∈ Yes` contradiction.

## 5. Next action

open_isoStrong_conclusion_L1_session_3
