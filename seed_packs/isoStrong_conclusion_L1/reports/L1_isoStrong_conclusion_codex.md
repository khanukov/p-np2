# 1. Executive verdict

YELLOW_ONE_OF_THREE_LANDED

# 2. What landed

- `traceSize1CandidateOnRows`
- `exists_label_not_in_finite_trace_family`
- `diagonalPartialTable`
- `diagonal_z_valid`
- `diagonal_z_agrees_on_D`

# 3. Corrected trace argument

The corrected route must trace size-1 candidates on **truth-table rows** (`Fin (Partial.tableLen n)`), not on variable indices (`Fin n`).

- The older helper `traceSize1CandidateOnFree` is indexed by an embedding into `Fin n`, so it captures projections against variable coordinates.
- For diagonalization over a partial table subcube `(Finset.univ \ D).attach`, we need labels on row IDs (assignments), and candidate evaluations must read assignment bits via `Nat.testBit row i`.
- `traceSize1CandidateOnRows` implements exactly that row-level semantics:
  - constants map to constant traces,
  - input projection `i` maps row `r` to the `i`-th bit of `r.val`.

This aligns the finite pigeonhole step with the MCSP value-coordinate layer.

# 4. Remaining blockers

- Missing conversion lemma from `z ∈ (gapSliceOfParams p).Yes` with `p.sYES = 1` to an explicit `Size1Candidate p.n` whose row-trace matches all defined rows of `decodePartial z`.
- Missing/unfinished bridge lemma from consistency of that witness with `decodePartial (encodePartial (diagonalPartialTable ...))` to equality with `label` on `(Finset.univ \ D).attach`.
- End-to-end theorem still pending:
  - `exists_valid_agreeing_not_yes_under_slack`

# 5. Next action

open_isoStrong_conclusion_L1_session_3
