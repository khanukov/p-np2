# L1 general iso-strong no-go — session 3

## 1. Executive verdict

**YELLOW_PARTIAL_GENERAL_L1**

## 2. What landed

- `is_consistent_general_diagonal_table_implies_trace_in_image`
- `general_diagonal_z_not_yes_of_label_not_in_trace_image`

## 3. General not-YES bridge status

Closed for the partial target: from
`encodePartial (generalDiagonalPartialTable ...) ∈ (gapSliceOfParams p).Yes`,
we derive a bounded-size consistent circuit witness, convert consistency on the
general diagonal table into exact trace equality on free rows, and contradict
`label ∉ image(traceCircuitOnRows ...)`.

## 4. Remaining blockers

- `exists_valid_agreeing_not_yes_under_general_slack` currently triggers a deterministic elaboration timeout (`whnf`, heartbeat limit) in this file context.
- Precise remaining statement:
  ```lean
  theorem exists_valid_agreeing_not_yes_under_general_slack
      (p : GapPartialMCSPParams)
      (yYes : Core.BitVec (partialInputLen p))
      (hValidYes : ValidEncoding p yYes)
      (D : Finset (Fin (Partial.tableLen p.n)))
      (hSlack :
        circuitCountBound p.n (p.sNO - 1) <
          2 ^ ((Finset.univ \ D).card)) :
      ∃ z : Core.BitVec (partialInputLen p),
        ValidEncoding p z ∧
        AgreeOnValues D yYes z ∧
        ¬ z ∈ (gapSliceOfParams p).Yes
  ```

## 5. Next action

**open_general_isoStrong_no_go_L1_session_4**
