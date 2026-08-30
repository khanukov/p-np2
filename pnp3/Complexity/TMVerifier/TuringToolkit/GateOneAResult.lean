import Complexity.TMVerifier.TuringToolkit.GateOneARepair

/-!
# S9 dependency-closed five-tag gate-result boundary (2026-08-30)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

This module consumes the exact canonical `aRepairDone` endpoint of S8b without
changing its architecture.  Three exact transitions finish a non-constant
gate: `aRepairDone → aResultStart → readAStart → combineStart`.  The
middle row alone applies the latched residual to operand A and installs
`g1ResultCtx`; the existing result dispatch performs the final handoff.

`const` retains its distinct pass-B bypass.  `g1GateResultSteps` is therefore
an honest three-way schedule for all five tags.  Successful runs stop at the
`combineStart` boundary with the canonical tape and head zero; S10b consumes
that boundary immediately.  This module itself states no output, acceptance,
rejection, or `TM.accepts` claim.  A `none` specification remains a separate semantic
case; in particular, no successful output is asserted for an out-of-bounds
request.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## The two new result-row configurations and their exact atoms -/

/-- Canonical S9 handoff immediately after the S8b endpoint. -/
def g1AResultStartConfig (r : G1Request) (b v : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length 0 (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .aResultStart .p0 false false false (g1AWalkCtx r b v)

/-- The executed `aRepairDone → aResultStart` row preserves everything. -/
theorem g1CS_step_aRepairDone_result (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aRepairDone .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .aResultStart .p0 false false false ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape (g1ARepairDoneState ctx)
    (g1AResultStartState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_aRepairDone_result phase .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- The executed result row applies exactly `ctx.res` to `ctx.vB`. -/
theorem g1CS_step_aResultStart_apply (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aResultStart .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .readAStart .p0 false false false
        (g1ResultCtx (ctx.res.apply ctx.vB)) := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape (g1AResultStartState ctx)
    (g1ReadAState (g1ResultCtx (ctx.res.apply ctx.vB))) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_aResultStart_apply phase .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- From the exact canonical S8b endpoint, three genuine stationary steps
apply the residual and reach the existing combine boundary. -/
theorem g1CS_aRepairDone_combine_exact (r : G1Request) (b v : Bool) :
    TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v) 3 =
      g1CombineConfig r ((g1Residual r.tag b).apply v) := by
  rw [show (3 : Nat) = 1 + (1 + 1) by omega, runConfig_add,
    g1ARepairDoneConfig, g1CS_step_aRepairDone_result, runConfig_add,
    g1CS_step_aResultStart_apply]
  rw [show g1ListTape
      ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits) =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape from by
      simpa only [g1ValidationFrames] using g1ListTape_validation_eq_initial r]
  simpa only [g1CombineConfig, g1AWalkCtx_res, g1AWalkCtx_vB] using
    g1CS_step_readAStart_result (encodeG1 r).length 0
      (g1_route_lt_tapeLength r 0 (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      (g1ResultCtx ((g1Residual r.tag b).apply v)) rfl

/-! ## Exact schedules and unchanged clock -/

/-- Real-initial binary S8b schedule plus the three result handoffs. -/
def g1BACombineSteps (r : G1Request) : Nat := g1ABinaryRepairSteps r + 3

/-- Real-initial unary S8b schedule plus the three result handoffs. -/
def g1UACombineSteps (r : G1Request) : Nat := g1AUnaryRepairSteps r + 3

theorem g1BACombineSteps_eq (r : G1Request) :
    g1BACombineSteps r = g1ABinaryCursorSteps r +
      (8 * r.arg1 ^ 2 + (8 * r.arg2 + 70) * r.arg1 +
        4 * r.tag.units + 12 * r.arg2 + 60) := by
  rw [g1BACombineSteps, g1ABinaryRepairSteps, g1AWalkRepairSteps_eq]
  omega

theorem g1UACombineSteps_eq (r : G1Request) :
    g1UACombineSteps r = g1AUnaryCursorSteps r +
      (8 * r.arg1 ^ 2 + (8 * r.arg2 + 70) * r.arg1 +
        4 * r.tag.units + 12 * r.arg2 + 60) := by
  rw [g1UACombineSteps, g1AUnaryRepairSteps, g1AWalkRepairSteps_eq]
  omega

/-- The exact dependency-closed five-tag schedule. -/
def g1GateResultSteps (r : G1Request) : Nat :=
  if r.tag = .const then g1ConstActivatedSteps r
  else if r.tag.arity = 2 then g1BACombineSteps r
  else g1UACombineSteps r

theorem g1GateResultSteps_const (r : G1Request) (ht : r.tag = .const) :
    g1GateResultSteps r = g1ConstActivatedSteps r := by
  rw [g1GateResultSteps, if_pos ht]

theorem g1GateResultSteps_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1GateResultSteps r = g1BACombineSteps r := by
  have hne : r.tag ≠ .const := by rcases ht with h | h <;> rw [h] <;> decide
  have h2 : r.tag.arity = 2 := by rcases ht with h | h <;> rw [h] <;> rfl
  rw [g1GateResultSteps, if_neg hne, if_pos h2]

theorem g1GateResultSteps_unary (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1GateResultSteps r = g1UACombineSteps r := by
  have hne : r.tag ≠ .const := by rcases ht with h | h <;> rw [h] <;> decide
  have h2 : r.tag.arity ≠ 2 := by rcases ht with h | h <;> rw [h] <;> decide
  rw [g1GateResultSteps, if_neg hne, if_neg h2]

theorem g1ResultSq_succ (N : Nat) :
    (N + 1) ^ 2 = N ^ 2 + (2 * N + 1) := by
  rw [Nat.pow_two, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

theorem g1ResultClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  rw [g1Clock, g1ResultSq_succ, Nat.mul_pow,
    show (4 : Nat) ^ 2 = 16 from rfl]
  omega

theorem g1BACombineSteps_le_clock (r : G1Request) :
    g1BACombineSteps r ≤ g1Clock (encodeG1 r).length := by
  rw [g1BACombineSteps]
  refine (Nat.add_le_add_right (g1ABinaryRepairSteps_le_poly r) 3).trans ?_
  rw [g1ARepairLivePoly, encodeG1_length, g1ResultClock_quad]
  omega

theorem g1UACombineSteps_le_clock (r : G1Request) :
    g1UACombineSteps r ≤ g1Clock (encodeG1 r).length := by
  rw [g1UACombineSteps]
  refine (Nat.add_le_add_right (g1AUnaryRepairSteps_le_poly r) 3).trans ?_
  rw [g1ARepairLivePoly, encodeG1_length, g1ResultClock_quad]
  omega

theorem g1GateResultSteps_le_clock (r : G1Request) :
    g1GateResultSteps r ≤ g1Clock (encodeG1 r).length := by
  rw [g1GateResultSteps]
  split_ifs
  · exact g1ConstActivatedSteps_le_clock r
  · exact g1BACombineSteps_le_clock r
  · exact g1UACombineSteps_le_clock r

/-! ## Composition with the exact current S8b initial capstones -/

theorem g1CS_aCombine_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BACombineSteps r) =
      g1CombineConfig r ((g1Residual r.tag b).apply (v r.arg1)) := by
  rw [g1BACombineSteps, runConfig_add,
    g1CS_aRepair_binary_initial_exact r hc ht b hb v hv rest hvals]
  exact g1CS_aRepairDone_combine_exact r b (v r.arg1)

theorem g1CS_aCombine_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UACombineSteps r) =
      g1CombineConfig r ((g1Residual r.tag false).apply (v r.arg1)) := by
  rw [g1UACombineSteps, runConfig_add,
    g1CS_aRepair_unary_initial_exact r hc ht v hv rest hvals]
  exact g1CS_aRepairDone_combine_exact r false (v r.arg1)

/-- A selected operand supplies the whole finite prefix witness required by
the canonical S8b driver, without adding any runtime datum to control. -/
theorem g1Vals_prefix_witness {r : G1Request} {a : Bool}
    (ha : r.vals[r.arg1]? = some a) :
    ∃ v : Nat → Bool, (∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) ∧
      v r.arg1 = a ∧ ∃ rest : List Bool, r.vals = v 0 :: rest := by
  have harg : r.arg1 < r.vals.length :=
    (List.getElem?_eq_some_iff.1 ha).1
  let v : Nat → Bool := fun j => r.vals[j]?.getD false
  have hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j) := by
    intro j hj
    have hjlt : j < r.vals.length := by omega
    simp [v, List.getElem?_eq_getElem hjlt]
  have hva : v r.arg1 = a := by
    have h := hv r.arg1 (Nat.le_refl _)
    rw [ha] at h
    exact Option.some.inj h.symm
  have hne : r.vals ≠ [] := by
    intro hnil
    simp [hnil] at harg
  obtain ⟨x, xs, hlist⟩ := List.exists_cons_of_ne_nil hne
  have h0 := hv 0 (by omega)
  rw [hlist] at h0
  have hx : x = v 0 := Option.some.inj h0
  subst x
  exact ⟨v, hv, hva, xs, hlist⟩

/-! ## Pure-spec bridges for all five tags -/

theorem g1Spec_operands_binary {r : G1Request}
    (ht : r.tag = .and ∨ r.tag = .or) {res : Bool}
    (hs : r.spec = some res) :
    ∃ a b, r.vals[r.arg1]? = some a ∧ r.vals[r.arg2]? = some b := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  cases h1 : vals[a1]? with
  | none =>
      exfalso
      rcases ht with rfl | rfl
      · rw [G1Request.spec_and_oob (Or.inl h1)] at hs
        exact Option.noConfusion hs
      · rw [G1Request.spec_or_oob (Or.inl h1)] at hs
        exact Option.noConfusion hs
  | some a =>
      cases h2 : vals[a2]? with
      | none =>
          exfalso
          rcases ht with rfl | rfl
          · rw [G1Request.spec_and_oob (Or.inr h2)] at hs
            exact Option.noConfusion hs
          · rw [G1Request.spec_or_oob (Or.inr h2)] at hs
            exact Option.noConfusion hs
      | some b => exact ⟨a, b, rfl, rfl⟩

theorem g1Spec_operand_unary {r : G1Request}
    (ht : r.tag = .input ∨ r.tag = .not) {res : Bool}
    (hs : r.spec = some res) : ∃ a, r.vals[r.arg1]? = some a := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  cases h1 : vals[a1]? with
  | none =>
      exfalso
      rcases ht with rfl | rfl <;> simp [G1Request.spec, h1] at hs
  | some a => exact ⟨a, rfl⟩

theorem g1Spec_input_bridge {r : G1Request} (ht : r.tag = .input)
    {res : Bool} (hs : r.spec = some res) :
    r.vals[r.arg1]? = some res := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  subst tag
  by_cases h2 : a2 = 0
  · subst a2
    simpa [G1Request.spec] using hs
  · simp [G1Request.spec, h2] at hs

theorem g1Spec_not_bridge {r : G1Request} (ht : r.tag = .not)
    {res : Bool} (hs : r.spec = some res) :
    ∃ a, r.vals[r.arg1]? = some a ∧ res = !a := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  subst tag
  by_cases h2 : a2 = 0
  · subst a2
    cases h : vals[a1]? with
    | none => simp [G1Request.spec, h] at hs
    | some a =>
        refine ⟨a, rfl, ?_⟩
        simp [G1Request.spec, h] at hs
        revert hs
        cases a <;> cases res <;> decide
  · simp [G1Request.spec, h2] at hs

theorem g1Spec_and_bridge {r : G1Request} (ht : r.tag = .and)
    {res : Bool} (hs : r.spec = some res) :
    ∃ a b, r.vals[r.arg1]? = some a ∧ r.vals[r.arg2]? = some b ∧
      res = (a && b) := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  subst tag
  cases h1 : vals[a1]? with
  | none => simp [G1Request.spec, h1] at hs
  | some a =>
      cases h2 : vals[a2]? with
      | none => simp [G1Request.spec, h1, h2] at hs
      | some b =>
          refine ⟨a, b, rfl, rfl, ?_⟩
          simp [G1Request.spec, h1, h2] at hs
          exact hs.symm

theorem g1Spec_or_bridge {r : G1Request} (ht : r.tag = .or)
    {res : Bool} (hs : r.spec = some res) :
    ∃ a b, r.vals[r.arg1]? = some a ∧ r.vals[r.arg2]? = some b ∧
      res = (a || b) := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  subst tag
  cases h1 : vals[a1]? with
  | none => simp [G1Request.spec, h1] at hs
  | some a =>
      cases h2 : vals[a2]? with
      | none => simp [G1Request.spec, h1, h2] at hs
      | some b =>
          refine ⟨a, b, rfl, rfl, ?_⟩
          simp [G1Request.spec, h1, h2] at hs
          exact hs.symm

theorem g1Spec_const_bridge {r : G1Request} (ht : r.tag = .const)
    {res : Bool} (hs : r.spec = some res) :
    (r.arg1 = 0 ∧ res = false) ∨ (r.arg1 = 1 ∧ res = true) := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hs ⊢
  subst tag
  cases a2 with
  | succ a2 => simp [G1Request.spec] at hs
  | zero =>
      cases a1 with
      | zero =>
          left
          exact ⟨rfl, Option.some.inj hs.symm⟩
      | succ a1 =>
          cases a1 with
          | zero =>
              right
              exact ⟨rfl, Option.some.inj hs.symm⟩
          | succ a1 => simp [G1Request.spec] at hs

/-! ## Pure semantics to the exact machine boundary -/

theorem g1CS_gate_result_binary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (res : Bool)
    (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BACombineSteps r) = g1CombineConfig r res := by
  obtain ⟨a, b, ha, hb⟩ := g1Spec_operands_binary ht hs
  obtain ⟨v, hv, hva, rest, hvals⟩ := g1Vals_prefix_witness ha
  rw [g1CS_aCombine_binary_exact r hc ht b hb v hv rest hvals, hva,
    g1Residual_apply_spec_binary ht ha hb hs]

theorem g1CS_gate_result_unary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (res : Bool)
    (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UACombineSteps r) = g1CombineConfig r res := by
  obtain ⟨a, ha⟩ := g1Spec_operand_unary ht hs
  obtain ⟨v, hv, hva, rest, hvals⟩ := g1Vals_prefix_witness ha
  rw [g1CS_aCombine_unary_exact r hc ht v hv rest hvals, hva,
    g1Residual_apply_spec_unary ht false ha hs]

theorem g1CS_gate_result_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r) = g1CombineConfig r res := by
  rcases htag : r.tag with h | h | h | h | h
  · rw [g1GateResultSteps_unary r (Or.inl htag)]
    exact g1CS_gate_result_unary r hc (Or.inl htag) res hs
  · rw [g1GateResultSteps_const r htag]
    exact g1CS_activate_const_exact r hc htag res hs
  · rw [g1GateResultSteps_unary r (Or.inr htag)]
    exact g1CS_gate_result_unary r hc (Or.inr htag) res hs
  · rw [g1GateResultSteps_binary r (Or.inl htag)]
    exact g1CS_gate_result_binary r hc (Or.inl htag) res hs
  · rw [g1GateResultSteps_binary r (Or.inr htag)]
    exact g1CS_gate_result_binary r hc (Or.inr htag) res hs

/-! ## Exact boundary projections and stability -/

theorem g1CS_gate_result_ctx (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).state.snd.ctx = g1ResultCtx res := by
  rw [g1CS_gate_result_exact r hc res hs]
  rfl

theorem g1CS_gate_result_pass_vB (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r)).state.snd.ctx.pass = true ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r)).state.snd.ctx.vB = res := by
  rw [g1CS_gate_result_exact r hc res hs]
  exact ⟨rfl, rfl⟩

theorem g1CS_gate_result_head (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).head : Nat) = 0 := by
  rw [g1CS_gate_result_exact r hc res hs]
  rfl

theorem g1CS_gate_result_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).state.snd = g1CombineState (g1ResultCtx res) := by
  rw [g1CS_gate_result_exact r hc res hs]
  rfl

theorem g1CS_gate_result_tape (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_gate_result_exact r hc res hs]
  rfl

/-! ## Honest `none`/OOB separation -/

theorem g1Spec_none_of_arg1_oob (r : G1Request) (ht : r.tag ≠ .const)
    (hm : r.vals.length ≤ r.arg1) : r.spec = none := by
  have hnone : r.vals[r.arg1]? = none := List.getElem?_eq_none hm
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hnone ⊢
  cases tag with
  | const => exact absurd rfl ht
  | input => simp [G1Request.spec, hnone]
  | not => simp [G1Request.spec, hnone]
  | and => exact G1Request.spec_and_oob (Or.inl hnone)
  | or => exact G1Request.spec_or_oob (Or.inl hnone)

theorem g1Spec_none_of_arg2_oob_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (hm : r.vals.length ≤ r.arg2) :
    r.spec = none := by
  have hnone : r.vals[r.arg2]? = none := List.getElem?_eq_none hm
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht hnone ⊢
  rcases ht with rfl | rfl
  · exact G1Request.spec_and_oob (Or.inr hnone)
  · exact G1Request.spec_or_oob (Or.inr hnone)

/-- The total semantic split.  Only the `some` branch receives a machine-result
claim; the `none` branch deliberately asserts no output, acceptance, or
rejection behavior. -/
theorem g1CS_gate_result_or_spec_none (r : G1Request) (hc : r.Canonical) :
    (∃ res, r.spec = some res ∧
      TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r) = g1CombineConfig r res) ∨ r.spec = none := by
  cases hs : r.spec with
  | none => exact Or.inr rfl
  | some res => exact Or.inl ⟨res, rfl, g1CS_gate_result_exact r hc res hs⟩

theorem g1CombineState_ne_oob (res : Bool) (ctx : G1Ctx) :
    g1CombineState (g1ResultCtx res) ≠ g1OOBState ctx := by
  intro h
  have hm : G1Mode.combineStart = G1Mode.bOOB := congrArg G1State.mode h
  exact G1Mode.noConfusion hm

theorem g1CS_gate_result_false_ne_oob (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = some false) (ctx : G1Ctx) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).state.snd ≠ g1OOBState ctx := by
  rw [g1CS_gate_result_state r hc false hs]
  exact g1CombineState_ne_oob false ctx

/-! ## Named literal five-tag probes -/

namespace G1AResultProbes

def reqInputT : G1Request := ⟨.input, 0, 0, [true]⟩
def reqNotF : G1Request := ⟨.not, 0, 0, [true]⟩
def reqAndF : G1Request := ⟨.and, 0, 1, [true, false]⟩
def reqOrT : G1Request := ⟨.or, 0, 1, [false, true]⟩
def reqConstF : G1Request := ⟨.const, 0, 0, []⟩
def reqConstT : G1Request := ⟨.const, 1, 0, []⟩

theorem literal_canonical :
    reqInputT.Canonical ∧ reqNotF.Canonical ∧ reqAndF.Canonical ∧
      reqOrT.Canonical ∧ reqConstF.Canonical ∧ reqConstT.Canonical := by
  decide

theorem literal_specs :
    reqInputT.spec = some true ∧ reqNotF.spec = some false ∧
      reqAndF.spec = some false ∧ reqOrT.spec = some true ∧
      reqConstF.spec = some false ∧ reqConstT.spec = some true := by
  decide

theorem literal_steps :
    g1GateResultSteps reqInputT = 195 ∧
      g1GateResultSteps reqNotF = 243 ∧
      g1GateResultSteps reqAndF = 430 ∧
      g1GateResultSteps reqOrT = 454 ∧
      g1GateResultSteps reqConstF = 117 ∧
      g1GateResultSteps reqConstT = 133 := by
  decide

theorem literal_clocks :
    g1Clock (encodeG1 reqInputT).length = 558080 ∧
      g1Clock (encodeG1 reqNotF).length = 861184 ∧
      g1Clock (encodeG1 reqAndF).length = 1438720 ∧
      g1Clock (encodeG1 reqOrT).length = 1664000 ∧
      g1Clock (encodeG1 reqConstF).length = 558080 ∧
      g1Clock (encodeG1 reqConstT).length = 701440 := by
  decide

theorem literal_results :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 195 =
          g1CombineConfig reqInputT true ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 243 =
          g1CombineConfig reqNotF false ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 430 =
          g1CombineConfig reqAndF false ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 454 =
          g1CombineConfig reqOrT true ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 117 =
          g1CombineConfig reqConstF false ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 133 =
          g1CombineConfig reqConstT true := by
  have hi := g1CS_gate_result_exact reqInputT literal_canonical.1 true
    literal_specs.1
  have hn := g1CS_gate_result_exact reqNotF literal_canonical.2.1 false
    literal_specs.2.1
  have ha := g1CS_gate_result_exact reqAndF literal_canonical.2.2.1 false
    literal_specs.2.2.1
  have ho := g1CS_gate_result_exact reqOrT literal_canonical.2.2.2.1 true
    literal_specs.2.2.2.1
  have hcf := g1CS_gate_result_exact reqConstF
    literal_canonical.2.2.2.2.1 false literal_specs.2.2.2.2.1
  have hct := g1CS_gate_result_exact reqConstT
    literal_canonical.2.2.2.2.2 true literal_specs.2.2.2.2.2
  rw [literal_steps.1] at hi
  rw [literal_steps.2.1] at hn
  rw [literal_steps.2.2.1] at ha
  rw [literal_steps.2.2.2.1] at ho
  rw [literal_steps.2.2.2.2.1] at hcf
  rw [literal_steps.2.2.2.2.2] at hct
  exact ⟨hi, hn, ha, ho, hcf, hct⟩

end G1AResultProbes

end Pnp3.Internal.PsubsetPpoly.TM
