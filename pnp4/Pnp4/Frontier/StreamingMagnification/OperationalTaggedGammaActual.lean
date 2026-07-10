import Pnp4.Frontier.StreamingMagnification.OperationalTaggedGammaGlobal

/-!
# Finite-tape execution bridge for the tagged gamma front end

`OperationalTaggedGammaGlobal` proves the exact canonical three-field trace
on natural-number tape coordinates.  This module transfers that trace to the
repository's actual finite-tape semantics.  Its final acceptance theorem is
one-sided: it concerns the exact canonical bitstring constructed below and
does not assert a parser-soundness converse for arbitrary inputs.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalTaggedGamma

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity
open OperationalGammaZipper

abbrev TaggedExecutionTM := taggedGamma.executionTM

/-- Agreement of an actual finite-tape configuration with the tagged
natural-coordinate facade on every allocated cell. -/
def TaggedFiniteNatAgree {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (natural : TaggedNatConfig) : Prop :=
  actual.state = natural.state /\
    actual.head.val = natural.head /\
      forall index, actual.tape index = natural.tape index.val

theorem taggedMoveHead_val_eq_moveNat {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (naturalHead : Nat) (move : Move)
    (hhead : actual.head.val = naturalHead)
    (hroom : naturalHead + 1 < TaggedExecutionTM.tapeLength inputLength) :
    (actual.moveHead move).val = moveNat naturalHead move := by
  cases move with
  | left =>
      by_cases hzero : naturalHead = 0
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
  | stay => simp [TM.Configuration.moveHead, moveNat, hhead]
  | right => simp [TM.Configuration.moveHead, moveNat, hhead, hroom]

theorem taggedNatStep_head_le_succ (natural : TaggedNatConfig) :
    (taggedNatStep natural).head <= natural.head + 1 := by
  unfold taggedNatStep
  generalize taggedGamma.step natural.state (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  cases move <;> simp [moveNat] <;> omega

theorem taggedNatRun_head_le (natural : TaggedNatConfig) (steps : Nat) :
    (taggedNatRun natural steps).head <= natural.head + steps := by
  induction steps with
  | zero => simp [taggedNatRun]
  | succ steps ih =>
      rw [taggedNatRun_succ]
      exact le_trans (taggedNatStep_head_le_succ _) (by omega)

theorem taggedFiniteNatAgree_step {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (natural : TaggedNatConfig)
    (hagrees : TaggedFiniteNatAgree actual natural)
    (hroom : natural.head + 1 < TaggedExecutionTM.tapeLength inputLength) :
    TaggedFiniteNatAgree (TaggedExecutionTM.stepConfig actual)
      (taggedNatStep natural) := by
  rcases hagrees with ⟨hstate, hhead, htape⟩
  have hscan :
      actual.tape actual.head = natural.tape natural.head := by
    rw [htape actual.head, hhead]
  generalize hresult :
    taggedGamma.step natural.state (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  unfold TaggedFiniteNatAgree
  simp only [TM.stepConfig, taggedNatStep, TaggedExecutionTM,
    OperationalTM.executionTM]
  rw [hstate, hscan, hresult]
  refine ⟨rfl,
    taggedMoveHead_val_eq_moveNat actual natural.head move hhead hroom, ?_⟩
  intro index
  by_cases hindex : index = actual.head
  · subst index
    simp [TM.Configuration.write, writeNat, hhead]
  · have hval : index.val ≠ natural.head := by
      intro heq
      apply hindex
      apply Fin.ext
      exact heq.trans hhead.symm
    simp [TM.Configuration.write, writeNat, hindex, hval, htape index]

theorem taggedRunConfig_succ_front {inputLength steps : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength) :
    TaggedExecutionTM.runConfig actual (steps + 1) =
      TaggedExecutionTM.runConfig (TaggedExecutionTM.stepConfig actual)
        steps := by
  unfold TM.runConfig
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply
      (TM.stepConfig (M := TaggedExecutionTM)) steps actual

theorem taggedNatRun_succ_front (natural : TaggedNatConfig) (steps : Nat) :
    taggedNatRun natural (steps + 1) =
      taggedNatRun (taggedNatStep natural) steps := by
  unfold taggedNatRun
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply taggedNatStep steps natural

theorem taggedFiniteNatAgree_run {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (natural : TaggedNatConfig) (steps : Nat)
    (hagrees : TaggedFiniteNatAgree actual natural)
    (hroom : natural.head + steps <
      TaggedExecutionTM.tapeLength inputLength) :
    TaggedFiniteNatAgree (TaggedExecutionTM.runConfig actual steps)
      (taggedNatRun natural steps) := by
  induction steps generalizing actual natural with
  | zero => simpa [TM.runConfig, taggedNatRun] using hagrees
  | succ steps ih =>
      rw [taggedRunConfig_succ_front, taggedNatRun_succ_front]
      apply ih
      · exact taggedFiniteNatAgree_step actual natural hagrees (by omega)
      · have hstep := taggedNatStep_head_le_succ natural
        omega

/-! ## Exact canonical input and initial agreement -/

/-- The exact finite bitstring containing tag `179` and three canonical gamma
fields, with no ambient suffix included in the input length. -/
def taggedTripleInput (payload₁ payload₂ payload₃ : List Bool) :
    Boolcube.Point
      (tripleFootprint payload₁.length payload₂.length payload₃.length) :=
  fun index =>
    (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
      payload₃.length payload₃)[index.val]'(by
        rw [tripleInitialFrame_length rfl rfl rfl]
        exact index.isLt)

theorem taggedInitialConfig_finiteNatAgree
    (payload₁ payload₂ payload₃ : List Bool) :
    TaggedFiniteNatAgree
      (TaggedExecutionTM.initialConfig
        (taggedTripleInput payload₁ payload₂ payload₃))
      ⟨.tag0, 0,
        framedTape
          (tripleInitialFrame payload₁.length payload₁ payload₂.length
            payload₂ payload₃.length payload₃)
          (fun _ => false)⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  unfold TM.initialConfig
  dsimp only
  unfold framedTape
  by_cases hinput : index.val <
      tripleFootprint payload₁.length payload₂.length payload₃.length
  · simp only [hinput, dite_true, taggedTripleInput]
    have hframe : index.val <
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃).length := by
      rw [tripleInitialFrame_length rfl rfl rfl]
      exact hinput
    rw [List.getElem?_eq_getElem hframe]
  · have hframe :
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃)[index.val]? = none := by
      rw [List.getElem?_eq_none_iff]
      rw [tripleInitialFrame_length rfl rfl rfl]
      omega
    simp [hinput, hframe]

theorem taggedTripleTime_le_sum_square
    (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ <=
      5 * ((k₁ + k₂ + k₃) * (k₁ + k₂ + k₃)) +
        4 * (k₁ + k₂ + k₃) + 11 := by
  rw [taggedTripleTime_closed]
  have hsquares :
      (k₁ + k₂ + k₃) * (k₁ + k₂ + k₃) =
        k₁ * k₁ + k₂ * k₂ + k₃ * k₃ +
          2 * (k₁ * k₂ + k₁ * k₃ + k₂ * k₃) := by
    ring
  rw [hsquares]
  omega

/-- The useful tagged trace has enough allocated head room to be transferred
without encountering right-boundary clamping. -/
theorem taggedTripleTime_lt_tapeLength (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ <
      TaggedExecutionTM.tapeLength (tripleFootprint k₁ k₂ k₃) := by
  let total := k₁ + k₂ + k₃
  have htime :
      taggedTripleTime k₁ k₂ k₃ <=
        5 * (total * total) + 4 * total + 11 := by
    simpa [total] using taggedTripleTime_le_sum_square k₁ k₂ k₃
  have hexpand :
      (11 + 2 * total) + ((11 + 2 * total) ^ 4 + 4) + 1 =
        (5 * (total * total) + 4 * total + 11) +
          (16 * total ^ 4 + 352 * total ^ 3 +
            2899 * total ^ 2 + 10646 * total + 14646) := by
    ring
  simp only [TaggedExecutionTM, TM.tapeLength,
    OperationalTM.executionTM, taggedGamma]
  change taggedTripleTime k₁ k₂ k₃ <
    tripleFootprint k₁ k₂ k₃ +
      (tripleFootprint k₁ k₂ k₃ ^ 4 + 4) + 1
  rw [show tripleFootprint k₁ k₂ k₃ = 11 + 2 * total by
    simp [tripleFootprint, total]]
  rw [hexpand]
  omega

/-! ## Actual finite-tape endpoint and the canonical quartic clock -/

/-- Exact finite-tape agreement at the useful accepting time for the canonical
three-field bitstring. -/
theorem taggedExecution_runConfig_triple
    (payload₁ payload₂ payload₃ : List Bool) :
    TaggedFiniteNatAgree
      (TaggedExecutionTM.runConfig
        (TaggedExecutionTM.initialConfig
          (taggedTripleInput payload₁ payload₂ payload₃))
        (taggedTripleTime payload₁.length payload₂.length payload₃.length))
      ⟨.done,
        tripleFootprint payload₁.length payload₂.length payload₃.length,
        framedTape (tripleFinalFrame payload₁ payload₂ payload₃)
          (fun _ => false)⟩ := by
  have hagrees := taggedFiniteNatAgree_run
    (TaggedExecutionTM.initialConfig
      (taggedTripleInput payload₁ payload₂ payload₃))
    ⟨.tag0, 0,
      framedTape
        (tripleInitialFrame payload₁.length payload₁ payload₂.length payload₂
          payload₃.length payload₃)
        (fun _ => false)⟩
    (taggedTripleTime payload₁.length payload₂.length payload₃.length)
    (taggedInitialConfig_finiteNatAgree payload₁ payload₂ payload₃)
    (by
      simpa using taggedTripleTime_lt_tapeLength payload₁.length
        payload₂.length payload₃.length)
  rw [taggedNatRun_triple] at hagrees
  exact hagrees

theorem taggedRunConfig_add {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (first second : Nat) :
    TaggedExecutionTM.runConfig actual (first + second) =
      TaggedExecutionTM.runConfig
        (TaggedExecutionTM.runConfig actual first) second := by
  unfold TM.runConfig
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem taggedStepConfig_state_done {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (hdone : actual.state = .done) :
    (TaggedExecutionTM.stepConfig actual).state = .done := by
  unfold TM.stepConfig
  simp [TaggedExecutionTM, OperationalTM.executionTM, taggedGamma, hdone]

theorem taggedRunConfig_state_done {inputLength : Nat}
    (actual : TaggedExecutionTM.Configuration inputLength)
    (steps : Nat) (hdone : actual.state = .done) :
    (TaggedExecutionTM.runConfig actual steps).state = .done := by
  induction steps generalizing actual with
  | zero => simpa [TM.runConfig] using hdone
  | succ steps ih =>
      rw [taggedRunConfig_succ_front]
      exact ih (TaggedExecutionTM.stepConfig actual)
        (taggedStepConfig_state_done actual hdone)

theorem taggedTripleTime_le_runTime (k₁ k₂ k₃ : Nat) :
    taggedTripleTime k₁ k₂ k₃ <=
      TaggedExecutionTM.runTime (tripleFootprint k₁ k₂ k₃) := by
  let total := k₁ + k₂ + k₃
  have htime :
      taggedTripleTime k₁ k₂ k₃ <=
        5 * (total * total) + 4 * total + 11 := by
    simpa [total] using taggedTripleTime_le_sum_square k₁ k₂ k₃
  have hexpand :
      (11 + 2 * total) ^ 4 + 4 =
        (5 * (total * total) + 4 * total + 11) +
          (16 * total ^ 4 + 352 * total ^ 3 +
            2899 * total ^ 2 + 10644 * total + 14634) := by
    ring
  simp only [TaggedExecutionTM, OperationalTM.executionTM, taggedGamma]
  change taggedTripleTime k₁ k₂ k₃ <=
    tripleFootprint k₁ k₂ k₃ ^ 4 + 4
  rw [show tripleFootprint k₁ k₂ k₃ = 11 + 2 * total by
    simp [tripleFootprint, total]]
  rw [hexpand]
  omega

/-- The absorbing accepting state reached at the exact useful time remains
accepting at the machine's longer canonical quartic clock. -/
theorem taggedExecution_run_state_done
    (payload₁ payload₂ payload₃ : List Bool) :
    (TaggedExecutionTM.run
      (taggedTripleInput payload₁ payload₂ payload₃)).state = .done := by
  let inputLength :=
    tripleFootprint payload₁.length payload₂.length payload₃.length
  let initial := TaggedExecutionTM.initialConfig
    (taggedTripleInput payload₁ payload₂ payload₃)
  let finish :=
    taggedTripleTime payload₁.length payload₂.length payload₃.length
  have hfinish :
      (TaggedExecutionTM.runConfig initial finish).state = .done := by
    have hagrees :=
      taggedExecution_runConfig_triple payload₁ payload₂ payload₃
    exact hagrees.1
  have hle : finish <= TaggedExecutionTM.runTime inputLength := by
    exact taggedTripleTime_le_runTime payload₁.length payload₂.length
      payload₃.length
  unfold TM.run
  change
    (TaggedExecutionTM.runConfig initial
      (TaggedExecutionTM.runTime inputLength)).state = .done
  rw [show TaggedExecutionTM.runTime inputLength =
      finish + (TaggedExecutionTM.runTime inputLength - finish) by
    omega]
  rw [taggedRunConfig_add]
  exact taggedRunConfig_state_done _ _ hfinish

/-- One-sided acceptance of the exact canonical tag-plus-three-gamma
bitstring in the repository's actual finite-tape execution semantics. -/
theorem taggedGamma_accepts_canonical_triple
    (payload₁ payload₂ payload₃ : List Bool) :
    taggedGamma.accepts
      (tripleFootprint payload₁.length payload₂.length payload₃.length)
      (taggedTripleInput payload₁ payload₂ payload₃) = true := by
  unfold OperationalTM.accepts
  rw [taggedExecution_run_state_done]
  rfl

end OperationalTaggedGamma
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedNatRun_head_le
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedExecution_runConfig_triple
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedExecution_run_state_done
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalTaggedGamma.taggedGamma_accepts_canonical_triple
