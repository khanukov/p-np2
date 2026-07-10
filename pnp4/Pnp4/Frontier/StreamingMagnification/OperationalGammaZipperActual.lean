import Pnp4.Frontier.StreamingMagnification.OperationalGammaZipperGlobal

/-!
# Finite-tape execution bridge for the gamma zipper

`OperationalGammaZipperGlobal` proves the complete trace using an unbounded
natural-coordinate facade.  This module relates that facade step-for-step to
the repository's actual `TM.Configuration`, provided the finite tape has the
elementary head room required to avoid right-boundary clamping.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalGammaZipper

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity

abbrev GammaExecutionTM := gammaZipper.executionTM

/-- Agreement of an actual finite-tape configuration with the
natural-coordinate facade on every allocated cell. -/
def FiniteNatAgree {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (natural : NatConfig) : Prop :=
  actual.state = natural.state /\
    actual.head.val = natural.head /\
      forall index, actual.tape index = natural.tape index.val

theorem moveHead_val_eq_moveNat {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (naturalHead : Nat) (move : Move)
    (hhead : actual.head.val = naturalHead)
    (hroom : naturalHead + 1 < GammaExecutionTM.tapeLength inputLength) :
    (actual.moveHead move).val = moveNat naturalHead move := by
  cases move with
  | left =>
      by_cases hzero : naturalHead = 0
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
  | stay => simp [TM.Configuration.moveHead, moveNat, hhead]
  | right => simp [TM.Configuration.moveHead, moveNat, hhead, hroom]

theorem natStep_head_le_succ (natural : NatConfig) :
    (natStep natural).head <= natural.head + 1 := by
  unfold natStep
  generalize gammaZipper.step natural.state (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  cases move <;> simp [moveNat] <;> omega

theorem natRun_head_le (natural : NatConfig) (steps : Nat) :
    (natRun natural steps).head <= natural.head + steps := by
  induction steps with
  | zero => simp [natRun]
  | succ steps ih =>
      rw [natRun_succ]
      exact le_trans (natStep_head_le_succ _) (by omega)

theorem finiteNatAgree_step {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (natural : NatConfig)
    (hagrees : FiniteNatAgree actual natural)
    (hroom : natural.head + 1 < GammaExecutionTM.tapeLength inputLength) :
    FiniteNatAgree (GammaExecutionTM.stepConfig actual) (natStep natural) := by
  rcases hagrees with ⟨hstate, hhead, htape⟩
  have hscan :
      actual.tape actual.head = natural.tape natural.head := by
    rw [htape actual.head, hhead]
  generalize hresult :
    gammaZipper.step natural.state (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  unfold FiniteNatAgree
  simp only [TM.stepConfig, natStep, GammaExecutionTM,
    OperationalTM.executionTM]
  rw [hstate, hscan, hresult]
  refine ⟨rfl, moveHead_val_eq_moveNat actual natural.head move hhead hroom,
    ?_⟩
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

theorem gammaRunConfig_succ_front {inputLength steps : Nat}
    (actual : GammaExecutionTM.Configuration inputLength) :
    GammaExecutionTM.runConfig actual (steps + 1) =
      GammaExecutionTM.runConfig (GammaExecutionTM.stepConfig actual) steps := by
  unfold TM.runConfig
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply
      (TM.stepConfig (M := GammaExecutionTM)) steps actual

theorem natRun_succ_front (natural : NatConfig) (steps : Nat) :
    natRun natural (steps + 1) = natRun (natStep natural) steps := by
  unfold natRun
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply natStep steps natural

theorem finiteNatAgree_run {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (natural : NatConfig) (steps : Nat)
    (hagrees : FiniteNatAgree actual natural)
    (hroom : natural.head + steps <
      GammaExecutionTM.tapeLength inputLength) :
    FiniteNatAgree (GammaExecutionTM.runConfig actual steps)
      (natRun natural steps) := by
  induction steps generalizing actual natural with
  | zero => simpa [TM.runConfig, natRun] using hagrees
  | succ steps ih =>
      rw [gammaRunConfig_succ_front, natRun_succ_front]
      apply ih
      · exact finiteNatAgree_step actual natural hagrees (by omega)
      · have hstep := natStep_head_le_succ natural
        omega

/-! ## The repository `TM.initialConfig` for a canonical gamma frame -/

def gammaFrameInput (payload : List Bool) :
    Boolcube.Point (2 * payload.length + 2) :=
  fun index =>
    (initialFrame payload.length payload)[index.val]'(by
      rw [initialFrame_length]
      omega)

theorem initialConfig_finiteNatAgree (payload : List Bool) :
    FiniteNatAgree
      (GammaExecutionTM.initialConfig (gammaFrameInput payload))
      (canonicalInitialConfig payload (fun _ => false)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro index
  unfold TM.initialConfig canonicalInitialConfig
  dsimp only
  unfold framedTape
  by_cases hinput : index.val < 2 * payload.length + 2
  · simp only [hinput, dite_true, gammaFrameInput]
    have hframe : index.val < (initialFrame payload.length payload).length := by
      rw [initialFrame_length]
      omega
    rw [List.getElem?_eq_getElem hframe]
  · have hframe :
        (initialFrame payload.length payload)[index.val]? = none := by
      rw [List.getElem?_eq_none_iff]
      rw [initialFrame_length]
      omega
    simp [hinput, hframe]

theorem gammaFinishTime_lt_tapeLength (k : Nat) :
    gammaFinishTime k < GammaExecutionTM.tapeLength (2 * k + 2) := by
  simp only [gammaFinishTime, gammaBodyTime, GammaExecutionTM,
    TM.tapeLength, OperationalTM.executionTM, gammaZipper]
  rw [show 1 + (5 * k * k + 4 * k + 1) =
    5 * k * k + 4 * k + 2 by omega]
  change 5 * k * k + 4 * k + 2 <
    2 * k + 2 + ((2 * k + 2) ^ 3 + 3) + 1
  have hexpand :
      2 * k + 2 + ((2 * k + 2) ^ 3 + 3) + 1 =
        (5 * k * k + 4 * k + 2) +
          (8 * k * k * k + 19 * k * k + 22 * k + 12) := by
    ring
  rw [hexpand]
  omega

/-- The actual repository finite-tape semantics agrees with the exact useful
natural-coordinate endpoint.  First-hit control is proved separately in
`OperationalGammaZipperActive`. -/
theorem gammaExecution_runConfig_finish (payload : List Bool) :
    FiniteNatAgree
      (GammaExecutionTM.runConfig
        (GammaExecutionTM.initialConfig (gammaFrameInput payload))
        (gammaFinishTime payload.length))
      (canonicalFinalConfig payload (fun _ => false)) := by
  have hagrees := finiteNatAgree_run
    (GammaExecutionTM.initialConfig (gammaFrameInput payload))
    (canonicalInitialConfig payload (fun _ => false))
    (gammaFinishTime payload.length)
    (initialConfig_finiteNatAgree payload)
    (by
      simpa [canonicalInitialConfig] using
        gammaFinishTime_lt_tapeLength payload.length)
  rw [natRun_gammaZipper_standalone] at hagrees
  exact hagrees

theorem gammaRunConfig_add {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (first second : Nat) :
    GammaExecutionTM.runConfig actual (first + second) =
      GammaExecutionTM.runConfig
        (GammaExecutionTM.runConfig actual first) second := by
  unfold TM.runConfig
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem gammaStepConfig_state_done {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (hdone : actual.state = .done) :
    (GammaExecutionTM.stepConfig actual).state = .done := by
  unfold TM.stepConfig
  simp [GammaExecutionTM, OperationalTM.executionTM, gammaZipper, hdone]

theorem gammaRunConfig_state_done {inputLength : Nat}
    (actual : GammaExecutionTM.Configuration inputLength)
    (steps : Nat) (hdone : actual.state = .done) :
    (GammaExecutionTM.runConfig actual steps).state = .done := by
  induction steps generalizing actual with
  | zero => simpa [TM.runConfig] using hdone
  | succ steps ih =>
      rw [gammaRunConfig_succ_front]
      exact ih (GammaExecutionTM.stepConfig actual)
        (gammaStepConfig_state_done actual hdone)

theorem gammaFinishTime_le_runTime (k : Nat) :
    gammaFinishTime k <= GammaExecutionTM.runTime (2 * k + 2) := by
  simp only [gammaFinishTime, gammaBodyTime, GammaExecutionTM,
    OperationalTM.executionTM, gammaZipper]
  rw [show 1 + (5 * k * k + 4 * k + 1) =
    5 * k * k + 4 * k + 2 by omega]
  have hexpand :
      (2 * k + 2) ^ 3 + 3 =
        (5 * k * k + 4 * k + 2) +
          (8 * k * k * k + 19 * k * k + 20 * k + 9) := by
    ring
  rw [hexpand]
  omega

/-- Consequently the state is still `done` at the repository machine's
longer canonical cubic clock. -/
theorem gammaExecution_run_state_done (payload : List Bool) :
    (GammaExecutionTM.run (gammaFrameInput payload)).state = .done := by
  let initial := GammaExecutionTM.initialConfig (gammaFrameInput payload)
  let finish := gammaFinishTime payload.length
  have hfinish :
      (GammaExecutionTM.runConfig initial finish).state = .done := by
    have hagrees := gammaExecution_runConfig_finish payload
    exact hagrees.1
  have hle : finish <=
      GammaExecutionTM.runTime (2 * payload.length + 2) := by
    exact gammaFinishTime_le_runTime payload.length
  unfold TM.run
  change
    (GammaExecutionTM.runConfig initial
      (GammaExecutionTM.runTime (2 * payload.length + 2))).state = .done
  rw [show GammaExecutionTM.runTime (2 * payload.length + 2) =
      finish +
        (GammaExecutionTM.runTime (2 * payload.length + 2) - finish) by
    omega]
  rw [gammaRunConfig_add]
  exact gammaRunConfig_state_done _ _ hfinish

/-- One-sided correctness for canonical finite gamma inputs in the actual
repository execution semantics.  This is not a parser-soundness converse. -/
theorem gammaZipper_accepts_frame (payload : List Bool) :
    gammaZipper.accepts (2 * payload.length + 2) (gammaFrameInput payload) =
      true := by
  unfold OperationalTM.accepts
  rw [gammaExecution_run_state_done]
  rfl

end OperationalGammaZipper
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_head_le
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.gammaExecution_runConfig_finish
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.gammaExecution_run_state_done
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.gammaZipper_accepts_frame
