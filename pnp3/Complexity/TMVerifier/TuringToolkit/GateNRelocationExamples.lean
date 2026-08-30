import Complexity.TMVerifier.TuringToolkit.GateNRelocation

/-!
# GN-3A literal relocation capstones

These examples instantiate the generic theorem with `G1M` as both source and
target, identity state injection, input lengths `W = 4`, `N = 20`, base `7`,
and a visibly nonconstant ambient tape.  The short capstone takes two genuine
left-moving repair transitions from local head two.  The separate left-clamp
counterexample witnesses why positivity, not merely a left-moving row, is
required by the safety predicate.

The last example uses the genuine `aRepairStart` left-moving row at local head
zero.  The source clamps at zero while a positive-base shifted head moves to
`base - 1`; hence unconditional relocation without local step safety is false.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM.GNRelocationExamples

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

def capSource : Configuration (M := G1M) 4 where
  state := ⟨g1CS.toPhased.startPhase, g1State .aRepairStart .p0⟩
  head := gnSourceIndex 4 2 (by decide)
  tape := frameListTape G1Frame.bof.bits

def capAmbient : Fin (G1M.tapeLength 20) -> Bool :=
  fun i => decide (i.val % 2 = 0)

def capInject : G1M.state -> G1M.state := id

theorem cap_inject_injective : Function.Injective capInject := by
  intro a b h
  exact h

theorem cap_room : 7 + gnLocalSpan 4 <= G1M.tapeLength 20 :=
  gn_g1_target_room_of_add_sixteen (W := 4) (N := 20) (base := 7)
    (by decide) (by decide)

theorem cap_head_local : (capSource.head : Nat) < gnLocalSpan 4 := by decide

theorem cap_source_move :
    (G1M.step capSource.state (capSource.tape capSource.head)).snd.snd =
      Move.left := rfl

theorem cap_step_safe : G1LocalStepSafe capSource := by
  refine ⟨cap_head_local, ?_, ?_⟩
  · intro h
    decide
  · intro h
    rw [cap_source_move] at h
    contradiction

theorem cap_step_delegates : G1StepDelegates G1M capInject capSource := rfl

theorem cap_source_step_head :
    ((TM.stepConfig (M := G1M) capSource).head : Nat) = 1 := by
  rw [stepConfig_head, cap_source_move,
    Configuration.moveHead_left_val_of_pos capSource (by decide)]
  rfl

theorem cap_source_step_move :
    (G1M.step (TM.stepConfig (M := G1M) capSource).state
      ((TM.stepConfig (M := G1M) capSource).tape
        (TM.stepConfig (M := G1M) capSource).head)).snd.snd = Move.left := rfl

/-- Literal shifted one-step capstone. -/
theorem capstone_shifted_one_step :
    TM.stepConfig (M := G1M)
        (gnShiftConfig G1M 7 capInject capAmbient capSource cap_room cap_head_local) =
      gnShiftConfig G1M 7 capInject capAmbient
        (TM.stepConfig (M := G1M) capSource) cap_room
        (gn_local_step_safe_next_head capSource cap_step_safe) :=
  gn_delegate_step_shift capInject capAmbient capSource cap_room
    cap_step_safe cap_step_delegates

theorem cap_run_safe_two : G1RunSafe capSource 2 := by
  intro j hj
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · exact cap_step_safe
  · rw [runConfig_one]
    refine ⟨?_, ?_, ?_⟩
    · rw [cap_source_step_head]
      decide
    · intro h
      rw [cap_source_step_head]
      decide
    · intro h
      rw [cap_source_step_move] at h
      contradiction

theorem cap_run_delegates_two : G1RunDelegates G1M capInject capSource 2 := by
  intro j hj
  exact rfl

/-- Literal two-step run capstone. -/
theorem capstone_shifted_short_run :
    TM.runConfig (M := G1M)
        (gnShiftConfig G1M 7 capInject capAmbient capSource cap_room cap_head_local) 2 =
      gnShiftConfig G1M 7 capInject capAmbient
        (TM.runConfig (M := G1M) capSource 2) cap_room
        (gn_run_safe_endpoint_head capSource cap_head_local cap_run_safe_two) :=
  gn_delegate_run_shift capInject capAmbient capSource cap_room cap_head_local
    cap_run_safe_two cap_run_delegates_two

/-- A concrete outside cell is the nonconstant ambient bit at every prefix. -/
theorem capstone_outside_every_prefix (j : Nat) (hj : j <= 2) :
    (TM.runConfig (M := G1M)
      (gnShiftConfig G1M 7 capInject capAmbient capSource cap_room cap_head_local)
      j).tape ⟨0, by simp [TM.tapeLength]⟩ = true := by
  have h := gn_delegate_run_shift_outside_prefix capInject capAmbient capSource
    cap_room cap_head_local cap_run_safe_two cap_run_delegates_two hj
    (⟨0, by simp [TM.tapeLength]⟩ : Fin (G1M.tapeLength 20))
    (Or.inl (by decide))
  simpa [capAmbient] using h

/-- Numerically, the footprint is nine cells and the final frame at offset
four fits; the eight-cell (`W + 4`) candidate does not. -/
theorem capstone_footprint_exact :
    gnLocalSpan 4 = 9 ∧ 4 + 4 < gnLocalSpan 4 ∧ ¬ (4 + 4 < 4 + 4) := by
  decide

def leftZeroSource : Configuration (M := G1M) 0 where
  state := ⟨g1CS.toPhased.startPhase, g1State .aRepairStart .p0⟩
  head := gnSourceIndex 0 0 (by decide)
  tape := fun _ => false

theorem left_zero_head_local :
    (leftZeroSource.head : Nat) < gnLocalSpan 0 := by decide

theorem left_zero_target_room :
    1 + gnLocalSpan 0 <= G1M.tapeLength 16 := by
  exact gn_g1_target_room_of_add_sixteen (W := 0) (N := 16) (base := 1)
    (by decide) (by decide)

theorem left_zero_source_next_local :
    ((TM.stepConfig (M := G1M) leftZeroSource).head : Nat) < gnLocalSpan 0 := by
  rw [stepConfig_head]
  have hmove :
      (G1M.step leftZeroSource.state
        (leftZeroSource.tape leftZeroSource.head)).snd.snd = Move.left := rfl
  rw [hmove, Configuration.moveHead_left_clamp _ (by decide)]
  exact left_zero_head_local

/-- Genuine counterexample: the left move at local zero clamps in the source,
but after shifting to positive base it moves left.  This is precisely the case
excluded by `G1LocalStepSafe`. -/
theorem capstone_left_zero_unconditional_shift_false :
    TM.stepConfig (M := G1M)
        (gnShiftConfig G1M 1 capInject (fun _ => false) leftZeroSource
          left_zero_target_room left_zero_head_local) ≠
      gnShiftConfig G1M 1 capInject (fun _ => false)
        (TM.stepConfig (M := G1M) leftZeroSource) left_zero_target_room
        left_zero_source_next_local := by
  intro h
  let shifted := gnShiftConfig G1M 1 capInject (fun _ => false) leftZeroSource
    left_zero_target_room left_zero_head_local
  have hscan : shifted.tape shifted.head =
      leftZeroSource.tape leftZeroSource.head := by
    exact gnShiftConfig_bit_inside capInject (fun _ => false) leftZeroSource
      left_zero_target_room left_zero_head_local left_zero_head_local
  have hmove :
      (G1M.step leftZeroSource.state
        (leftZeroSource.tape leftZeroSource.head)).snd.snd = Move.left := rfl
  have htarget : ((TM.stepConfig (M := G1M) shifted).head : Nat) = 0 := by
    rw [stepConfig_head]
    change ((Configuration.moveHead (c := shifted)
      (G1M.step (capInject leftZeroSource.state)
        (shifted.tape shifted.head)).snd.snd) : Nat) = 0
    rw [hscan, show capInject leftZeroSource.state = leftZeroSource.state from rfl,
      hmove, Configuration.moveHead_left_val_of_pos shifted (by decide)]
    rfl
  have hrhs :
      ((gnShiftConfig G1M 1 capInject (fun _ => false)
        (TM.stepConfig (M := G1M) leftZeroSource) left_zero_target_room
        left_zero_source_next_local).head : Nat) = 1 := by
    rw [gnShiftConfig_head_val]
    have hsource :
        ((TM.stepConfig (M := G1M) leftZeroSource).head : Nat) = 0 := by
      rw [stepConfig_head, hmove,
        Configuration.moveHead_left_clamp leftZeroSource (by decide)]
      rfl
    omega
  have hhead := congrArg (fun c : Configuration (M := G1M) 16 => c.head.val) h
  change ((TM.stepConfig (M := G1M) shifted).head : Nat) =
    ((gnShiftConfig G1M 1 capInject (fun _ => false)
      (TM.stepConfig (M := G1M) leftZeroSource) left_zero_target_room
      left_zero_source_next_local).head : Nat) at hhead
  rw [htarget, hrhs] at hhead
  contradiction

end Pnp3.Internal.PsubsetPpoly.TM.GNRelocationExamples
