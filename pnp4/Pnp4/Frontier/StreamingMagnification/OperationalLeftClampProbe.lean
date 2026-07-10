import Pnp4.Frontier.StreamingMagnification.OperationalUniformity
import Mathlib.Tactic.DeriveFintype

/-!
# A tape-preserving probe for the physical left clamp

This module gives a fixed finite-control primitive which distinguishes a head
at cell `0` from a head at a positive natural coordinate.  The tape alphabet
is still only `Bool`, so the probe first remembers the bit under the head and
the bit immediately to its right.  It then writes the complement of the
remembered right-hand bit under the original head and performs a left/right
bounce.

At the left clamp the bounce lands on the right-hand cell, which contains the
remembered bit.  Away from the clamp it lands back on the marked original
cell, which contains its complement.  The controller can therefore classify
the two cases without assuming a reserved tape symbol.  It restores the sole
modified cell and returns to the original head coordinate after at most six
steps.  The construction is a local operational primitive; it does not by
itself decode a request or prove a lower bound.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalLeftClampProbe

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity

/-- The control stores only two tape bits.  In `done atClamp`, `atClamp = true`
records that the starting head was cell `0`. -/
inductive ProbeState where
  | saveHead
  | saveRight (headBit : Bool)
  | markHead (headBit rightBit : Bool)
  | bounce (headBit rightBit : Bool)
  | classify (headBit rightBit : Bool)
  | restoreZero (headBit : Bool)
  | done (atClamp : Bool)
  deriving DecidableEq, Fintype

/-- Fixed transition table for the left-clamp probe. -/
def leftClampProbe : OperationalTM where
  state := ProbeState
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := .saveHead
  step := fun state scanned =>
    match state with
    | .saveHead => (.saveRight scanned, scanned, Move.right)
    | .saveRight headBit =>
        (.markHead headBit scanned, scanned, Move.left)
    | .markHead headBit rightBit =>
        (.bounce headBit rightBit, !rightBit, Move.left)
    | .bounce headBit rightBit =>
        (.classify headBit rightBit, scanned, Move.right)
    | .classify headBit rightBit =>
        if scanned = rightBit then
          (.restoreZero headBit, scanned, Move.left)
        else
          (.done false, headBit, Move.stay)
    | .restoreZero headBit => (.done true, headBit, Move.stay)
    | .done atClamp => (.done atClamp, scanned, Move.stay)
  -- The additive exponent term makes the canonical clock at least six even
  -- for the empty input; the controller is already absorbing once done.
  exponent := 6
  output := fun state =>
    match state with
    | .done atClamp => atClamp
    | _ => false

@[simp] theorem leftClampProbe_state_card :
    Fintype.card leftClampProbe.state = 19 := by
  decide

@[simp] theorem leftClampProbe_clock (inputLength : Nat) :
    leftClampProbe.executionTM.runTime inputLength = inputLength ^ 6 + 6 := by
  rfl

/-! ## Natural-coordinate execution -/

/-- Natural-coordinate tape update. -/
def writeNat (tape : Nat -> Bool) (position : Nat) (bit : Bool) :
    Nat -> Bool :=
  fun query => if query = position then bit else tape query

/-- Natural-coordinate movement with the repository's clamped-left rule. -/
def moveNat (position : Nat) : Move -> Nat
  | .left => position - 1
  | .stay => position
  | .right => position + 1

/-- Proof facade for the exact fixed transition table. -/
structure NatConfig where
  state : ProbeState
  head : Nat
  tape : Nat -> Bool

/-- One natural-coordinate probe transition. -/
def natStep (config : NatConfig) : NatConfig :=
  let result := leftClampProbe.step config.state (config.tape config.head)
  { state := result.1
    head := moveNat config.head result.2.2
    tape := writeNat config.tape config.head result.2.1 }

/-- Exact iteration of the natural-coordinate transition. -/
def natRun (config : NatConfig) (steps : Nat) : NatConfig :=
  Nat.iterate natStep steps config

@[simp] theorem writeNat_same (tape : Nat -> Bool) (position : Nat) :
    writeNat tape position (tape position) = tape := by
  funext query
  by_cases hquery : query = position
  · subst query
    simp [writeNat]
  · simp [writeNat, hquery]

theorem writeNat_eq_self_of_eq {tape : Nat -> Bool} {position : Nat}
    {bit : Bool} (hbit : tape position = bit) :
    writeNat tape position bit = tape := by
  rw [<- hbit]
  exact writeNat_same tape position

@[simp] theorem writeNat_apply_same (tape : Nat -> Bool) (position : Nat)
    (bit : Bool) :
    writeNat tape position bit position = bit := by
  simp [writeNat]

@[simp] theorem writeNat_apply_ne (tape : Nat -> Bool) (position query : Nat)
    (bit : Bool) (hquery : query ≠ position) :
    writeNat tape position bit query = tape query := by
  simp [writeNat, hquery]

@[simp] theorem writeNat_writeNat_same (tape : Nat -> Bool)
    (position : Nat) (first second : Bool) :
    writeNat (writeNat tape position first) position second =
      writeNat tape position second := by
  funext query
  by_cases hquery : query = position
  · subst query
    simp [writeNat]
  · simp [writeNat, hquery]

@[simp] theorem natStep_saveHead (head : Nat) (tape : Nat -> Bool) :
    natStep ⟨.saveHead, head, tape⟩ =
      ⟨.saveRight (tape head), head + 1, tape⟩ := by
  simp [natStep, leftClampProbe, moveNat]

@[simp] theorem natStep_saveRight (head : Nat) (tape : Nat -> Bool)
    (headBit : Bool) :
    natStep ⟨.saveRight headBit, head, tape⟩ =
      ⟨.markHead headBit (tape head), head - 1, tape⟩ := by
  simp [natStep, leftClampProbe, moveNat]

@[simp] theorem natStep_markHead (head : Nat) (tape : Nat -> Bool)
    (headBit rightBit : Bool) :
    natStep ⟨.markHead headBit rightBit, head, tape⟩ =
      ⟨.bounce headBit rightBit, head - 1,
        writeNat tape head (!rightBit)⟩ := by
  simp [natStep, leftClampProbe, moveNat]

@[simp] theorem natStep_bounce (head : Nat) (tape : Nat -> Bool)
    (headBit rightBit : Bool) :
    natStep ⟨.bounce headBit rightBit, head, tape⟩ =
      ⟨.classify headBit rightBit, head + 1, tape⟩ := by
  simp [natStep, leftClampProbe, moveNat]

theorem natStep_classify_eq (head : Nat) (tape : Nat -> Bool)
    (headBit rightBit : Bool) (hbit : tape head = rightBit) :
    natStep ⟨.classify headBit rightBit, head, tape⟩ =
      ⟨.restoreZero headBit, head - 1, tape⟩ := by
  have hwrite : writeNat tape head rightBit = tape :=
    writeNat_eq_self_of_eq hbit
  simp [natStep, leftClampProbe, moveNat, hbit, hwrite]

theorem natStep_classify_ne (head : Nat) (tape : Nat -> Bool)
    (headBit rightBit : Bool) (hbit : tape head ≠ rightBit) :
    natStep ⟨.classify headBit rightBit, head, tape⟩ =
      ⟨.done false, head, writeNat tape head headBit⟩ := by
  simp [natStep, leftClampProbe, moveNat, hbit]

@[simp] theorem natStep_restoreZero (head : Nat) (tape : Nat -> Bool)
    (headBit : Bool) :
    natStep ⟨.restoreZero headBit, head, tape⟩ =
      ⟨.done true, head, writeNat tape head headBit⟩ := by
  simp [natStep, leftClampProbe, moveNat]

@[simp] theorem natStep_done (head : Nat) (tape : Nat -> Bool)
    (atClamp : Bool) :
    natStep ⟨.done atClamp, head, tape⟩ =
      ⟨.done atClamp, head, tape⟩ := by
  simp [natStep, leftClampProbe, moveNat]

/-- At cell `0`, six transitions report the clamp, return the head to `0`,
and restore the tape exactly. -/
theorem natRun_six_zero (tape : Nat -> Bool) :
    natRun ⟨.saveHead, 0, tape⟩ 6 = ⟨.done true, 0, tape⟩ := by
  change natStep (natStep (natStep (natStep (natStep (natStep
    ⟨.saveHead, 0, tape⟩))))) = ⟨.done true, 0, tape⟩
  rw [natStep_saveHead, natStep_saveRight, natStep_markHead,
    natStep_bounce]
  have hright : writeNat tape 0 (!tape 1) 1 = tape 1 := by
    simp [writeNat]
  rw [natStep_classify_eq _ _ _ _ hright, natStep_restoreZero]
  simp

/-- At every positive coordinate, six transitions report that the clamp was
not hit, return to the starting coordinate, and restore the tape exactly. -/
theorem natRun_six_positive (head : Nat) (tape : Nat -> Bool)
    (hhead : 0 < head) :
    natRun ⟨.saveHead, head, tape⟩ 6 =
      ⟨.done false, head, tape⟩ := by
  change natStep (natStep (natStep (natStep (natStep (natStep
    ⟨.saveHead, head, tape⟩))))) = ⟨.done false, head, tape⟩
  rw [natStep_saveHead, natStep_saveRight]
  simp only [Nat.add_sub_cancel]
  rw [natStep_markHead, natStep_bounce]
  have hback : head - 1 + 1 = head := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hhead))
  rw [hback]
  have hmarker : writeNat tape head (!tape (head + 1)) head ≠
      tape (head + 1) := by
    simp only [writeNat_apply_same]
    cases tape (head + 1) <;> decide
  rw [natStep_classify_ne _ _ _ _ hmarker]
  simp

/-- Uniform endpoint statement: the output bit is exactly the proposition
that the initial natural head coordinate was zero. -/
theorem natRun_six (head : Nat) (tape : Nat -> Bool) :
    natRun ⟨.saveHead, head, tape⟩ 6 =
      ⟨.done (head = 0), head, tape⟩ := by
  by_cases hzero : head = 0
  · subst head
    simpa using natRun_six_zero tape
  · have hpositive : 0 < head := Nat.pos_of_ne_zero hzero
    simpa [hzero] using natRun_six_positive head tape hpositive

/-- The six-step endpoint preserves every tape cell. -/
theorem natRun_six_tape (head : Nat) (tape : Nat -> Bool) :
    (natRun ⟨.saveHead, head, tape⟩ 6).tape = tape := by
  rw [natRun_six]

/-- The endpoint returns the head to its initial coordinate. -/
theorem natRun_six_head (head : Nat) (tape : Nat -> Bool) :
    (natRun ⟨.saveHead, head, tape⟩ 6).head = head := by
  rw [natRun_six]

/-- The endpoint's output distinguishes exactly `head = 0` from `head > 0`. -/
theorem natRun_six_output (head : Nat) (tape : Nat -> Bool) :
    leftClampProbe.output (natRun ⟨.saveHead, head, tape⟩ 6).state =
      decide (head = 0) := by
  rw [natRun_six]
  rfl

/-! ## Sharp bridge to the actual finite-tape semantics -/

/-- The actual finite-tape carrier of the probe. -/
abbrev ProbeExecutionTM := leftClampProbe.executionTM

/-- Agreement between an actual finite configuration and the
natural-coordinate facade on every allocated tape cell. -/
def ProbeFiniteNatAgree {inputLength : Nat}
    (actual : ProbeExecutionTM.Configuration inputLength)
    (natural : NatConfig) : Prop :=
  actual.state = natural.state /\
    actual.head.val = natural.head /\
      forall index, actual.tape index = natural.tape index.val

/-- Movement agrees with natural coordinates under the sharp condition that
room is supplied only when this particular transition moves right. -/
theorem probeMoveHead_val_eq_moveNat {inputLength : Nat}
    (actual : ProbeExecutionTM.Configuration inputLength)
    (naturalHead : Nat) (move : Move)
    (hhead : actual.head.val = naturalHead)
    (hright : move = .right ->
      naturalHead + 1 < ProbeExecutionTM.tapeLength inputLength) :
    (actual.moveHead move).val = moveNat naturalHead move := by
  cases move with
  | left =>
      by_cases hzero : naturalHead = 0
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
      · simp [TM.Configuration.moveHead, moveNat, hhead, hzero]
  | stay => simp [TM.Configuration.moveHead, moveNat, hhead]
  | right =>
      have hroom : actual.head.val + 1 <
          ProbeExecutionTM.tapeLength inputLength := by
        simpa [hhead] using hright rfl
      unfold TM.Configuration.moveHead
      rw [dif_pos hroom]
      simp [moveNat, hhead]

/-- A single actual transition agrees with the natural transition.  Unlike a
generic `head + steps` bridge, the hypothesis asks for right room only when
the transition table actually chooses `Move.right`. -/
theorem probeFiniteNatAgree_step {inputLength : Nat}
    (actual : ProbeExecutionTM.Configuration inputLength)
    (natural : NatConfig)
    (hagrees : ProbeFiniteNatAgree actual natural)
    (hright :
      (leftClampProbe.step natural.state
        (natural.tape natural.head)).2.2 = .right ->
      natural.head + 1 < ProbeExecutionTM.tapeLength inputLength) :
    ProbeFiniteNatAgree (ProbeExecutionTM.stepConfig actual)
      (natStep natural) := by
  rcases hagrees with ⟨hstate, hhead, htape⟩
  have hscan : actual.tape actual.head =
      natural.tape natural.head := by
    rw [htape actual.head, hhead]
  generalize hresult :
    leftClampProbe.step natural.state
      (natural.tape natural.head) = result
  rcases result with ⟨nextState, written, move⟩
  unfold ProbeFiniteNatAgree
  simp only [TM.stepConfig, natStep,
    OperationalTM.executionTM]
  rw [hstate, hscan, hresult]
  refine ⟨rfl,
    probeMoveHead_val_eq_moveNat actual natural.head move hhead ?_, ?_⟩
  · intro hmove
    apply hright
    rw [hresult]
    exact hmove
  · intro index
    by_cases hindex : index = actual.head
    · subst index
      simp [TM.Configuration.write, writeNat, hhead]
    · have hval : index.val ≠ natural.head := by
        intro heq
        apply hindex
        apply Fin.ext
        exact heq.trans hhead.symm
      simp [TM.Configuration.write, writeNat, hindex, hval, htape index]

/-- Extend an actual finite tape by false cells to obtain a total natural
tape.  Only its values on allocated indices are used by the bridge. -/
def actualTapeNat {inputLength : Nat}
    (actual : ProbeExecutionTM.Configuration inputLength) : Nat -> Bool :=
  fun position =>
    if hposition : position < ProbeExecutionTM.tapeLength inputLength then
      actual.tape ⟨position, hposition⟩
    else
      false

@[simp] theorem actualTapeNat_allocated {inputLength : Nat}
    (actual : ProbeExecutionTM.Configuration inputLength)
    (index : Fin (ProbeExecutionTM.tapeLength inputLength)) :
    actualTapeNat actual index.val = actual.tape index := by
  unfold actualTapeNat
  simp only [index.isLt, dite_true]

/-- Exact six-step transfer.  The only right-room premise is `c + 1 < L`,
because the trace visits no coordinate to the right of `c + 1`. -/
theorem probeFiniteNatAgree_run_six {inputLength c : Nat}
    (actual : ProbeExecutionTM.Configuration inputLength)
    (tape : Nat -> Bool)
    (hagrees : ProbeFiniteNatAgree actual ⟨.saveHead, c, tape⟩)
    (hroom : c + 1 < ProbeExecutionTM.tapeLength inputLength) :
    ProbeFiniteNatAgree
      (ProbeExecutionTM.runConfig actual 6)
      (natRun ⟨.saveHead, c, tape⟩ 6) := by
  by_cases hzero : c = 0
  · subst c
    let marked := writeNat tape 0 (!tape 1)
    let n₀ : NatConfig := ⟨.saveHead, 0, tape⟩
    let n₁ : NatConfig := ⟨.saveRight (tape 0), 1, tape⟩
    let n₂ : NatConfig := ⟨.markHead (tape 0) (tape 1), 0, tape⟩
    let n₃ : NatConfig := ⟨.bounce (tape 0) (tape 1), 0, marked⟩
    let n₄ : NatConfig := ⟨.classify (tape 0) (tape 1), 1, marked⟩
    let n₅ : NatConfig := ⟨.restoreZero (tape 0), 0, marked⟩
    let n₆ : NatConfig := ⟨.done true, 0, tape⟩
    have h₁ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig actual) n₁ := by
      have hstep := probeFiniteNatAgree_step actual n₀ (by simpa [n₀] using hagrees)
        (by
          intro _
          simpa [n₀] using hroom)
      simpa [n₀, n₁] using hstep
    have h₂ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig actual)) n₂ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig actual) n₁ h₁ (by
          intro hmove
          simp [n₁, leftClampProbe] at hmove)
      simpa [n₁, n₂] using hstep
    have h₃ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig actual))) n₃ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig actual)) n₂ h₂ (by
          intro hmove
          simp [n₂, leftClampProbe] at hmove)
      simpa [n₂, n₃, marked] using hstep
    have h₄ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig actual)))) n₄ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig actual))) n₃ h₃ (by
          intro _
          simpa [n₃] using hroom)
      simpa [n₃, n₄] using hstep
    have hrightBit : marked 1 = tape 1 := by
      simp [marked]
    have h₅ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig
                (ProbeExecutionTM.stepConfig actual))))) n₅ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig actual)))) n₄ h₄ (by
          intro hmove
          simp [n₄, leftClampProbe, hrightBit] at hmove)
      simpa [n₄, n₅, natStep_classify_eq _ _ _ _ hrightBit] using hstep
    have h₆ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig
                (ProbeExecutionTM.stepConfig
                  (ProbeExecutionTM.stepConfig actual)))))) n₆ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig
                (ProbeExecutionTM.stepConfig actual))))) n₅ h₅ (by
          intro hmove
          simp [n₅, leftClampProbe] at hmove)
      simpa [n₅, n₆, marked] using hstep
    rw [natRun_six_zero]
    simpa [TM.runConfig, n₆] using h₆
  · have hpositive : 0 < c := Nat.pos_of_ne_zero hzero
    have hback : c - 1 + 1 = c :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
    let marked := writeNat tape c (!tape (c + 1))
    let n₀ : NatConfig := ⟨.saveHead, c, tape⟩
    let n₁ : NatConfig := ⟨.saveRight (tape c), c + 1, tape⟩
    let n₂ : NatConfig :=
      ⟨.markHead (tape c) (tape (c + 1)), c, tape⟩
    let n₃ : NatConfig :=
      ⟨.bounce (tape c) (tape (c + 1)), c - 1, marked⟩
    let n₄ : NatConfig :=
      ⟨.classify (tape c) (tape (c + 1)), c, marked⟩
    let n₅ : NatConfig := ⟨.done false, c, tape⟩
    let n₆ : NatConfig := ⟨.done false, c, tape⟩
    have h₁ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig actual) n₁ := by
      have hstep := probeFiniteNatAgree_step actual n₀ (by simpa [n₀] using hagrees)
        (by
          intro _
          simpa [n₀] using hroom)
      simpa [n₀, n₁] using hstep
    have h₂ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig actual)) n₂ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig actual) n₁ h₁ (by
          intro hmove
          simp [n₁, leftClampProbe] at hmove)
      simpa [n₁, n₂] using hstep
    have h₃ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig actual))) n₃ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig actual)) n₂ h₂ (by
          intro hmove
          simp [n₂, leftClampProbe] at hmove)
      simpa [n₂, n₃, marked] using hstep
    have h₄ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig actual)))) n₄ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig actual))) n₃ h₃ (by
          intro _
          have : c - 1 + 1 < ProbeExecutionTM.tapeLength inputLength := by
            omega
          simpa [n₃] using this)
      simpa [n₃, n₄, hback] using hstep
    have hmarker : marked c ≠ tape (c + 1) := by
      simp only [marked, writeNat_apply_same]
      cases tape (c + 1) <;> decide
    have h₅ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig
                (ProbeExecutionTM.stepConfig actual))))) n₅ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig actual)))) n₄ h₄ (by
          intro hmove
          simp [n₄, leftClampProbe, hmarker] at hmove)
      simpa [n₄, n₅, natStep_classify_ne _ _ _ _ hmarker, marked] using hstep
    have h₆ : ProbeFiniteNatAgree
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig
                (ProbeExecutionTM.stepConfig
                  (ProbeExecutionTM.stepConfig actual)))))) n₆ := by
      have hstep := probeFiniteNatAgree_step
        (ProbeExecutionTM.stepConfig
          (ProbeExecutionTM.stepConfig
            (ProbeExecutionTM.stepConfig
              (ProbeExecutionTM.stepConfig
                (ProbeExecutionTM.stepConfig actual))))) n₅ h₅ (by
          intro hmove
          simp [n₅, leftClampProbe] at hmove)
      simpa [n₅, n₆] using hstep
    rw [natRun_six_positive c tape hpositive]
    simpa [TM.runConfig, n₆] using h₆

/-- Main actual finite-tape theorem.  Six steps classify the initial head,
return the same `Fin` head, and restore the tape extensionally. -/
theorem runConfig_six_exact {inputLength : Nat}
    (config : ProbeExecutionTM.Configuration inputLength)
    (hstate : config.state = .saveHead)
    (hroom : config.head.val + 1 <
      ProbeExecutionTM.tapeLength inputLength) :
    let final := ProbeExecutionTM.runConfig config 6
    final.state = .done (config.head.val = 0) /\
      final.head = config.head /\
        final.tape = config.tape := by
  let tape := actualTapeNat config
  have hinitial : ProbeFiniteNatAgree config
      ⟨.saveHead, config.head.val, tape⟩ := by
    refine ⟨hstate, rfl, ?_⟩
    intro index
    symm
    exact actualTapeNat_allocated config index
  have hagrees := probeFiniteNatAgree_run_six config tape hinitial hroom
  rw [natRun_six] at hagrees
  rcases hagrees with ⟨hfinalState, hfinalHead, hfinalTape⟩
  refine ⟨hfinalState, ?_, ?_⟩
  · apply Fin.ext
    exact hfinalHead
  · funext index
    rw [hfinalTape index]
    exact actualTapeNat_allocated config index

/-- State projection of the sharp actual endpoint. -/
theorem runConfig_six_state {inputLength : Nat}
    (config : ProbeExecutionTM.Configuration inputLength)
    (hstate : config.state = .saveHead)
    (hroom : config.head.val + 1 <
      ProbeExecutionTM.tapeLength inputLength) :
    (ProbeExecutionTM.runConfig config 6).state =
      .done (config.head.val = 0) :=
  (runConfig_six_exact config hstate hroom).1

/-- Head projection of the sharp actual endpoint. -/
theorem runConfig_six_head {inputLength : Nat}
    (config : ProbeExecutionTM.Configuration inputLength)
    (hstate : config.state = .saveHead)
    (hroom : config.head.val + 1 <
      ProbeExecutionTM.tapeLength inputLength) :
    (ProbeExecutionTM.runConfig config 6).head = config.head :=
  (runConfig_six_exact config hstate hroom).2.1

/-- Tape projection of the sharp actual endpoint. -/
theorem runConfig_six_tape {inputLength : Nat}
    (config : ProbeExecutionTM.Configuration inputLength)
    (hstate : config.state = .saveHead)
    (hroom : config.head.val + 1 <
      ProbeExecutionTM.tapeLength inputLength) :
    (ProbeExecutionTM.runConfig config 6).tape = config.tape :=
  (runConfig_six_exact config hstate hroom).2.2

/-- The actual endpoint output is exactly the initial left-clamp predicate. -/
theorem runConfig_six_output {inputLength : Nat}
    (config : ProbeExecutionTM.Configuration inputLength)
    (hstate : config.state = .saveHead)
    (hroom : config.head.val + 1 <
      ProbeExecutionTM.tapeLength inputLength) :
    leftClampProbe.output
      (ProbeExecutionTM.runConfig config 6).state =
      decide (config.head.val = 0) := by
  rw [runConfig_six_state config hstate hroom]
  rfl

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalLeftClampProbe.runConfig_six_exact

end OperationalLeftClampProbe
end StreamingMagnification
end Frontier
end Pnp4
