import Complexity.TMVerifier.TuringToolkit.Foundation
import Pnp4.Frontier.StreamingMagnification.OperationalUniformity

/-!
# Clock and physical-boundary limits of the operational TM model

The repository TM allocates

`tapeLength n = n + runTime n + 1`

cells, starts its head at zero, and moves the head by at most one cell per
transition.  Consequently its physical right clamp cannot be observed during
the `runTime n` transitions of a canonical run.  Moreover, input cells beyond
the ambient input length are initialized to `false`, so an input and an
all-zero extension have the same execution prefix until a finite-tape clamp
could intervene.

This module makes both facts explicit.  It also records a small concrete
witness showing that the external choice of final sampling time remains a real
length channel: two zero strings can have different observations solely
because their canonical clocks run for different numbers of transitions.

These are model-semantics theorems.  They do not provide a parser, a lower
bound, or a `P != NP` conclusion.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalClockBoundary

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity

universe u

/-! ## Zero extension and cross-length configuration agreement -/

/-- Append `padding` semantic zero bits to a bitstring. -/
def zeroExtend {inputLength : Nat}
    (input : Boolcube.Point inputLength) (padding : Nat) :
    Boolcube.Point (inputLength + padding) :=
  fun index =>
    if h : index.val < inputLength then input ⟨index.val, h⟩ else false

/--
Agreement between configurations whose dependent tape types use different
ambient input lengths.  State and numeric head position agree, and the two
tapes agree at every natural position allocated by both tapes.
-/
def CrossConfigAgree (machine : TM.{u}) {leftLength rightLength : Nat}
    (left : machine.Configuration leftLength)
    (right : machine.Configuration rightLength) : Prop :=
  left.state = right.state /\
    left.head.val = right.head.val /\
      forall (position : Nat)
        (hleft : position < machine.tapeLength leftLength)
        (hright : position < machine.tapeLength rightLength),
        left.tape ⟨position, hleft⟩ = right.tape ⟨position, hright⟩

/-- A repository initial tape cannot distinguish an input from an all-zero
extension on any cell present in both finite tapes. -/
theorem initialConfig_zeroExtend_agree (machine : TM.{u})
    {inputLength : Nat} (input : Boolcube.Point inputLength) (padding : Nat) :
    CrossConfigAgree machine (machine.initialConfig input)
      (machine.initialConfig (zeroExtend input padding)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro position hleft hright
  by_cases hinput : position < inputLength
  · have hextended : position < inputLength + padding := by omega
    simp [TM.initialConfig, zeroExtend, hinput, hextended]
  · by_cases hextended : position < inputLength + padding
    · simp [TM.initialConfig, zeroExtend, hinput, hextended]
    · simp [TM.initialConfig, zeroExtend, hinput, hextended]

/-- Away from the right clamp, equal numeric heads respond identically to a
common movement instruction even when their `Fin` tape types differ. -/
theorem moveHead_cross_val_eq (machine : TM.{u})
    {leftLength rightLength : Nat}
    (left : machine.Configuration leftLength)
    (right : machine.Configuration rightLength)
    (move : Move)
    (hhead : left.head.val = right.head.val)
    (hleftRoom : left.head.val + 1 < machine.tapeLength leftLength)
    (hrightRoom : right.head.val + 1 < machine.tapeLength rightLength) :
    (left.moveHead move).val = (right.moveHead move).val := by
  cases move with
  | left =>
      by_cases hzero : left.head.val = 0
      · simp [TM.Configuration.moveHead, hzero, hhead.symm]
      · have hrightZero : right.head.val ≠ 0 := by omega
        simp [TM.Configuration.moveHead, hrightZero, hhead]
  | stay => simp [TM.Configuration.moveHead, hhead]
  | right =>
      rw [TM.Configuration.moveHead_right_lt left hleftRoom]
      rw [TM.Configuration.moveHead_right_lt right hrightRoom]
      simp [hhead]

/-- One transition preserves cross-length agreement whenever neither head can
encounter its physical right clamp. -/
theorem crossConfigAgree_step (machine : TM.{u})
    {leftLength rightLength : Nat}
    (left : machine.Configuration leftLength)
    (right : machine.Configuration rightLength)
    (hagrees : CrossConfigAgree machine left right)
    (hleftRoom : left.head.val + 1 < machine.tapeLength leftLength)
    (hrightRoom : right.head.val + 1 < machine.tapeLength rightLength) :
    CrossConfigAgree machine (machine.stepConfig left)
      (machine.stepConfig right) := by
  rcases hagrees with ⟨hstate, hhead, htape⟩
  have hscan : left.tape left.head = right.tape right.head := by
    have hrightBound : left.head.val < machine.tapeLength rightLength := by
      simpa [hhead] using right.head.isLt
    have h := htape left.head.val left.head.isLt hrightBound
    have hfin :
        (⟨left.head.val, hrightBound⟩ : Fin (machine.tapeLength rightLength)) =
          right.head :=
      Fin.ext hhead
    simpa [hfin] using h
  unfold CrossConfigAgree
  simp only [TM.stepConfig]
  rw [hstate, hscan]
  refine ⟨rfl,
    moveHead_cross_val_eq machine left right _ hhead hleftRoom hrightRoom, ?_⟩
  intro position hleft hright
  by_cases hposition : position = left.head.val
  · have hleftFin :
        (⟨position, hleft⟩ : Fin (machine.tapeLength leftLength)) =
          left.head :=
      Fin.ext hposition
    have hrightFin :
        (⟨position, hright⟩ : Fin (machine.tapeLength rightLength)) =
          right.head :=
      Fin.ext (hposition.trans hhead)
    simp [TM.Configuration.write, hleftFin, hrightFin]
  · have hleftFin :
        (⟨position, hleft⟩ : Fin (machine.tapeLength leftLength)) ≠
          left.head := by
      intro heq
      apply hposition
      exact congrArg Fin.val heq
    have hrightFin :
        (⟨position, hright⟩ : Fin (machine.tapeLength rightLength)) ≠
          right.head := by
      intro heq
      apply hposition
      have hval := congrArg Fin.val heq
      omega
    simp [TM.Configuration.write, hleftFin, hrightFin,
      htape position hleft hright]

private theorem runConfig_succ_front (machine : TM.{u})
    {inputLength steps : Nat} (config : machine.Configuration inputLength) :
    machine.runConfig config (steps + 1) =
      machine.runConfig (machine.stepConfig config) steps := by
  unfold TM.runConfig
  simpa [Nat.succ_eq_add_one] using
    Function.iterate_succ_apply (TM.stepConfig (M := machine)) steps config

/-- Cross-length agreement is preserved for a whole bounded trace.  The room
hypotheses are deliberately stated from the initial heads; the generic
one-cell-per-step head bound propagates them through the induction. -/
theorem crossConfigAgree_run (machine : TM.{u})
    {leftLength rightLength steps : Nat}
    (left : machine.Configuration leftLength)
    (right : machine.Configuration rightLength)
    (hagrees : CrossConfigAgree machine left right)
    (hleftRoom : left.head.val + steps < machine.tapeLength leftLength)
    (hrightRoom : right.head.val + steps < machine.tapeLength rightLength) :
    CrossConfigAgree machine (machine.runConfig left steps)
      (machine.runConfig right steps) := by
  induction steps generalizing left right with
  | zero => simpa [TM.runConfig] using hagrees
  | succ steps ih =>
      rw [runConfig_succ_front machine left,
        runConfig_succ_front machine right]
      apply ih
      · exact crossConfigAgree_step machine left right hagrees
          (by omega) (by omega)
      · have hstep := TM.stepConfig_head_val_le_succ
          (M := machine) left
        omega
      · have hstep := TM.stepConfig_head_val_le_succ
          (M := machine) right
        omega

/-- An input and its all-zero extension have identical state, numeric head,
and common tape cells after every number of transitions for which both finite
tapes have head room. -/
theorem zeroExtend_same_trace_prefix (machine : TM.{u})
    {inputLength : Nat} (input : Boolcube.Point inputLength)
    (padding steps : Nat)
    (hshortRoom : steps < machine.tapeLength inputLength)
    (hextendedRoom : steps < machine.tapeLength (inputLength + padding)) :
    CrossConfigAgree machine
      (machine.runConfig (machine.initialConfig input) steps)
      (machine.runConfig
        (machine.initialConfig (zeroExtend input padding)) steps) := by
  apply crossConfigAgree_run machine
  · exact initialConfig_zeroExtend_agree machine input padding
  · simpa [TM.initialConfig] using hshortRoom
  · simpa [TM.initialConfig] using hextendedRoom

/-! ## The physical right clamp is unreachable at the canonical clock -/

/-- The declared runtime is strictly below the allocated tape length. -/
theorem runTime_lt_tapeLength (machine : TM.{u}) (inputLength : Nat) :
    machine.runTime inputLength < machine.tapeLength inputLength := by
  unfold TM.tapeLength
  omega

/-- Before every transition of a canonical run, the head has strict room for
a right move.  Thus the right-clamp branch of `moveHead` is unreachable during
the complete declared run. -/
theorem canonicalRun_preStep_has_right_room (machine : TM.{u})
    {inputLength : Nat} (input : Boolcube.Point inputLength) (elapsed : Nat)
    (helapsed : elapsed < machine.runTime inputLength) :
    (machine.runConfig (machine.initialConfig input) elapsed).head.val + 1 <
      machine.tapeLength inputLength := by
  have hhead := TM.runConfig_head_val_le
    (M := machine) (machine.initialConfig input) elapsed
  have hinitial : (machine.initialConfig input).head.val = 0 := rfl
  rw [hinitial] at hhead
  unfold TM.tapeLength
  omega

/-- Exact non-clamping equation for a hypothetical right move before any
canonical transition. -/
theorem canonicalRun_moveHead_right_eq_succ (machine : TM.{u})
    {inputLength : Nat} (input : Boolcube.Point inputLength) (elapsed : Nat)
    (helapsed : elapsed < machine.runTime inputLength) :
    let config := machine.runConfig (machine.initialConfig input) elapsed
    config.moveHead Move.right =
      ⟨config.head.val + 1,
        canonicalRun_preStep_has_right_room machine input elapsed helapsed⟩ := by
  dsimp only
  exact TM.Configuration.moveHead_right_lt _
    (canonicalRun_preStep_has_right_room machine input elapsed helapsed)

/-! ## Operational polynomial clocks and zero extensions -/

/-- For a fixed operational program, every prefix no longer than the shorter
input's canonical clock is identical on an input and an all-zero extension.
The polynomial clock is monotone in the ambient input length, so both actual
finite tapes have the required head room. -/
theorem operational_zeroExtend_same_trace_prefix (program : OperationalTM)
    {inputLength : Nat} (input : Boolcube.Point inputLength)
    (padding steps : Nat)
    (hsteps : steps <= program.executionTM.runTime inputLength) :
    CrossConfigAgree program.executionTM
      (program.executionTM.runConfig
        (program.executionTM.initialConfig input) steps)
      (program.executionTM.runConfig
        (program.executionTM.initialConfig (zeroExtend input padding)) steps) := by
  apply zeroExtend_same_trace_prefix program.executionTM input padding steps
  · unfold TM.tapeLength
    omega
  · have hbase : inputLength <= inputLength + padding := by omega
    have hpow : inputLength ^ program.exponent <=
        (inputLength + padding) ^ program.exponent :=
      Nat.pow_le_pow_left hbase program.exponent
    simp only [TM.tapeLength, OperationalTM.executionTM] at hsteps ⊢
    omega

/-- In particular, the complete short-input run is an identical execution
prefix of every all-zero extension.  Any difference at the longer input's
final observation must arise strictly after the short clock has expired. -/
theorem operational_zeroExtend_same_short_clock (program : OperationalTM)
    {inputLength : Nat} (input : Boolcube.Point inputLength) (padding : Nat) :
    CrossConfigAgree program.executionTM
      (program.executionTM.runConfig
        (program.executionTM.initialConfig input)
        (program.executionTM.runTime inputLength))
      (program.executionTM.runConfig
        (program.executionTM.initialConfig (zeroExtend input padding))
        (program.executionTM.runTime inputLength)) := by
  exact operational_zeroExtend_same_trace_prefix program input padding
    (program.executionTM.runTime inputLength) (le_refl _)

/-! ## Generic expiration of an early accepting pulse -/

private theorem runConfig_succ_back (machine : TM.{u})
    {inputLength : Nat} (config : machine.Configuration inputLength)
    (steps : Nat) :
    machine.runConfig config (steps + 1) =
      machine.stepConfig (machine.runConfig config steps) := by
  unfold TM.runConfig
  exact Function.iterate_succ_apply'
    (TM.stepConfig (M := machine)) steps config

private theorem runConfig_add (machine : TM.{u})
    {inputLength : Nat} (config : machine.Configuration inputLength)
    (first second : Nat) :
    machine.runConfig config (first + second) =
      machine.runConfig (machine.runConfig config first) second := by
  unfold TM.runConfig
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem runConfig_state_fixed (machine : TM.{u}) {dead : machine.state}
    (hdead : forall symbol, (machine.step dead symbol).1 = dead)
    {inputLength : Nat} (config : machine.Configuration inputLength)
    (steps : Nat) (hstate : config.state = dead) :
    (machine.runConfig config steps).state = dead := by
  induction steps generalizing config with
  | zero => simpa [TM.runConfig] using hstate
  | succ steps ih =>
      rw [runConfig_succ_front machine config]
      apply ih
      simpa [TM.stepConfig, hstate] using hdead (config.tape config.head)

/-- If a program reaches a one-tick pulse strictly before its canonical
clock, and that pulse immediately enters a state whose state component is
absorbing, final acceptance observes the dead state's output.  Tape writes
and head movement in the two terminal controls are unrestricted. -/
theorem accepts_eq_output_of_early_pulse (program : OperationalTM)
    {pulse dead : program.state}
    (hpulse : forall symbol, (program.step pulse symbol).1 = dead)
    (hdead : forall symbol, (program.step dead symbol).1 = dead)
    {inputLength finish : Nat} (input : Boolcube.Point inputLength)
    (hreaches :
      (program.executionTM.runConfig
        (program.executionTM.initialConfig input) finish).state = pulse)
    (hearly : finish < program.executionTM.runTime inputLength) :
    program.accepts inputLength input = program.output dead := by
  let initial := program.executionTM.initialConfig input
  have hreaches' :
      (program.executionTM.runConfig initial finish).state = pulse := by
    simpa [initial] using hreaches
  have hnext :
      (program.executionTM.runConfig initial (finish + 1)).state = dead := by
    rw [runConfig_succ_back]
    unfold TM.stepConfig
    dsimp only
    rw [hreaches']
    exact hpulse _
  have hle : finish + 1 <= program.executionTM.runTime inputLength := by omega
  unfold OperationalTM.accepts
  change program.output
    ((program.executionTM.runConfig initial
      (program.executionTM.runTime inputLength)).state) = program.output dead
  rw [show program.executionTM.runTime inputLength =
      (finish + 1) +
        (program.executionTM.runTime inputLength - (finish + 1)) by omega]
  rw [runConfig_add]
  rw [runConfig_state_fixed program.executionTM hdead _ _ hnext]

/-! ## The external clock remains a real length channel -/

/-- A zero bitstring of any requested length. -/
def zeroInput (inputLength : Nat) : Boolcube.Point inputLength :=
  fun _ => false

@[simp] theorem zeroExtend_zeroInput (inputLength padding : Nat) :
    zeroExtend (zeroInput inputLength) padding =
      zeroInput (inputLength + padding) := by
  funext index
  simp [zeroExtend, zeroInput]

/-- A fixed two-state program that ignores the tape and toggles its state once
per transition.  Its output depends only on the external sampling time. -/
def timingOnlyToggle : OperationalTM where
  state := Bool
  start := false
  step := fun state symbol => (!state, symbol, .stay)
  exponent := 1
  output := id

@[simp] theorem timingOnlyToggle_accepts_one :
    timingOnlyToggle.accepts 1 (zeroInput 1) = false := by
  rfl

@[simp] theorem timingOnlyToggle_accepts_two :
    timingOnlyToggle.accepts 2 (zeroInput 2) = true := by
  rfl

/-- The two inputs differ only by an explicit zero bit, while their outputs
differ because the linear canonical clocks contain two versus three steps. -/
theorem timingOnlyToggle_distinguishes_zero_extension :
    timingOnlyToggle.accepts 1 (zeroInput 1) ≠
      timingOnlyToggle.accepts 2 (zeroExtend (zeroInput 1) 1) := by
  simp

end OperationalClockBoundary
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary.canonicalRun_preStep_has_right_room
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary.canonicalRun_moveHead_right_eq_succ
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary.operational_zeroExtend_same_trace_prefix
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary.operational_zeroExtend_same_short_clock
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary.accepts_eq_output_of_early_pulse
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalClockBoundary.timingOnlyToggle_distinguishes_zero_extension
