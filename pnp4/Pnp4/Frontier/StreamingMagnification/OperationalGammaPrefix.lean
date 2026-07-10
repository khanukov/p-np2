import Pnp4.Frontier.StreamingMagnification.OperationalDynamicScan
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

/-!
# A fixed-control destructive Elias-gamma payload walker

`OperationalDynamicScan` can find the first `1`, but its two-state control
does not remember how many zeroes preceded that terminator.  This module
stores that unbounded count on the same binary tape.  For an input beginning

```text
0^k 1 b₀ ... bₖ₋₁ rest
```

the machine destructively rewrites the prefix to `1^k`, turns the terminator
into a moving marker, and matches one prefix cell with one tape cell per round
trip.  After exactly `k` rounds the marker is at position `2*k` and the head is
at geometric position `2*k + 1`.  This is the start of `rest` only when the
ambient input really contains the full `k`-cell payload span.  The transition
table is fixed and has no input-length or host-level loop parameter.

The tape alphabet is only `Bool`, and blank cells are `false`.  Therefore a
missing zero suffix of a payload is observationally identical to present zero
payload bits.  The executable below is consequently an honest *destructive
payload walker*, not a full parser or numeric decoder.  The module makes this
limitation explicit by proving its behaviour on a truncated unary terminator.

The present machine also uses the physical left clamp at cell `0` to detect
the last counter cell.  It therefore handles a gamma field beginning at tape
origin, not the request codec's gamma field after its eight-bit tag.  A tagged
wrapper needs either a sentinel immediately to the left of the gamma field or
a block encoding with a reserved marker pattern; neither bridge is claimed
here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalGammaPrefix

open Pnp3.ComplexityInterfaces
open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity

/-- Fixed finite control for the destructive gamma-prefix walk. -/
inductive GammaState where
  | scanStart
  | scanZeros
  | markLeft
  | seekDelimiter
  | processCounter
  | checkMore
  | seekMarkerMore
  | makeMarkerMore
  | returnCounter
  | seekMarkerLast
  | makeMarkerLast
  | done
  deriving DecidableEq, Fintype

/-- The fixed transition table.  Its canonical exponent is `3`; the useful
trace is quadratic, leaving a simple polynomial amount of absorbing slack. -/
def gammaPrefixWalker : OperationalTM where
  state := GammaState
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := .scanStart
  step := fun state scanned =>
    match state with
    | .scanStart =>
        if scanned then (.done, true, Move.right)
        else (.scanZeros, false, Move.right)
    | .scanZeros =>
        if scanned then (.markLeft, false, Move.left)
        else (.scanZeros, false, Move.right)
    | .markLeft =>
        if scanned then (.seekDelimiter, true, Move.right)
        else (.markLeft, true, Move.left)
    | .seekDelimiter =>
        if scanned then (.seekDelimiter, true, Move.right)
        else (.processCounter, true, Move.left)
    | .processCounter => (.checkMore, false, Move.left)
    | .checkMore =>
        if scanned then (.seekMarkerMore, true, Move.right)
        else (.seekMarkerLast, false, Move.right)
    | .seekMarkerMore =>
        if scanned then (.makeMarkerMore, false, Move.right)
        else (.seekMarkerMore, false, Move.right)
    | .makeMarkerMore => (.returnCounter, true, Move.left)
    | .returnCounter =>
        if scanned then (.processCounter, true, Move.stay)
        else (.returnCounter, false, Move.left)
    | .seekMarkerLast =>
        if scanned then (.makeMarkerLast, false, Move.right)
        else (.seekMarkerLast, false, Move.right)
    | .makeMarkerLast => (.done, true, Move.right)
    | .done => (.done, scanned, Move.stay)
  exponent := 3
  output := fun state => state == .done

@[simp] theorem gammaPrefixWalker_state_card :
    Fintype.card gammaPrefixWalker.state = 12 := by
  decide

@[simp] theorem gammaPrefixWalker_clock (inputLength : Nat) :
    gammaPrefixWalker.executionTM.runTime inputLength =
      inputLength ^ 3 + 3 := by
  rfl

@[simp] theorem gammaPrefixWalker_tapeLength (inputLength : Nat) :
    gammaPrefixWalker.executionTM.tapeLength inputLength =
      inputLength + (inputLength ^ 3 + 3) + 1 := by
  rfl

/-! ## A natural-coordinate execution facade -/

/-- A natural-coordinate tape write. -/
def writeNat (tape : Nat → Bool) (position : Nat) (bit : Bool) : Nat → Bool :=
  fun query => if query = position then bit else tape query

/-- Natural-coordinate movement with the same left-boundary convention as the
repository tape.  Right-clamping is ruled out separately by trace bounds. -/
def moveNat (position : Nat) : Move → Nat
  | .left => position - 1
  | .stay => position
  | .right => position + 1

/-- Proof-friendly natural-coordinate configurations. -/
structure NatConfig where
  state : GammaState
  head : Nat
  tape : Nat → Bool

/-- One transition of the exact same fixed control on natural coordinates. -/
def natStep (config : NatConfig) : NatConfig :=
  let result := gammaPrefixWalker.step config.state (config.tape config.head)
  { state := result.1
    head := moveNat config.head result.2.2
    tape := writeNat config.tape config.head result.2.1 }

/-- Iteration of the natural-coordinate fixed control. -/
def natRun (config : NatConfig) (steps : Nat) : NatConfig :=
  Nat.iterate natStep steps config

@[simp] theorem natRun_zero (config : NatConfig) :
    natRun config 0 = config := rfl

theorem natRun_succ (config : NatConfig) (steps : Nat) :
    natRun config (steps + 1) = natStep (natRun config steps) := by
  unfold natRun
  exact Function.iterate_succ_apply' natStep steps config

@[simp] theorem natRun_one (config : NatConfig) :
    natRun config 1 = natStep config := by
  simpa using natRun_succ config 0

theorem natRun_add (config : NatConfig) (first second : Nat) :
    natRun config (first + second) =
      natRun (natRun config first) second := by
  unfold natRun
  rw [Nat.add_comm, Function.iterate_add_apply]

@[simp] theorem writeNat_same (tape : Nat → Bool) (position : Nat) :
    writeNat tape position (tape position) = tape := by
  funext query
  by_cases hquery : query = position
  · subst query
    simp [writeNat]
  · simp [writeNat, hquery]

theorem writeNat_eq_self_of_eq {tape : Nat → Bool} {position : Nat}
    {bit : Bool} (hbit : tape position = bit) :
    writeNat tape position bit = tape := by
  rw [← hbit]
  exact writeNat_same tape position

@[simp] theorem natStep_scanStart_zero (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = false) :
    natStep ⟨.scanStart, head, tape⟩ =
      ⟨.scanZeros, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_scanStart_one (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = true) :
    natStep ⟨.scanStart, head, tape⟩ =
      ⟨.done, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_scanZeros_zero (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = false) :
    natStep ⟨.scanZeros, head, tape⟩ =
      ⟨.scanZeros, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_scanZeros_one (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = true) :
    natStep ⟨.scanZeros, head, tape⟩ =
      ⟨.markLeft, head - 1, writeNat tape head false⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat]

@[simp] theorem natStep_markLeft_zero (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = false) :
    natStep ⟨.markLeft, head, tape⟩ =
      ⟨.markLeft, head - 1, writeNat tape head true⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat]

@[simp] theorem natStep_markLeft_one (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = true) :
    natStep ⟨.markLeft, head, tape⟩ =
      ⟨.seekDelimiter, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_seekDelimiter_one (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = true) :
    natStep ⟨.seekDelimiter, head, tape⟩ =
      ⟨.seekDelimiter, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_seekDelimiter_zero (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = false) :
    natStep ⟨.seekDelimiter, head, tape⟩ =
      ⟨.processCounter, head - 1, writeNat tape head true⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat]

@[simp] theorem natStep_processCounter (head : Nat) (tape : Nat → Bool) :
    natStep ⟨.processCounter, head, tape⟩ =
      ⟨.checkMore, head - 1, writeNat tape head false⟩ := by
  cases hbit : tape head <;>
    simp [natStep, gammaPrefixWalker, hbit, moveNat]

@[simp] theorem natStep_checkMore_one (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = true) :
    natStep ⟨.checkMore, head, tape⟩ =
      ⟨.seekMarkerMore, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_checkMore_zero (head : Nat) (tape : Nat → Bool)
    (hscanned : tape head = false) :
    natStep ⟨.checkMore, head, tape⟩ =
      ⟨.seekMarkerLast, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_seekMarkerMore_zero (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = false) :
    natStep ⟨.seekMarkerMore, head, tape⟩ =
      ⟨.seekMarkerMore, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_seekMarkerMore_one (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = true) :
    natStep ⟨.seekMarkerMore, head, tape⟩ =
      ⟨.makeMarkerMore, head + 1, writeNat tape head false⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat]

@[simp] theorem natStep_makeMarkerMore (head : Nat) (tape : Nat → Bool) :
    natStep ⟨.makeMarkerMore, head, tape⟩ =
      ⟨.returnCounter, head - 1, writeNat tape head true⟩ := by
  cases hbit : tape head <;>
    simp [natStep, gammaPrefixWalker, hbit, moveNat]

@[simp] theorem natStep_returnCounter_zero (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = false) :
    natStep ⟨.returnCounter, head, tape⟩ =
      ⟨.returnCounter, head - 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_returnCounter_one (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = true) :
    natStep ⟨.returnCounter, head, tape⟩ =
      ⟨.processCounter, head, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_seekMarkerLast_zero (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = false) :
    natStep ⟨.seekMarkerLast, head, tape⟩ =
      ⟨.seekMarkerLast, head + 1, tape⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat,
    writeNat_eq_self_of_eq hscanned]

@[simp] theorem natStep_seekMarkerLast_one (head : Nat)
    (tape : Nat → Bool) (hscanned : tape head = true) :
    natStep ⟨.seekMarkerLast, head, tape⟩ =
      ⟨.makeMarkerLast, head + 1, writeNat tape head false⟩ := by
  simp [natStep, gammaPrefixWalker, hscanned, moveNat]

@[simp] theorem natStep_makeMarkerLast (head : Nat) (tape : Nat → Bool) :
    natStep ⟨.makeMarkerLast, head, tape⟩ =
      ⟨.done, head + 1, writeNat tape head true⟩ := by
  cases hbit : tape head <;>
    simp [natStep, gammaPrefixWalker, hbit, moveNat]

@[simp] theorem natStep_done (head : Nat) (tape : Nat → Bool) :
    natStep ⟨.done, head, tape⟩ = ⟨.done, head, tape⟩ := by
  simp [natStep, gammaPrefixWalker, moveNat, writeNat_same]

/-- Embed a natural-coordinate configuration into a sufficiently long
repository tape. -/
def NatConfig.embed {inputLength : Nat} (config : NatConfig)
    (hhead : config.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength) :
    TM.Configuration
      (M := gammaPrefixWalker.executionTM) inputLength where
  state := config.state
  head := ⟨config.head, hhead⟩
  tape := fun position => config.tape position.val

@[simp] theorem NatConfig.embed_state {inputLength : Nat}
    (config : NatConfig)
    (hhead : config.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength) :
    (config.embed hhead).state = config.state := rfl

@[simp] theorem NatConfig.embed_head_val {inputLength : Nat}
    (config : NatConfig)
    (hhead : config.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength) :
    (config.embed hhead).head.val = config.head := rfl

@[simp] theorem NatConfig.embed_tape {inputLength : Nat}
    (config : NatConfig)
    (hhead : config.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength)
    (position : Fin
      (gammaPrefixWalker.executionTM.tapeLength inputLength)) :
    (config.embed hhead).tape position = config.tape position.val := rfl

theorem NatConfig.embed_eq_of_eq {inputLength : Nat}
    {left right : NatConfig}
    (hleft : left.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength)
    (hright : right.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength)
    (hconfig : left = right) :
    left.embed hleft = right.embed hright := by
  subst right
  rfl

/-- One natural-coordinate transition is exactly one repository transition as
long as the (possibly requested) right move cannot meet the far tape edge. -/
theorem NatConfig.stepConfig_embed {inputLength : Nat}
    (config : NatConfig)
    (hhead : config.head <
      gammaPrefixWalker.executionTM.tapeLength inputLength)
    (hnext : (natStep config).head <
      gammaPrefixWalker.executionTM.tapeLength inputLength)
    (hright : config.head + 1 <
      gammaPrefixWalker.executionTM.tapeLength inputLength) :
    gammaPrefixWalker.executionTM.stepConfig
        (config.embed hhead) =
      (natStep config).embed hnext := by
  change moveNat config.head
      (gammaPrefixWalker.step config.state
        (config.tape config.head)).2.2 <
    gammaPrefixWalker.executionTM.tapeLength inputLength at hnext
  unfold TM.stepConfig NatConfig.embed natStep
  dsimp only
  rw [TM.Configuration.mk.injEq]
  refine ⟨by rfl, ?_, ?_⟩
  · apply Fin.ext
    simp only [OperationalTM.executionTM]
    cases hmove : (gammaPrefixWalker.step config.state
      (config.tape config.head)).2.2 with
    | left =>
        simp only [moveNat]
        by_cases hzero : config.head = 0
        · simp [TM.Configuration.moveHead, hzero]
        · simp [TM.Configuration.moveHead, hzero]
    | stay => rfl
    | right =>
        simp only [moveNat]
        change ((TM.Configuration.moveHead
          (c := config.embed hhead) Move.right).val = config.head + 1)
        rw [TM.Configuration.moveHead_right_lt
          (c := config.embed hhead) hright]
        rfl
  · funext position
    simp only [OperationalTM.executionTM]
    unfold TM.Configuration.write writeNat
    by_cases heq : position.val = config.head
    · have hfin : position = ⟨config.head, hhead⟩ := Fin.ext heq
      simp [hfin]
    · have hfin : position ≠ ⟨config.head, hhead⟩ := by
        intro h
        exact heq (congrArg Fin.val h)
      simp [heq, hfin]

/-- Exact multi-step simulation.  The hypothesis only rules out the remote
right clamp; all useful traces below stay in `[0, 2*k+1]`. -/
theorem NatConfig.runConfig_embed {inputLength : Nat}
    (config : NatConfig) (steps : Nat)
    (hbound : ∀ elapsed, elapsed ≤ steps →
      (natRun config elapsed).head + 1 <
        gammaPrefixWalker.executionTM.tapeLength inputLength) :
    gammaPrefixWalker.executionTM.runConfig
        (config.embed (by
          have := hbound 0 (Nat.zero_le steps)
          simpa using Nat.lt_of_succ_lt this)) steps =
      (natRun config steps).embed (by
        have := hbound steps (Nat.le_refl steps)
        exact Nat.lt_of_succ_lt this) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hprefix : ∀ elapsed, elapsed ≤ steps →
          (natRun config elapsed).head + 1 <
            gammaPrefixWalker.executionTM.tapeLength inputLength := by
        intro elapsed helapsed
        exact hbound elapsed (Nat.le_succ_of_le helapsed)
      rw [TM.runConfig_succ]
      rw [ih hprefix]
      have hrightStep := hbound steps (by omega)
      have hnextStep : (natStep (natRun config steps)).head <
          gammaPrefixWalker.executionTM.tapeLength inputLength := by
        have h := hbound (steps + 1) (Nat.le_refl (steps + 1))
        rw [natRun_succ] at h
        omega
      rw [NatConfig.stepConfig_embed
        (hnext := hnextStep) (hright := hrightStep)]
      simp only [natRun_succ]

/-- Endpoint-sharp simulation: the final head only has to be in bounds;
right-move slack is required exactly at the strict intermediate times. -/
theorem NatConfig.runConfig_embed_bounded {inputLength : Nat}
    (config : NatConfig) (steps : Nat)
    (hheads : ∀ elapsed, elapsed ≤ steps →
      (natRun config elapsed).head <
        gammaPrefixWalker.executionTM.tapeLength inputLength)
    (hrights : ∀ elapsed, elapsed < steps →
      (natRun config elapsed).head + 1 <
        gammaPrefixWalker.executionTM.tapeLength inputLength) :
    gammaPrefixWalker.executionTM.runConfig
        (config.embed (hheads 0 (Nat.zero_le steps))) steps =
      (natRun config steps).embed (hheads steps (Nat.le_refl steps)) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hheadsPrefix : ∀ elapsed, elapsed ≤ steps →
          (natRun config elapsed).head <
            gammaPrefixWalker.executionTM.tapeLength inputLength := by
        intro elapsed helapsed
        exact hheads elapsed (Nat.le_succ_of_le helapsed)
      have hrightsPrefix : ∀ elapsed, elapsed < steps →
          (natRun config elapsed).head + 1 <
            gammaPrefixWalker.executionTM.tapeLength inputLength := by
        intro elapsed helapsed
        exact hrights elapsed (Nat.lt.step helapsed)
      rw [TM.runConfig_succ, ih hheadsPrefix hrightsPrefix]
      have hnext : (natStep (natRun config steps)).head <
          gammaPrefixWalker.executionTM.tapeLength inputLength := by
        have h := hheads (steps + 1) (Nat.le_refl (steps + 1))
        rw [natRun_succ] at h
        exact h
      have hright := hrights steps (Nat.lt_succ_self steps)
      rw [NatConfig.stepConfig_embed
        (hnext := hnext) (hright := hright)]
      simp only [natRun_succ]

/-! ## Exact natural-coordinate scan invariants -/

theorem natRun_scanZeros {start steps : Nat} (tape : Nat → Bool)
    (hzero : ∀ offset, offset < steps → tape (start + offset) = false) :
    natRun ⟨.scanZeros, start, tape⟩ steps =
      ⟨.scanZeros, start + steps, tape⟩ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : ∀ offset, offset < steps →
          tape (start + offset) = false := by
        intro offset hoffset
        exact hzero offset (by omega)
      have hcell : tape (start + steps) = false :=
        hzero steps (by omega)
      rw [natRun_succ, ih hprefix]
      rw [natStep_scanZeros_zero _ _ hcell]
      congr 1

theorem natRun_seekDelimiter {start steps : Nat} (tape : Nat → Bool)
    (hone : ∀ offset, offset < steps → tape (start + offset) = true) :
    natRun ⟨.seekDelimiter, start, tape⟩ steps =
      ⟨.seekDelimiter, start + steps, tape⟩ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : ∀ offset, offset < steps →
          tape (start + offset) = true := by
        intro offset hoffset
        exact hone offset (by omega)
      have hcell : tape (start + steps) = true :=
        hone steps (by omega)
      rw [natRun_succ, ih hprefix]
      rw [natStep_seekDelimiter_one _ _ hcell]
      congr 1

theorem natRun_seekMarkerMore {start steps : Nat} (tape : Nat → Bool)
    (hzero : ∀ offset, offset < steps → tape (start + offset) = false) :
    natRun ⟨.seekMarkerMore, start, tape⟩ steps =
      ⟨.seekMarkerMore, start + steps, tape⟩ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : ∀ offset, offset < steps →
          tape (start + offset) = false := by
        intro offset hoffset
        exact hzero offset (by omega)
      have hcell : tape (start + steps) = false :=
        hzero steps (by omega)
      rw [natRun_succ, ih hprefix]
      rw [natStep_seekMarkerMore_zero _ _ hcell]
      congr 1

theorem natRun_seekMarkerLast {start steps : Nat} (tape : Nat → Bool)
    (hzero : ∀ offset, offset < steps → tape (start + offset) = false) :
    natRun ⟨.seekMarkerLast, start, tape⟩ steps =
      ⟨.seekMarkerLast, start + steps, tape⟩ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : ∀ offset, offset < steps →
          tape (start + offset) = false := by
        intro offset hoffset
        exact hzero offset (by omega)
      have hcell : tape (start + steps) = false :=
        hzero steps (by omega)
      rw [natRun_succ, ih hprefix]
      rw [natStep_seekMarkerLast_zero _ _ hcell]
      congr 1

theorem natRun_returnCounter {start steps : Nat} (tape : Nat → Bool)
    (hsteps : steps ≤ start)
    (hzero : ∀ offset, offset < steps → tape (start - offset) = false) :
    natRun ⟨.returnCounter, start, tape⟩ steps =
      ⟨.returnCounter, start - steps, tape⟩ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : ∀ offset, offset < steps →
          tape (start - offset) = false := by
        intro offset hoffset
        exact hzero offset (by omega)
      have hstepBound : steps ≤ start := by omega
      have hcell : tape (start - steps) = false :=
        hzero steps (by omega)
      rw [natRun_succ, ih hstepBound hprefix]
      rw [natStep_returnCounter_zero _ _ hcell]
      congr 1

@[simp] theorem natRun_done (head steps : Nat) (tape : Nat → Bool) :
    natRun ⟨.done, head, tape⟩ steps = ⟨.done, head, tape⟩ := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [natRun_succ, ih]
      exact natStep_done head tape

/-! ## The moving-marker invariant -/

/-- Tape at a cycle boundary after `processed` payload cells.  The remaining
counter is `1^(k-processed)`, the whole working gap is zero, and the unique
right marker is at `k+processed`. -/
def progressTape (base : Nat → Bool) (k processed : Nat) : Nat → Bool :=
  fun position =>
    if position < k - processed then true
    else if position < k + processed then false
    else if position = k + processed then true
    else base position

@[simp] theorem progressTape_counter {base : Nat → Bool} {k processed position : Nat}
    (hposition : position < k - processed) :
    progressTape base k processed position = true := by
  simp [progressTape, hposition]

@[simp] theorem progressTape_gap {base : Nat → Bool} {k processed position : Nat}
    (hlower : k - processed ≤ position)
    (hupper : position < k + processed) :
    progressTape base k processed position = false := by
  simp [progressTape, Nat.not_lt.mpr hlower, hupper]

@[simp] theorem progressTape_marker (base : Nat → Bool) (k processed : Nat) :
    progressTape base k processed (k + processed) = true := by
  simp [progressTape]

@[simp] theorem progressTape_tail {base : Nat → Bool} {k processed position : Nat}
    (htail : k + processed < position) :
    progressTape base k processed position = base position := by
  have hcounter : ¬ position < k - processed := by omega
  have hgap : ¬ position < k + processed := by omega
  have hmarker : position ≠ k + processed := by omega
  simp [progressTape, hcounter, hgap, hmarker]

/-- Exact cycle-boundary natural configuration. -/
def progressConfig (base : Nat → Bool) (k processed : Nat) : NatConfig :=
  { state := .processCounter
    head := k - processed - 1
    tape := progressTape base k processed }

/-- Exact successful endpoint: marker at `2*k`, head one cell later. -/
def finishedConfig (base : Nat → Bool) (k : Nat) : NatConfig :=
  { state := .done
    head := 2 * k + 1
    tape := progressTape base k k }

@[simp] theorem finishedConfig_state (base : Nat → Bool) (k : Nat) :
    (finishedConfig base k).state = .done := rfl

@[simp] theorem finishedConfig_head (base : Nat → Bool) (k : Nat) :
    (finishedConfig base k).head = 2 * k + 1 := rfl

@[simp] theorem finishedConfig_marker (base : Nat → Bool) (k : Nat) :
    (finishedConfig base k).tape (2 * k) = true := by
  simp [finishedConfig, progressTape, Nat.two_mul]

@[simp] theorem finishedConfig_erased_before_marker
    (base : Nat → Bool) (k position : Nat) (hposition : position < 2 * k) :
    (finishedConfig base k).tape position = false := by
  change progressTape base k k position = false
  have hgap : position < k + k := by simpa [Nat.two_mul] using hposition
  simp [progressTape, hgap]

@[simp] theorem finishedConfig_tail (base : Nat → Bool) (k position : Nat)
    (htail : 2 * k < position) :
    (finishedConfig base k).tape position = base position := by
  change progressTape base k k position = base position
  apply progressTape_tail
  omega

/-- One round moves the marker one cell right and shortens the unary counter
by one.  This is the exact destructive tape update behind the cycle proof. -/
theorem progressTape_round_update (base : Nat → Bool) (k processed : Nat)
    (hprocessed : processed < k) :
    writeNat
        (writeNat
          (writeNat (progressTape base k processed)
            (k - processed - 1) false)
          (k + processed) false)
        (k + processed + 1) true =
      progressTape base k (processed + 1) := by
  funext position
  unfold writeNat progressTape
  split_ifs <;> simp_all <;> omega

/-- Exact non-final round.  The runtime `4*processed+8` is derived from the
two crossings of the growing zero gap; it is not stored in finite control. -/
theorem natRun_progress_round (base : Nat → Bool) (k processed : Nat)
    (hmore : processed + 1 < k) :
    natRun (progressConfig base k processed) (4 * processed + 8) =
      progressConfig base k (processed + 1) := by
  let left := k - processed - 1
  let marker := k + processed
  let t0 := progressTape base k processed
  let t1 := writeNat t0 left false
  let t2 := writeNat t1 marker false
  let t3 := writeNat t2 (marker + 1) true
  have hprocessed : processed < k := by omega
  have hleft : left = k - processed - 1 := rfl
  have hleftPos : 0 < left := by
    dsimp only [left]
    omega
  have hmarker : marker = k + processed := rfl
  have ht0left : t0 left = true := by
    dsimp only [t0, left]
    apply progressTape_counter
    omega
  have ht1check : t1 (left - 1) = true := by
    unfold t1 writeNat
    have hne : left - 1 ≠ left := by omega
    rw [if_neg hne]
    dsimp only [t0, left]
    apply progressTape_counter
    omega
  have ht1gap : ∀ offset, offset < 2 * processed + 1 →
      t1 (left + offset) = false := by
    intro offset hoffset
    unfold t1 writeNat
    by_cases hposition : left + offset = left
    · simp [hposition]
    · rw [if_neg hposition]
      dsimp only [t0, left]
      apply progressTape_gap
      · omega
      · omega
  have ht1marker : t1 marker = true := by
    unfold t1 writeNat
    have hne : marker ≠ left := by
      dsimp only [marker, left]
      omega
    rw [if_neg hne]
    dsimp only [t0, marker]
    exact progressTape_marker base k processed
  have ht3next : t3 = progressTape base k (processed + 1) := by
    dsimp only [t3, t2, t1, t0, marker, left]
    exact progressTape_round_update base k processed hprocessed
  have ht3return : ∀ offset, offset < 2 * processed + 2 →
      t3 (marker - offset) = false := by
    intro offset hoffset
    rw [ht3next]
    apply progressTape_gap
    · dsimp only [marker]
      omega
    · dsimp only [marker]
      omega
  have ht3counter : t3 (left - 1) = true := by
    rw [ht3next]
    apply progressTape_counter
    dsimp only [left]
    omega
  change natRun ⟨.processCounter, left, t0⟩ (4 * processed + 8) =
    progressConfig base k (processed + 1)
  rw [show 4 * processed + 8 = 1 + (4 * processed + 7) by omega,
    natRun_add, natRun_one, natStep_processCounter]
  change natRun ⟨.checkMore, left - 1, t1⟩ (4 * processed + 7) = _
  rw [show 4 * processed + 7 = 1 + (4 * processed + 6) by omega,
    natRun_add, natRun_one,
    natStep_checkMore_one _ _ ht1check]
  rw [show left - 1 + 1 = left by omega]
  rw [show 4 * processed + 6 =
      (2 * processed + 1) + (2 * processed + 5) by omega,
    natRun_add, natRun_seekMarkerMore t1 ht1gap]
  rw [show left + (2 * processed + 1) = marker by
    dsimp only [left, marker]
    omega]
  rw [show 2 * processed + 5 = 1 + (2 * processed + 4) by omega,
    natRun_add, natRun_one,
    natStep_seekMarkerMore_one _ _ ht1marker]
  change natRun ⟨.makeMarkerMore, marker + 1, t2⟩
    (2 * processed + 4) = _
  rw [show 2 * processed + 4 = 1 + (2 * processed + 3) by omega,
    natRun_add, natRun_one, natStep_makeMarkerMore]
  rw [show marker + 1 - 1 = marker by omega]
  change natRun ⟨.returnCounter, marker, t3⟩
    (2 * processed + 3) = _
  rw [show 2 * processed + 3 =
      (2 * processed + 2) + 1 by omega,
    natRun_add,
    natRun_returnCounter t3 (by omega) ht3return]
  rw [show marker - (2 * processed + 2) = left - 1 by
    dsimp only [marker, left]
    omega]
  rw [natRun_one, natStep_returnCounter_one _ _ ht3counter]
  unfold progressConfig
  rw [ht3next]
  congr 1

/-- Exact final round.  It leaves the marker at `2*k` and performs the
requested fixed-control advance to `2*k+1`, the next-field position. -/
theorem natRun_progress_last (base : Nat → Bool) (k : Nat) (hk : 0 < k) :
    natRun (progressConfig base k (k - 1)) (2 * k + 2) =
      finishedConfig base k := by
  let processed := k - 1
  let marker := k + processed
  let t0 := progressTape base k processed
  let t1 := writeNat t0 0 false
  let t2 := writeNat t1 marker false
  let t3 := writeNat t2 (marker + 1) true
  have hprocessed : processed < k := by
    dsimp only [processed]
    omega
  have hleft : k - processed - 1 = 0 := by
    dsimp only [processed]
    omega
  have ht1zero : t1 0 = false := by
    simp [t1, writeNat]
  have ht1gap : ∀ offset, offset < 2 * k - 2 →
      t1 (1 + offset) = false := by
    intro offset hoffset
    unfold t1 writeNat
    have hne : 1 + offset ≠ 0 := by omega
    rw [if_neg hne]
    dsimp only [t0, processed]
    apply progressTape_gap
    · omega
    · omega
  have ht1marker : t1 marker = true := by
    unfold t1 writeNat
    have hne : marker ≠ 0 := by
      dsimp only [marker, processed]
      omega
    rw [if_neg hne]
    dsimp only [t0, marker]
    exact progressTape_marker base k processed
  have ht3next : t3 = progressTape base k k := by
    have hround := progressTape_round_update base k processed hprocessed
    have hsucc : processed + 1 = k := by
      dsimp only [processed]
      omega
    rw [hleft] at hround
    rw [hsucc] at hround
    simpa only [t3, t2, t1, t0, marker] using hround
  have hmarkerStep :
      natRun ⟨.seekMarkerLast, marker, t1⟩ 1 =
        ⟨.makeMarkerLast, marker + 1, t2⟩ := by
    rw [natRun_one, natStep_seekMarkerLast_one _ _ ht1marker]
  unfold progressConfig
  rw [show k - (k - 1) - 1 = 0 by omega]
  change natRun ⟨.processCounter, 0, t0⟩ (2 * k + 2) =
    finishedConfig base k
  rw [show 2 * k + 2 = 1 + (2 * k + 1) by omega,
    natRun_add, natRun_one, natStep_processCounter]
  change natRun ⟨.checkMore, 0, t1⟩ (2 * k + 1) = _
  rw [show 2 * k + 1 = 1 + 2 * k by omega,
    natRun_add, natRun_one, natStep_checkMore_zero _ _ ht1zero]
  rw [show 2 * k = (2 * k - 2) + 2 by omega,
    natRun_add, natRun_seekMarkerLast t1 ht1gap]
  rw [show 1 + (2 * k - 2) = marker by
    dsimp only [marker, processed]
    omega]
  rw [show 2 = 1 + 1 by omega, natRun_add, hmarkerStep]
  rw [natRun_one, natStep_makeMarkerLast]
  change (⟨.done, marker + 1 + 1, t3⟩ : NatConfig) =
    finishedConfig base k
  unfold finishedConfig
  rw [ht3next]
  congr 1
  dsimp only [marker, processed]
  omega

/-- Sum of the first `processed` non-final round-trip costs. -/
def roundsTime (processed : Nat) : Nat :=
  2 * processed * processed + 6 * processed

@[simp] theorem roundsTime_zero : roundsTime 0 = 0 := by
  simp [roundsTime]

theorem roundsTime_succ (processed : Nat) :
    roundsTime (processed + 1) =
      roundsTime processed + (4 * processed + 8) := by
  unfold roundsTime
  ring

/-- Exact iteration of the non-final cycle invariant. -/
theorem natRun_progress_rounds (base : Nat → Bool) (k processed : Nat)
    (hprocessed : processed < k) :
    natRun (progressConfig base k 0) (roundsTime processed) =
      progressConfig base k processed := by
  induction processed with
  | zero => simp
  | succ processed ih =>
      have hprefix : processed < k := by omega
      rw [roundsTime_succ, natRun_add, ih hprefix]
      exact natRun_progress_round base k processed hprocessed

/-- All marker cycles, starting from the initialized `1^k 1` boundary. -/
theorem natRun_all_progress_cycles (base : Nat → Bool) (k : Nat) (hk : 0 < k) :
    natRun (progressConfig base k 0) (2 * k * k + 4 * k - 2) =
      finishedConfig base k := by
  have hpred : k - 1 < k := by omega
  have htime : 2 * k * k + 4 * k - 2 =
      roundsTime (k - 1) + (2 * k + 2) := by
    cases k with
    | zero => omega
    | succ predecessor =>
        simp [roundsTime]
        ring_nf
        omega
  rw [htime, natRun_add,
    natRun_progress_rounds base k (k - 1) hpred]
  exact natRun_progress_last base k hk

/-! ## Exact initialization from `0^k 1` -/

/-- Tape while the original zero prefix is being changed, right-to-left, into
the unary `1` counter. -/
def markingTape (base : Nat → Bool) (k marked : Nat) : Nat → Bool :=
  fun position =>
    if k - marked ≤ position ∧ position < k then true
    else if position = k then false
    else base position

def markingConfig (base : Nat → Bool) (k marked : Nat) : NatConfig :=
  { state := .markLeft
    head := k - marked - 1
    tape := markingTape base k marked }

theorem markingTape_zero (base : Nat → Bool) (k : Nat) :
    markingTape base k 0 = writeNat base k false := by
  funext position
  unfold markingTape writeNat
  split_ifs <;> simp_all <;> omega

theorem markingTape_update (base : Nat → Bool) (k marked : Nat)
    (hmarked : marked < k) :
    writeNat (markingTape base k marked) (k - marked - 1) true =
      markingTape base k (marked + 1) := by
  funext position
  have hboundary : k - (marked + 1) = k - marked - 1 := by omega
  by_cases heq : position = k - marked - 1
  · subst position
    unfold writeNat
    rw [if_pos rfl]
    unfold markingTape
    rw [hboundary]
    rw [if_pos (by constructor <;> omega)]
  · unfold writeNat
    rw [if_neg heq]
    unfold markingTape
    rw [hboundary]
    by_cases hlt : position < k
    · have hiff : (k - marked ≤ position) ↔
          (k - marked - 1 ≤ position) := by omega
      by_cases hold : k - marked ≤ position
      · have hnew : k - marked - 1 ≤ position := hiff.mp hold
        rw [if_pos ⟨hold, hlt⟩, if_pos ⟨hnew, hlt⟩]
      · have hnew : ¬ k - marked - 1 ≤ position := by
          intro h
          exact hold (hiff.mpr h)
        have hnotOldCond : ¬ (k - marked ≤ position ∧ position < k) :=
          fun h => hold h.1
        have hnotNewCond : ¬ (k - marked - 1 ≤ position ∧ position < k) :=
          fun h => hnew h.1
        rw [if_neg hnotOldCond, if_neg hnotNewCond]
    · have hnotOld : ¬ (k - marked ≤ position ∧ position < k) := by
        simp [hlt]
      have hnotNew : ¬ (k - marked - 1 ≤ position ∧ position < k) := by
        simp [hlt]
      rw [if_neg hnotOld, if_neg hnotNew]

theorem markingTape_unmarked_zero (base : Nat → Bool) (k marked : Nat)
    (hmarked : marked < k)
    (hzero : ∀ position, position < k → base position = false) :
    markingTape base k marked (k - marked - 1) = false := by
  have hposition : k - marked - 1 < k := by omega
  have hnotMarked : ¬ (k - marked ≤ k - marked - 1 ∧
      k - marked - 1 < k) := by omega
  have hnotDelimiter : k - marked - 1 ≠ k := by omega
  unfold markingTape
  rw [if_neg hnotMarked, if_neg hnotDelimiter]
  exact hzero _ hposition

theorem natStep_markingConfig (base : Nat → Bool) (k marked : Nat)
    (hmarked : marked < k)
    (hzero : ∀ position, position < k → base position = false) :
    natStep (markingConfig base k marked) =
      markingConfig base k (marked + 1) := by
  unfold markingConfig
  rw [natStep_markLeft_zero _ _
    (markingTape_unmarked_zero base k marked hmarked hzero)]
  rw [markingTape_update base k marked hmarked]
  congr 1

theorem natRun_markingPrefix (base : Nat → Bool) (k marked : Nat)
    (hmarked : marked ≤ k)
    (hzero : ∀ position, position < k → base position = false) :
    natRun (markingConfig base k 0) marked =
      markingConfig base k marked := by
  induction marked with
  | zero => rfl
  | succ marked ih =>
      have hprefix : marked ≤ k := by omega
      have hstrict : marked < k := by omega
      rw [natRun_succ, ih hprefix]
      exact natStep_markingConfig base k marked hstrict hzero

theorem markingTape_complete_counter (base : Nat → Bool) (k : Nat) :
    writeNat (markingTape base k k) k true =
      progressTape base k 0 := by
  funext position
  unfold markingTape writeNat progressTape
  split_ifs <;> simp_all <;> omega

@[simp] theorem markingTape_complete_one (base : Nat → Bool) (k position : Nat)
    (hposition : position < k) :
    markingTape base k k position = true := by
  simp [markingTape, hposition]

@[simp] theorem markingTape_delimiter (base : Nat → Bool) (k : Nat) :
    markingTape base k k k = false := by
  simp [markingTape]

/-- Natural-coordinate start configuration at physical tape origin `0`. -/
def sourceConfig (base : Nat → Bool) : NatConfig :=
  { state := .scanStart, head := 0, tape := base }

/-- Exact positive-prefix initialization cost. -/
theorem natRun_initialize_positive (base : Nat → Bool) (k : Nat)
    (hk : 0 < k)
    (hzero : ∀ position, position < k → base position = false)
    (hone : base k = true) :
    natRun (sourceConfig base) (3 * k + 2) =
      progressConfig base k 0 := by
  let markedTape := markingTape base k k
  have hfirstZero : base 0 = false := hzero 0 hk
  have hscanZeros : ∀ offset, offset < k - 1 →
      base (1 + offset) = false := by
    intro offset hoffset
    apply hzero
    omega
  have hmarkStart :
      (⟨.markLeft, k - 1, writeNat base k false⟩ : NatConfig) =
        markingConfig base k 0 := by
    unfold markingConfig
    rw [markingTape_zero]
    congr 1
  have hmarkedHead : k - k - 1 = 0 := by omega
  have hmarkedZero : markedTape 0 = true := by
    dsimp only [markedTape]
    apply markingTape_complete_one
    exact hk
  have hseekOnes : ∀ offset, offset < k - 1 →
      markedTape (1 + offset) = true := by
    intro offset hoffset
    dsimp only [markedTape]
    apply markingTape_complete_one
    omega
  have hdelimiter : markedTape k = false := by
    dsimp only [markedTape]
    exact markingTape_delimiter base k
  change natRun ⟨.scanStart, 0, base⟩ (3 * k + 2) = _
  rw [show 3 * k + 2 = 1 + (3 * k + 1) by omega,
    natRun_add, natRun_one,
    natStep_scanStart_zero _ _ hfirstZero]
  rw [show 3 * k + 1 = (k - 1) + (2 * k + 2) by omega,
    natRun_add, natRun_scanZeros base hscanZeros]
  rw [show 1 + (k - 1) = k by omega]
  rw [show 2 * k + 2 = 1 + (2 * k + 1) by omega,
    natRun_add, natRun_one,
    natStep_scanZeros_one _ _ hone, hmarkStart]
  rw [show 2 * k + 1 = k + (k + 1) by omega,
    natRun_add, natRun_markingPrefix base k k (Nat.le_refl k) hzero]
  unfold markingConfig
  rw [hmarkedHead]
  change natRun ⟨.markLeft, 0, markedTape⟩ (k + 1) = _
  rw [show k + 1 = 1 + k by omega, natRun_add, natRun_one,
    natStep_markLeft_one _ _ hmarkedZero]
  rw [show k = (k - 1) + 1 by omega,
    natRun_add, natRun_seekDelimiter markedTape hseekOnes]
  rw [show 1 + (k - 1) = k by omega]
  rw [natRun_one, natStep_seekDelimiter_zero _ _ hdelimiter]
  unfold progressConfig
  rw [markingTape_complete_counter]
  congr 1
  rw [show k - 1 + 1 = k by omega]

theorem progressTape_zero_eq_of_terminator
    (base : Nat → Bool) (hone : base 0 = true) :
    progressTape base 0 0 = base := by
  funext position
  unfold progressTape
  by_cases hzero : position = 0
  · subst position
    simp [hone]
  · simp [hzero]

/-- The `k = 0` gamma prefix is the single terminator.  One fixed-control
step leaves its marker at `0` and advances the head to `1`. -/
theorem natRun_initialize_zero (base : Nat → Bool) (hone : base 0 = true) :
    natRun (sourceConfig base) 1 = finishedConfig base 0 := by
  change natRun ⟨.scanStart, 0, base⟩ 1 = _
  rw [natRun_one, natStep_scanStart_one _ _ hone]
  unfold finishedConfig
  rw [progressTape_zero_eq_of_terminator base hone]

/-- Exact useful trace length from the original gamma prefix to the
next-field head position. -/
def finishTime (k : Nat) : Nat :=
  if k = 0 then 1 else 2 * k * k + 7 * k

@[simp] theorem finishTime_zero : finishTime 0 = 1 := by
  simp [finishTime]

theorem finishTime_pos (k : Nat) : 0 < finishTime k := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp [finishTime, hk]
    omega

/-- Complete natural-coordinate execution theorem. -/
theorem natRun_source_to_finished (base : Nat → Bool) (k : Nat)
    (hzero : ∀ position, position < k → base position = false)
    (hone : base k = true) :
    natRun (sourceConfig base) (finishTime k) =
      finishedConfig base k := by
  by_cases hk : k = 0
  · subst k
    simpa using natRun_initialize_zero base hone
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have htime : 2 * k * k + 7 * k =
        (3 * k + 2) + (2 * k * k + 4 * k - 2) := by
      cases k with
      | zero => contradiction
      | succ predecessor =>
          ring_nf
          omega
    rw [finishTime, if_neg hk, htime, natRun_add,
      natRun_initialize_positive base k hkpos hzero hone]
    exact natRun_all_progress_cycles base k hkpos

/-! ## Polynomial clock and actual repository execution -/

theorem natStep_head_le_succ (config : NatConfig) :
    (natStep config).head ≤ config.head + 1 := by
  unfold natStep
  generalize hresult : gammaPrefixWalker.step config.state
    (config.tape config.head) = result
  rcases result with ⟨nextState, written, move⟩
  cases move <;> simp [moveNat] <;> omega

theorem natRun_head_le (config : NatConfig) (steps : Nat) :
    (natRun config steps).head ≤ config.head + steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [natRun_succ]
      have hstep := natStep_head_le_succ (natRun config steps)
      omega

theorem finishTime_le_local_clock (k : Nat) :
    finishTime k ≤ (k + 1) ^ 3 + 3 := by
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk1 : k = 1
  · subst k
    norm_num [finishTime]
  by_cases hk2 : k = 2
  · subst k
    norm_num [finishTime]
  have hk3 : 3 ≤ k := by omega
  have hsevenBase : 7 ≤ 4 * k := by omega
  have hseven : 7 * k ≤ 4 * k * k :=
    Nat.mul_le_mul_right k hsevenBase
  have hthree : 3 * k ≤ k * k :=
    Nat.mul_le_mul_right k hk3
  have hcubic : 3 * k * k ≤ k * k * k :=
    Nat.mul_le_mul_right k hthree
  rw [finishTime, if_neg hk0]
  calc
    2 * k * k + 7 * k ≤ 2 * k * k + 4 * k * k :=
      Nat.add_le_add_left hseven _
    _ = 6 * k * k := by ring
    _ = 3 * k * k + 3 * k * k := by ring
    _ ≤ k * k * k + 3 * k * k :=
      Nat.add_le_add_right hcubic _
    _ ≤ (k + 1) ^ 3 + 3 := by
      have hexpand : (k + 1) ^ 3 + 3 =
          k * k * k + 3 * k * k + (3 * k + 4) := by ring
      rw [hexpand]
      exact Nat.le_add_right _ _

theorem finishTime_le_clock {inputLength k : Nat} (hk : k < inputLength) :
    finishTime k ≤ inputLength ^ 3 + 3 := by
  calc
    finishTime k ≤ (k + 1) ^ 3 + 3 := finishTime_le_local_clock k
    _ ≤ inputLength ^ 3 + 3 :=
      Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) 3) 3

theorem finishedHead_le_finishTime (k : Nat) :
    2 * k + 1 ≤ finishTime k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [finishTime, if_neg hk]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    omega

/-- Total natural-coordinate view of the canonical initial binary tape. -/
def inputTape {inputLength : Nat} (input : Bitstring inputLength) : Nat → Bool :=
  fun position =>
    if hposition : position < inputLength then
      input ⟨position, hposition⟩
    else
      false

@[simp] theorem inputTape_input {inputLength : Nat}
    (input : Bitstring inputLength) {position : Nat}
    (hposition : position < inputLength) :
    inputTape input position = input ⟨position, hposition⟩ := by
  simp [inputTape, hposition]

@[simp] theorem inputTape_blank {inputLength : Nat}
    (input : Bitstring inputLength) {position : Nat}
    (hposition : inputLength ≤ position) :
    inputTape input position = false := by
  simp [inputTape, Nat.not_lt.mpr hposition]

theorem sourceConfig_embed_eq_initialConfig {inputLength : Nat}
    (input : Bitstring inputLength)
    (hhead : (sourceConfig (inputTape input)).head <
      gammaPrefixWalker.executionTM.tapeLength inputLength) :
    (sourceConfig (inputTape input)).embed hhead =
      gammaPrefixWalker.executionTM.initialConfig input := by
  unfold sourceConfig NatConfig.embed TM.initialConfig inputTape
  rw [TM.Configuration.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · apply Fin.ext
    rfl
  · funext position
    rfl

/-- Exact actual-TM configuration at the end of the useful quadratic trace. -/
theorem runConfig_finish_of_zero_prefix
    {inputLength k : Nat} (input : Bitstring inputLength)
    (hk : k < inputLength)
    (hzero : ∀ (position : Nat) (hposition : position < k),
      input ⟨position, hposition.trans hk⟩ = false)
    (hone : input ⟨k, hk⟩ = true) :
    gammaPrefixWalker.executionTM.runConfig
        (gammaPrefixWalker.executionTM.initialConfig input)
        (finishTime k) =
      (finishedConfig (inputTape input) k).embed (by
        change 2 * k + 1 <
          gammaPrefixWalker.executionTM.tapeLength inputLength
        rw [gammaPrefixWalker_tapeLength]
        have hclock := finishTime_le_clock hk
        have hfinish := finishedHead_le_finishTime k
        omega) := by
  let source := sourceConfig (inputTape input)
  have hbaseZero : ∀ position, position < k →
      inputTape input position = false := by
    intro position hposition
    have hinput : position < inputLength := hposition.trans hk
    simpa [inputTape, hinput] using hzero position hposition
  have hbaseOne : inputTape input k = true := by
    simpa [inputTape, hk] using hone
  have htrace := natRun_source_to_finished (inputTape input) k
    hbaseZero hbaseOne
  have hclock := finishTime_le_clock hk
  have hbound : ∀ elapsed, elapsed ≤ finishTime k →
      (natRun source elapsed).head + 1 <
        gammaPrefixWalker.executionTM.tapeLength inputLength := by
    intro elapsed helapsed
    have hhead := natRun_head_le source elapsed
    rw [gammaPrefixWalker_tapeLength]
    dsimp only [source, sourceConfig] at hhead ⊢
    omega
  have hsim := NatConfig.runConfig_embed source (finishTime k) hbound
  have hsource : source.embed (by
        have := hbound 0 (Nat.zero_le (finishTime k))
        simpa using Nat.lt_of_succ_lt this) =
      gammaPrefixWalker.executionTM.initialConfig input := by
    dsimp only [source]
    apply sourceConfig_embed_eq_initialConfig
  have hfinal : natRun source (finishTime k) =
      finishedConfig (inputTape input) k := by
    simpa only [source] using htrace
  calc
    gammaPrefixWalker.executionTM.runConfig
        (gammaPrefixWalker.executionTM.initialConfig input) (finishTime k) =
        gammaPrefixWalker.executionTM.runConfig
          (source.embed (by
            have := hbound 0 (Nat.zero_le (finishTime k))
            simpa using Nat.lt_of_succ_lt this)) (finishTime k) := by
          rw [hsource]
    _ = (natRun source (finishTime k)).embed (by
          have := hbound (finishTime k) (Nat.le_refl (finishTime k))
          exact Nat.lt_of_succ_lt this) := hsim
    _ = (finishedConfig (inputTape input) k).embed (by
          change 2 * k + 1 <
            gammaPrefixWalker.executionTM.tapeLength inputLength
          rw [gammaPrefixWalker_tapeLength]
          have hfinish := finishedHead_le_finishTime k
          omega) := NatConfig.embed_eq_of_eq _ _ hfinal

/-- The successful state is configuration-wise absorbing. -/
@[simp] theorem stepConfig_done {inputLength : Nat}
    (config : TM.Configuration
      (M := gammaPrefixWalker.executionTM) inputLength)
    (hstate : config.state = .done) :
    gammaPrefixWalker.executionTM.stepConfig config = config := by
  cases config with
  | mk state head tape =>
      simp only at hstate
      subst state
      simp only [TM.stepConfig, OperationalTM.executionTM,
        gammaPrefixWalker, TM.Configuration.moveHead]
      congr 1
      funext position
      by_cases hposition : position = head
      · subst position
        simp [TM.Configuration.write]
      · simp [TM.Configuration.write, hposition]

theorem runConfig_done {inputLength : Nat}
    (config : TM.Configuration
      (M := gammaPrefixWalker.executionTM) inputLength)
    (hstate : config.state = .done) (steps : Nat) :
    gammaPrefixWalker.executionTM.runConfig config steps = config := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [TM.runConfig_succ, ih]
      exact stepConfig_done config hstate

/-- Exact canonical-clock result.  The useful quadratic trace finishes first;
all remaining cubic-clock steps are absorbing. -/
theorem run_eq_finished_of_zero_prefix
    {inputLength k : Nat} (input : Bitstring inputLength)
    (hk : k < inputLength)
    (hzero : ∀ (position : Nat) (hposition : position < k),
      input ⟨position, hposition.trans hk⟩ = false)
    (hone : input ⟨k, hk⟩ = true) :
    gammaPrefixWalker.executionTM.run input =
      (finishedConfig (inputTape input) k).embed (by
        change 2 * k + 1 <
          gammaPrefixWalker.executionTM.tapeLength inputLength
        rw [gammaPrefixWalker_tapeLength]
        have hclock := finishTime_le_clock hk
        have hfinish := finishedHead_le_finishTime k
        omega) := by
  have hfinish := runConfig_finish_of_zero_prefix input hk hzero hone
  have hclock := finishTime_le_clock hk
  have hsplit : inputLength ^ 3 + 3 =
      finishTime k + (inputLength ^ 3 + 3 - finishTime k) := by
    omega
  unfold TM.run
  change gammaPrefixWalker.executionTM.runConfig
    (gammaPrefixWalker.executionTM.initialConfig input)
    (inputLength ^ 3 + 3) = _
  calc
    gammaPrefixWalker.executionTM.runConfig
        (gammaPrefixWalker.executionTM.initialConfig input)
        (inputLength ^ 3 + 3) =
        gammaPrefixWalker.executionTM.runConfig
          (gammaPrefixWalker.executionTM.initialConfig input)
          (finishTime k +
            (inputLength ^ 3 + 3 - finishTime k)) :=
      congrArg
        (gammaPrefixWalker.executionTM.runConfig
          (gammaPrefixWalker.executionTM.initialConfig input)) hsplit
    _ = gammaPrefixWalker.executionTM.runConfig
          (gammaPrefixWalker.executionTM.runConfig
            (gammaPrefixWalker.executionTM.initialConfig input)
            (finishTime k))
          (inputLength ^ 3 + 3 - finishTime k) :=
      TM.runConfig_add _ _ _
    _ = gammaPrefixWalker.executionTM.runConfig
          ((finishedConfig (inputTape input) k).embed _)
          (inputLength ^ 3 + 3 - finishTime k) :=
      congrArg
        (fun config => gammaPrefixWalker.executionTM.runConfig config
          (inputLength ^ 3 + 3 - finishTime k)) hfinish
    _ = (finishedConfig (inputTape input) k).embed _ :=
      runConfig_done _ (by rfl) _

theorem run_state_done_of_zero_prefix
    {inputLength k : Nat} (input : Bitstring inputLength)
    (hk : k < inputLength)
    (hzero : ∀ (position : Nat) (hposition : position < k),
      input ⟨position, hposition.trans hk⟩ = false)
    (hone : input ⟨k, hk⟩ = true) :
    (gammaPrefixWalker.executionTM.run input).state = .done := by
  rw [run_eq_finished_of_zero_prefix input hk hzero hone]
  rfl

theorem run_head_eq_two_mul_add_one_of_zero_prefix
    {inputLength k : Nat} (input : Bitstring inputLength)
    (hk : k < inputLength)
    (hzero : ∀ (position : Nat) (hposition : position < k),
      input ⟨position, hposition.trans hk⟩ = false)
    (hone : input ⟨k, hk⟩ = true) :
    (gammaPrefixWalker.executionTM.run input).head.val = 2 * k + 1 := by
  rw [run_eq_finished_of_zero_prefix input hk hzero hone]
  rfl

theorem accepts_eq_true_of_zero_prefix
    {inputLength k : Nat} (input : Bitstring inputLength)
    (hk : k < inputLength)
    (hzero : ∀ (position : Nat) (hposition : position < k),
      input ⟨position, hposition.trans hk⟩ = false)
    (hone : input ⟨k, hk⟩ = true) :
    gammaPrefixWalker.accepts inputLength input = true := by
  unfold OperationalTM.accepts
  rw [run_state_done_of_zero_prefix input hk hzero hone]
  rfl

/-! ## All-zero rejection and the blank-zero limitation -/

theorem natRun_source_all_zero (base : Nat → Bool) (steps : Nat)
    (hsteps : 0 < steps) (hallZero : ∀ position, base position = false) :
    natRun (sourceConfig base) steps =
      ⟨.scanZeros, steps, base⟩ := by
  have htail : ∀ offset, offset < steps - 1 →
      base (1 + offset) = false := by
    intro offset _hoffset
    exact hallZero _
  change natRun ⟨.scanStart, 0, base⟩ steps = _
  rw [show steps = 1 + (steps - 1) by omega,
    natRun_add, natRun_one,
    natStep_scanStart_zero _ _ (hallZero 0),
    natRun_scanZeros base htail]

def allZeroFinishedConfig (base : Nat → Bool) (steps : Nat) : NatConfig :=
  { state := .scanZeros, head := steps, tape := base }

/-- At the canonical clock an all-zero input is still in the scanning state;
the tape is untouched.  This includes the empty input. -/
theorem run_eq_allZeroFinished
    {inputLength : Nat} (input : Bitstring inputLength)
    (hallZero : ∀ index : Fin inputLength, input index = false) :
    gammaPrefixWalker.executionTM.run input =
      (allZeroFinishedConfig (inputTape input) (inputLength ^ 3 + 3)).embed (by
        change inputLength ^ 3 + 3 <
          gammaPrefixWalker.executionTM.tapeLength inputLength
        rw [gammaPrefixWalker_tapeLength]
        omega) := by
  let steps := inputLength ^ 3 + 3
  let source := sourceConfig (inputTape input)
  have hsteps : 0 < steps := by
    dsimp only [steps]
    omega
  have hbaseZero : ∀ position, inputTape input position = false := by
    intro position
    by_cases hposition : position < inputLength
    · simpa [inputTape, hposition] using hallZero ⟨position, hposition⟩
    · exact inputTape_blank input (Nat.le_of_not_gt hposition)
  have htrace : natRun source steps =
      allZeroFinishedConfig (inputTape input) steps := by
    dsimp only [source, allZeroFinishedConfig]
    exact natRun_source_all_zero (inputTape input) steps hsteps hbaseZero
  have hheads : ∀ elapsed, elapsed ≤ steps →
      (natRun source elapsed).head <
        gammaPrefixWalker.executionTM.tapeLength inputLength := by
    intro elapsed helapsed
    have hhead := natRun_head_le source elapsed
    rw [gammaPrefixWalker_tapeLength]
    dsimp only [source, sourceConfig, steps] at hhead ⊢
    omega
  have hrights : ∀ elapsed, elapsed < steps →
      (natRun source elapsed).head + 1 <
        gammaPrefixWalker.executionTM.tapeLength inputLength := by
    intro elapsed helapsed
    have hhead := natRun_head_le source elapsed
    rw [gammaPrefixWalker_tapeLength]
    dsimp only [source, sourceConfig, steps] at hhead ⊢
    omega
  have hsim := NatConfig.runConfig_embed_bounded source steps hheads hrights
  have hsource : source.embed (hheads 0 (Nat.zero_le steps)) =
      gammaPrefixWalker.executionTM.initialConfig input := by
    dsimp only [source]
    apply sourceConfig_embed_eq_initialConfig
  unfold TM.run
  change gammaPrefixWalker.executionTM.runConfig
      (gammaPrefixWalker.executionTM.initialConfig input) steps = _
  calc
    gammaPrefixWalker.executionTM.runConfig
        (gammaPrefixWalker.executionTM.initialConfig input) steps =
        gammaPrefixWalker.executionTM.runConfig
          (source.embed (hheads 0 (Nat.zero_le steps))) steps := by
      rw [hsource]
    _ = (natRun source steps).embed
          (hheads steps (Nat.le_refl steps)) := hsim
    _ = (allZeroFinishedConfig (inputTape input) steps).embed _ :=
      NatConfig.embed_eq_of_eq _ _ htrace

theorem run_state_scanZeros_of_all_zero
    {inputLength : Nat} (input : Bitstring inputLength)
    (hallZero : ∀ index : Fin inputLength, input index = false) :
    (gammaPrefixWalker.executionTM.run input).state = .scanZeros := by
  rw [run_eq_allZeroFinished input hallZero]
  rfl

theorem accepts_eq_false_of_all_zero
    {inputLength : Nat} (input : Bitstring inputLength)
    (hallZero : ∀ index : Fin inputLength, input index = false) :
    gammaPrefixWalker.accepts inputLength input = false := by
  unfold OperationalTM.accepts
  rw [run_state_scanZeros_of_all_zero input hallZero]
  rfl

/-! ## Canonical gamma input and explicit malformed behaviour -/

/-- A terminator with no physical payload cells after it.  For `k > 0` this
is a truncated gamma field, even though blank work-tape cells read as zero. -/
def truncatedGammaInput (k : Nat) : Bitstring (k + 1) :=
  fun position => decide (position.val = k)

@[simp] theorem truncatedGammaInput_zero (k position : Nat)
    (hposition : position < k) :
    truncatedGammaInput k ⟨position, by omega⟩ = false := by
  simp [truncatedGammaInput]
  omega

@[simp] theorem truncatedGammaInput_terminator (k : Nat) :
    truncatedGammaInput k ⟨k, by omega⟩ = true := by
  simp [truncatedGammaInput]

/-- Formal blank-zero limitation: for every positive `k`, a physically
missing `k`-bit payload is nevertheless consumed from blank tape and accepted.
This theorem is why the module is not advertised as a full parser. -/
theorem accepts_truncated_zero_payload (k : Nat) :
    gammaPrefixWalker.accepts (k + 1) (truncatedGammaInput k) = true := by
  exact accepts_eq_true_of_zero_prefix
    (input := truncatedGammaInput k) (k := k)
    (by omega)
    (by
      intro position hposition
      exact truncatedGammaInput_zero k position hposition)
    (truncatedGammaInput_terminator k)

theorem truncated_run_endpoint_beyond_input (k : Nat) (hk : 0 < k) :
    (gammaPrefixWalker.executionTM.run (truncatedGammaInput k)).head.val =
        2 * k + 1 ∧
      k + 1 < 2 * k + 1 := by
  constructor
  · exact run_head_eq_two_mul_add_one_of_zero_prefix
      (input := truncatedGammaInput k) (k := k)
      (by omega)
      (by
        intro position hposition
        exact truncatedGammaInput_zero k position hposition)
      (truncatedGammaInput_terminator k)
  · omega

open Pnp4.Frontier.ContractExpansion

/-- The walker accepts the repository's real canonical Elias-gamma bitvector.
This proves correct field-span consumption, but not preservation or numeric
decoding of its payload. -/
theorem accepts_canonical_gammaBit (value : Nat) :
    gammaPrefixWalker.accepts (gammaLen value)
      (fun position : Fin (gammaLen value) => gammaBit value position) = true := by
  let k := bitLength (value + 1) - 1
  have hk : k < gammaLen value := by
    dsimp only [k]
    rw [gammaLen_eq_zeros_add_bitLength]
    exact Nat.lt_add_of_pos_right
      (bitLength_pos_of_pos (Nat.succ_pos value))
  exact accepts_eq_true_of_zero_prefix
    (input := fun position : Fin (gammaLen value) => gammaBit value position)
    (k := k) hk
    (by
      intro position hposition
      apply gammaBit_zero_prefix
      exact hposition)
    (by
      dsimp only [k]
      simpa using gammaBit_terminator value)

theorem canonical_gammaBit_run_head_eq_gammaLen (value : Nat) :
    (gammaPrefixWalker.executionTM.run
      (fun position : Fin (gammaLen value) => gammaBit value position)).head.val =
        gammaLen value := by
  let k := bitLength (value + 1) - 1
  have hk : k < gammaLen value := by
    dsimp only [k]
    rw [gammaLen_eq_zeros_add_bitLength]
    exact Nat.lt_add_of_pos_right
      (bitLength_pos_of_pos (Nat.succ_pos value))
  have hhead := run_head_eq_two_mul_add_one_of_zero_prefix
    (input := fun position : Fin (gammaLen value) => gammaBit value position)
    (k := k) hk
    (by
      intro position hposition
      apply gammaBit_zero_prefix
      exact hposition)
    (by
      dsimp only [k]
      simpa using gammaBit_terminator value)
  have hlength : 2 * k + 1 = gammaLen value := by
    dsimp only [k]
    rw [gammaLen_eq_two_mul_zeros_add_one]
  exact hhead.trans hlength

end OperationalGammaPrefix
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaPrefix.natRun_progress_round
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaPrefix.run_eq_finished_of_zero_prefix
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaPrefix.accepts_eq_false_of_all_zero
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaPrefix.accepts_truncated_zero_payload
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaPrefix.accepts_canonical_gammaBit
