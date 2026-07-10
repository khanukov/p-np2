import Pnp4.Frontier.StreamingMagnification.OperationalUniformity
import Complexity.TMVerifier.TuringToolkit.Foundation

/-!
# A fixed-control input-uniform scan primitive

This module supplies the first genuinely input-uniform loop for the repaired
operational model.  The transition table has two Boolean states, independent
of the input length:

* `false` scans right across zeroes;
* reading the first `true` enters the absorbing `true` state;
* the absorbing state preserves the head and tape forever.

The canonical exponent is `1`, so an input of length `n` runs for exactly
`n + 1` steps.  This is enough to inspect every input position when no
terminator occurs; otherwise the controller stops moving at the first `true`.
The extra step is harmless.  This is only a unary-terminator scan.  It does
not yet count the zero prefix, decode an Elias-gamma payload, discover the
input length as tape data, or provide indirect tape addressing.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalDynamicScan

open Pnp3.ComplexityInterfaces
open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity

/-- One fixed two-state transition table.  `false` means scanning and `true`
means that a terminator has been found. -/
def scanUntilOne : OperationalTM where
  state := Bool
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := false
  step := fun found scanned =>
    if found || scanned then
      (true, scanned, Move.stay)
    else
      (false, scanned, Move.right)
  exponent := 1
  output := fun found => found

/-- The finite control really is fixed: it has exactly two states for every
input length. -/
@[simp] theorem scanUntilOne_state_card :
    Fintype.card scanUntilOne.state = 2 := by
  simp [scanUntilOne]

@[simp] theorem scanUntilOne_clock (inputLength : Nat) :
    scanUntilOne.executionTM.runTime inputLength = inputLength + 1 := by
  simp [scanUntilOne, OperationalTM.executionTM, pow_one]

@[simp] theorem scanUntilOne_tapeLength (inputLength : Nat) :
    scanUntilOne.executionTM.tapeLength inputLength =
      inputLength + (inputLength + 1) + 1 := by
  simp [TM.tapeLength, OperationalTM.executionTM, scanUntilOne, pow_one]

/-- Total read facade used to state prefix hypotheses without transporting
proofs of tape bounds through every configuration equality. -/
def tapeAt {inputLength : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (position : Nat) : Bool :=
  if h : position < scanUntilOne.executionTM.tapeLength inputLength then
    config.tape ⟨position, h⟩
  else
    false

/-- One zero-scanning step advances the head, preserves the tape, and remains
in the scanning state. -/
theorem stepConfig_scanning_zero {inputLength : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (hstate : config.state = false)
    (hscanned : config.tape config.head = false)
    (hhead : config.head.val + 1 <
      scanUntilOne.executionTM.tapeLength inputLength) :
    let next := scanUntilOne.executionTM.stepConfig config
    next.state = false ∧
      next.head.val = config.head.val + 1 ∧
      next.tape = config.tape := by
  change (scanUntilOne.executionTM.stepConfig config).state = false ∧
    (scanUntilOne.executionTM.stepConfig config).head.val =
      config.head.val + 1 ∧
    (scanUntilOne.executionTM.stepConfig config).tape = config.tape
  constructor
  · rw [TM.stepConfig_state]
    simp [OperationalTM.executionTM, scanUntilOne, hstate, hscanned]
  constructor
  · rw [TM.stepConfig_head]
    simp only [OperationalTM.executionTM, scanUntilOne, hstate, hscanned,
      Bool.false_or, Bool.false_eq_true, if_false]
    rw [TM.Configuration.moveHead_right_lt config hhead]
  · rw [TM.stepConfig_tape]
    simp only [OperationalTM.executionTM, scanUntilOne, hstate, hscanned,
      Bool.false_or, Bool.false_eq_true, if_false]
    funext position
    by_cases hposition : position = config.head
    · subst position
      simp [TM.Configuration.write, hscanned]
    · simp [TM.Configuration.write, hposition]

/-- Reading the terminator enters the done state without changing the head or
tape. -/
theorem stepConfig_scanning_one {inputLength : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (hstate : config.state = false)
    (hscanned : config.tape config.head = true) :
    let next := scanUntilOne.executionTM.stepConfig config
    next.state = true ∧ next.head = config.head ∧
      next.tape = config.tape := by
  change (scanUntilOne.executionTM.stepConfig config).state = true ∧
    (scanUntilOne.executionTM.stepConfig config).head = config.head ∧
    (scanUntilOne.executionTM.stepConfig config).tape = config.tape
  constructor
  · rw [TM.stepConfig_state]
    simp [OperationalTM.executionTM, scanUntilOne, hstate, hscanned]
  constructor
  · rw [TM.stepConfig_head]
    simp [OperationalTM.executionTM, scanUntilOne, hstate, hscanned]
  · rw [TM.stepConfig_tape]
    simp only [OperationalTM.executionTM, scanUntilOne, hstate, hscanned,
      Bool.false_or, if_true]
    funext position
    by_cases hposition : position = config.head
    · subst position
      simp [TM.Configuration.write, hscanned]
    · simp [TM.Configuration.write, hposition]

/-- The done state is fully absorbing, not merely output-stable. -/
@[simp] theorem stepConfig_done {inputLength : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (hstate : config.state = true) :
    scanUntilOne.executionTM.stepConfig config = config := by
  cases config with
  | mk state head tape =>
      simp only at hstate
      subst state
      simp only [TM.stepConfig, OperationalTM.executionTM, scanUntilOne,
        Bool.true_or, if_true, TM.Configuration.moveHead]
      congr 1
      funext position
      by_cases hposition : position = head
      · subst position
        simp [TM.Configuration.write]
      · simp [TM.Configuration.write, hposition]

/-- Once done, any number of remaining clock steps is observationally and
configuration-wise inert. -/
theorem runConfig_done {inputLength : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (hstate : config.state = true) (steps : Nat) :
    scanUntilOne.executionTM.runConfig config steps = config := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [TM.runConfig_succ]
      rw [ih]
      exact stepConfig_done config hstate

/-- Exact invariant for an arbitrary zero prefix starting at the current
head.  Unlike the old `seekRightProgram Δ`, the transition table here does
not contain `steps`; only this correctness theorem quantifies over it. -/
theorem runConfig_scans_zero_prefix {inputLength steps : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (hstate : config.state = false)
    (hbound : config.head.val + steps <
      scanUntilOne.executionTM.tapeLength inputLength)
    (hzero : ∀ offset, offset < steps →
      tapeAt config (config.head.val + offset) = false) :
    let final := scanUntilOne.executionTM.runConfig config steps
    final.state = false ∧
      final.head.val = config.head.val + steps ∧
      final.tape = config.tape := by
  induction steps with
  | zero =>
      change config.state = false ∧
        config.head.val = config.head.val + 0 ∧
        config.tape = config.tape
      exact ⟨hstate, by omega, rfl⟩
  | succ steps ih =>
      have hboundPrefix : config.head.val + steps <
          scanUntilOne.executionTM.tapeLength inputLength := by
        omega
      have hzeroPrefix : ∀ offset, offset < steps →
          tapeAt config (config.head.val + offset) = false := by
        intro offset hoffset
        exact hzero offset (by omega)
      obtain ⟨hprefixState, hprefixHead, hprefixTape⟩ :=
        ih hboundPrefix hzeroPrefix
      let prefixConfig := scanUntilOne.executionTM.runConfig config steps
      change prefixConfig.state = false at hprefixState
      change prefixConfig.head.val = config.head.val + steps at hprefixHead
      change prefixConfig.tape = config.tape at hprefixTape
      have hposition : config.head.val + steps <
          scanUntilOne.executionTM.tapeLength inputLength := hboundPrefix
      have hcell : config.tape ⟨config.head.val + steps, hposition⟩ = false := by
        have := hzero steps (by omega)
        unfold tapeAt at this
        rw [dif_pos hposition] at this
        exact this
      have hprefixScanned : prefixConfig.tape prefixConfig.head = false := by
        have hheadEq : prefixConfig.head =
            ⟨config.head.val + steps, hposition⟩ := by
          apply Fin.ext
          exact hprefixHead
        rw [hprefixTape, hheadEq]
        exact hcell
      have hright : prefixConfig.head.val + 1 <
          scanUntilOne.executionTM.tapeLength inputLength := by
        rw [hprefixHead]
        omega
      obtain ⟨hnextState, hnextHead, hnextTape⟩ :=
        stepConfig_scanning_zero prefixConfig hprefixState hprefixScanned hright
      rw [show steps + 1 = Nat.succ steps by omega, TM.runConfig_succ]
      exact ⟨hnextState, hnextHead.trans (by omega),
        hnextTape.trans hprefixTape⟩

/-- After an arbitrary zero prefix, the next `true` bit is consumed in one
step and the machine is done at exactly that position. -/
theorem runConfig_first_one {inputLength prefixLength : Nat}
    (config : TM.Configuration
      (M := scanUntilOne.executionTM) inputLength)
    (hstate : config.state = false)
    (hbound : config.head.val + prefixLength <
      scanUntilOne.executionTM.tapeLength inputLength)
    (hzero : ∀ offset, offset < prefixLength →
      tapeAt config (config.head.val + offset) = false)
    (hone : tapeAt config (config.head.val + prefixLength) = true) :
    let final := scanUntilOne.executionTM.runConfig config (prefixLength + 1)
    final.state = true ∧
      final.head.val = config.head.val + prefixLength ∧
      final.tape = config.tape := by
  obtain ⟨hprefixState, hprefixHead, hprefixTape⟩ :=
    runConfig_scans_zero_prefix config hstate hbound hzero
  let prefixConfig := scanUntilOne.executionTM.runConfig config prefixLength
  change prefixConfig.state = false at hprefixState
  change prefixConfig.head.val = config.head.val + prefixLength at hprefixHead
  change prefixConfig.tape = config.tape at hprefixTape
  have hposition : config.head.val + prefixLength <
      scanUntilOne.executionTM.tapeLength inputLength := hbound
  have hcell : config.tape
      ⟨config.head.val + prefixLength, hposition⟩ = true := by
    unfold tapeAt at hone
    rw [dif_pos hposition] at hone
    exact hone
  have hprefixScanned : prefixConfig.tape prefixConfig.head = true := by
    have hheadEq : prefixConfig.head =
        ⟨config.head.val + prefixLength, hposition⟩ := by
      apply Fin.ext
      exact hprefixHead
    rw [hprefixTape, hheadEq]
    exact hcell
  obtain ⟨hnextState, hnextHead, hnextTape⟩ :=
    stepConfig_scanning_one prefixConfig hprefixState hprefixScanned
  rw [TM.runConfig_succ]
  exact ⟨hnextState,
    (congrArg Fin.val hnextHead).trans hprefixHead,
    hnextTape.trans hprefixTape⟩

/-! ## Exact semantics from the canonical initial configuration -/

/-- If the first `true` input bit occurs after `prefixLength` zeroes, the
machine is already done after `prefixLength + 1` steps and remains done until
the exact canonical clock expires. -/
theorem run_state_eq_true_of_first_one
    {inputLength prefixLength : Nat}
    (input : Bitstring inputLength)
    (hfirst : prefixLength < inputLength)
    (hzero : ∀ (offset : Nat) (hoffset : offset < prefixLength),
      input ⟨offset, hoffset.trans hfirst⟩ = false)
    (hone : input ⟨prefixLength, hfirst⟩ = true) :
    (scanUntilOne.executionTM.run input).state = true := by
  let initial := scanUntilOne.executionTM.initialConfig input
  have hbound : initial.head.val + prefixLength <
      scanUntilOne.executionTM.tapeLength inputLength := by
    simp [initial, scanUntilOne_tapeLength]
    omega
  have hzeroTape : ∀ offset, offset < prefixLength →
      tapeAt initial (initial.head.val + offset) = false := by
    intro offset hoffset
    have hoffsetInput : offset < inputLength := hoffset.trans hfirst
    have hoffsetTape : offset <
        scanUntilOne.executionTM.tapeLength inputLength := by
      rw [scanUntilOne_tapeLength]
      omega
    unfold tapeAt
    rw [dif_pos (by simpa [initial] using hoffsetTape)]
    simpa [initial, TM.initialConfig, hoffsetInput] using
      hzero offset hoffset
  have honeTape :
      tapeAt initial (initial.head.val + prefixLength) = true := by
    have hfirstTape : prefixLength <
        scanUntilOne.executionTM.tapeLength inputLength := by
      rw [scanUntilOne_tapeLength]
      omega
    unfold tapeAt
    rw [dif_pos (by simpa [initial] using hfirstTape)]
    simpa [initial, TM.initialConfig, hfirst] using hone
  obtain ⟨hdone, _hhead, _htape⟩ :=
    runConfig_first_one initial (by rfl) hbound hzeroTape honeTape
  let afterFirst :=
    scanUntilOne.executionTM.runConfig initial (prefixLength + 1)
  change afterFirst.state = true at hdone
  have hclockSplit : inputLength + 1 =
      (prefixLength + 1) + (inputLength - prefixLength) := by
    omega
  unfold TM.run
  rw [scanUntilOne_clock, hclockSplit, TM.runConfig_add]
  exact (congrArg TM.Configuration.state
    (runConfig_done afterFirst hdone
      (inputLength - prefixLength))).trans hdone

/-- When every input bit is zero, the canonical `n + 1` clock scans the whole
input and one guaranteed blank cell, never entering the done state.  The extra
blank cell is the precise end convention available in the binary-tape model;
there is no hidden end-marker symbol. -/
theorem run_state_eq_false_of_all_zero
    {inputLength : Nat} (input : Bitstring inputLength)
    (hzero : ∀ index : Fin inputLength, input index = false) :
    (scanUntilOne.executionTM.run input).state = false := by
  let initial := scanUntilOne.executionTM.initialConfig input
  have hbound : initial.head.val + (inputLength + 1) <
      scanUntilOne.executionTM.tapeLength inputLength := by
    simp only [initial, TM.initialConfig, TM.tapeLength,
      OperationalTM.executionTM, scanUntilOne, pow_one]
    omega
  have hzeroTape : ∀ offset, offset < inputLength + 1 →
      tapeAt initial (initial.head.val + offset) = false := by
    intro offset hoffset
    have hoffsetTape : offset <
        scanUntilOne.executionTM.tapeLength inputLength := by
      rw [scanUntilOne_tapeLength]
      omega
    unfold tapeAt
    rw [dif_pos (by simpa [initial] using hoffsetTape)]
    by_cases hoffsetInput : offset < inputLength
    · simpa [initial, TM.initialConfig, hoffsetInput] using
        hzero ⟨offset, hoffsetInput⟩
    · have hblank : inputLength ≤ offset := Nat.le_of_not_gt hoffsetInput
      simp [initial, TM.initialConfig, Nat.not_lt.mpr hblank]
  have hrun := runConfig_scans_zero_prefix initial (by rfl)
    hbound hzeroTape
  unfold TM.run
  rw [scanUntilOne_clock]
  exact hrun.1

/-- First-one semantics stated directly through the executable operational
observation. -/
theorem accepts_eq_true_of_first_one
    {inputLength prefixLength : Nat}
    (input : Bitstring inputLength)
    (hfirst : prefixLength < inputLength)
    (hzero : ∀ (offset : Nat) (hoffset : offset < prefixLength),
      input ⟨offset, hoffset.trans hfirst⟩ = false)
    (hone : input ⟨prefixLength, hfirst⟩ = true) :
    scanUntilOne.accepts inputLength input = true := by
  exact run_state_eq_true_of_first_one input hfirst hzero hone

/-- All-zero inputs are rejected at the exact canonical clock. -/
theorem accepts_eq_false_of_all_zero
    {inputLength : Nat} (input : Bitstring inputLength)
    (hzero : ∀ index : Fin inputLength, input index = false) :
    scanUntilOne.accepts inputLength input = false := by
  exact run_state_eq_false_of_all_zero input hzero

/-- Complete executable semantics: the fixed program accepts exactly when the
input contains a `true` bit. -/
@[simp] theorem accepts_eq_true_iff
    (inputLength : Nat) (input : Bitstring inputLength) :
    scanUntilOne.accepts inputLength input = true ↔
      ∃ index : Fin inputLength, input index = true := by
  constructor
  · intro haccepts
    by_contra hexists
    push_neg at hexists
    have hallZero : ∀ index : Fin inputLength, input index = false := by
      intro index
      cases hvalue : input index with
      | false => rfl
      | true => exact (hexists index hvalue).elim
    have hrejected := accepts_eq_false_of_all_zero input hallZero
    rw [hrejected] at haccepts
    contradiction
  · rintro ⟨index, hindex⟩
    let predicate : Nat → Prop := fun position =>
      ∃ hposition : position < inputLength,
        input ⟨position, hposition⟩ = true
    have hexists : ∃ position, predicate position :=
      ⟨index.val, index.isLt, hindex⟩
    let first := Nat.find hexists
    have hfirstSpec : predicate first := Nat.find_spec hexists
    rcases hfirstSpec with ⟨hfirst, hone⟩
    have hzero : ∀ (offset : Nat) (hoffset : offset < first),
        input ⟨offset, hoffset.trans hfirst⟩ = false := by
      intro offset hoffset
      cases hvalue : input ⟨offset, hoffset.trans hfirst⟩ with
      | false => rfl
      | true =>
          exfalso
          exact Nat.find_min hexists hoffset
            ⟨hoffset.trans hfirst, hvalue⟩
    exact accepts_eq_true_of_first_one input hfirst hzero hone

/-! ## A concrete uniform-language capstone -/

/-- The language of bitstrings containing at least one `true` bit. -/
def ContainsOneLanguage : Language :=
  fun inputLength input =>
    decide (∃ index : Fin inputLength, input index = true)

@[simp] theorem containsOneLanguage_eq_true_iff
    (inputLength : Nat) (input : Bitstring inputLength) :
    ContainsOneLanguage inputLength input = true ↔
      ∃ index : Fin inputLength, input index = true := by
  simp [ContainsOneLanguage]

@[simp] theorem scanUntilOne_accepts
    (inputLength : Nat) (input : Bitstring inputLength) :
    scanUntilOne.accepts inputLength input =
      ContainsOneLanguage inputLength input := by
  apply Bool.eq_iff_iff.mpr
  simp [accepts_eq_true_iff]

/-- The dynamic scan is an actual `UniformP` decision procedure, witnessed by
one transition table independent of the input length. -/
theorem containsOneLanguage_in_uniformP :
    UniformP ContainsOneLanguage := by
  exact ⟨scanUntilOne, scanUntilOne_accepts⟩

end OperationalDynamicScan
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalDynamicScan.runConfig_scans_zero_prefix
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalDynamicScan.runConfig_first_one
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalDynamicScan.accepts_eq_true_iff
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalDynamicScan.containsOneLanguage_in_uniformP
