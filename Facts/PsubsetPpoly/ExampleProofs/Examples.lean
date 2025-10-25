import FactPsubsetPpoly
import Proof.Turing.Encoding

/-!
# Example witnesses for `P ⊆ P/poly`

This module packages explicit polynomial-time machines and languages that are
decided by the constructive simulation developed in the standalone proof.  The
examples double as regression tests: they exercise the public API and provide
hand-checkable reference points for the `P ⊆ P/poly` theorem.
-/

open Facts
open Complexity
open TM

namespace Facts
namespace PsubsetPpoly
namespace Tests

open scoped Classical

/--
Helper constructors for short bitstrings.  These make it easy to craft inputs
for the demonstrative machines without having to unfold `Fin` indices manually.
-/
def bitstring₁ (b : Bool) : Bitstring 1
  | ⟨0, _⟩ => b

/-- Assemble a bitstring of length two from its individual coordinates. -/
def bitstring₂ (b₀ b₁ : Bool) : Bitstring 2
  | ⟨0, _⟩ => b₀
  | ⟨1, _⟩ => b₁

/-- The language containing every bitstring. -/
def constTrueLanguage : Language := fun _ _ => true

/-- A machine that accepts immediately without reading the tape. -/
def constTrueTM : TM where
  state := Unit
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := ()
  accept := ()
  step := fun _ _ => ((), true, Move.stay)
  runTime := fun _ => 0

lemma constTrue_runTime : ∀ n, constTrueTM.runTime n ≤ n ^ 0 + 0 := by
  intro n
  simp [constTrueTM]

lemma constTrue_correct :
    ∀ n (x : Bitstring n),
      TM.accepts (M := constTrueTM) (n := n) x = constTrueLanguage n x := by
  intro n x
  simp [constTrueLanguage, constTrueTM, TM.accepts, TM.run, TM.runConfig]

/-- Witness that the constant-true language belongs to `P/poly`. -/
noncomputable def constTrue_inPpoly : InPpoly constTrueLanguage :=
  inPpoly_of_polyBound (M := constTrueTM) (c := 0)
    constTrue_runTime constTrue_correct

lemma constTrue_in_Ppoly_via_theorem : constTrueLanguage ∈ Ppoly := by
  have hP : constTrueLanguage ∈ P := by
    refine ⟨constTrueTM, 0, constTrue_runTime, constTrue_correct⟩
  exact complexity_P_subset_Ppoly hP

@[simp] lemma constTrueLanguage_eval (n : ℕ) (x : Bitstring n) :
    constTrueLanguage n x = true := rfl

/--
The machine accepts the sample bitstring consisting entirely of zeroes.  This
lemma is a sanity check used by the executable test harness.
-/
lemma constTrueTM_accepts_zero (n : ℕ) (x : Bitstring n) :
    TM.accepts (M := constTrueTM) (n := n) x = true := by
  simpa using constTrue_correct (n := n) (x := x)

/-- A language that checks whether the first input bit is one. -/
def firstBitLanguage : Language :=
  fun n x => if h : 0 < n then x ⟨0, h⟩ else false

/-- Deterministic machine deciding the first-bit language in one step. -/
def firstBitTM : TM where
  state := Bool
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := false
  accept := true
  step := fun q b =>
    if q then
      (true, b, Move.stay)
    else if b then
      (true, b, Move.stay)
    else
      (false, b, Move.stay)
  runTime := fun _ => 1

lemma firstBit_runTime : ∀ n, firstBitTM.runTime n ≤ n ^ 1 + 1 := by
  intro n
  simp [firstBitTM]

lemma firstBit_correct :
    ∀ n (x : Bitstring n),
      TM.accepts (M := firstBitTM) (n := n) x = firstBitLanguage n x := by
  classical
  intro n x
  have hRun : TM.run (M := firstBitTM) (n := n) x =
      TM.stepConfig (M := firstBitTM) (n := n) (firstBitTM.initialConfig x) := by
    simp [firstBitTM, TM.run, TM.runConfig]
  by_cases hpos : 0 < n
  · have hSymbol :
        (firstBitTM.initialConfig x).tape
            (firstBitTM.initialConfig x).head = x ⟨0, hpos⟩ := by
        simpa [firstBitTM]
          using TM.initial_tape_input (M := firstBitTM) (x := x)
            (i := (firstBitTM.initialConfig x).head) (hi := hpos)
    have hState :
        (firstBitTM.step (firstBitTM.initialConfig x).state
          ((firstBitTM.initialConfig x).tape
            (firstBitTM.initialConfig x).head)).fst =
          (x ⟨0, hpos⟩) := by
      simp [firstBitTM, hSymbol]
    have hAccept :
        TM.accepts (M := firstBitTM) (n := n) x = (x ⟨0, hpos⟩) := by
      simp [TM.accepts, hRun, TM.stepConfig, firstBitTM, hState, hSymbol,
        TM.Configuration.moveHead, TM.Configuration.write]
    simp [firstBitLanguage, hpos, hAccept]
  · have hn0 : n = 0 := by
        by_contra hneq
        exact hpos (Nat.pos_of_ne_zero hneq)
    subst hn0
    have hSymbol :
        (firstBitTM.initialConfig x).tape
            (firstBitTM.initialConfig x).head = false := by
      simp [firstBitTM, TM.initialConfig]
    have hState :
        (firstBitTM.step (firstBitTM.initialConfig x).state
          ((firstBitTM.initialConfig x).tape
            (firstBitTM.initialConfig x).head)).fst = false := by
      simp [firstBitTM, hSymbol]
    have hAccept : TM.accepts (M := firstBitTM) (n := n) x = false := by
      simp [TM.accepts, hRun, TM.stepConfig, firstBitTM, hState, hSymbol,
        TM.Configuration.moveHead, TM.Configuration.write]
    simp [firstBitLanguage, hpos, hAccept]

/-- Witness showing the first-bit language is in `P/poly`. -/
noncomputable def firstBit_inPpoly : InPpoly firstBitLanguage :=
  inPpoly_of_polyBound (M := firstBitTM) (c := 1)
    firstBit_runTime firstBit_correct

lemma firstBit_in_Ppoly_via_theorem : firstBitLanguage ∈ Ppoly := by
  have hP : firstBitLanguage ∈ P := by
    refine ⟨firstBitTM, 1, firstBit_runTime, firstBit_correct⟩
  exact complexity_P_subset_Ppoly hP

@[simp] lemma firstBitLanguage_eval_pos {n : ℕ} (h : 0 < n) (x : Bitstring n) :
    firstBitLanguage n x = x ⟨0, h⟩ := by
  simp [firstBitLanguage, h]

@[simp] lemma firstBitLanguage_eval_zero :
    firstBitLanguage 0 (bitstring₁ false) = false := by
  simp [firstBitLanguage, bitstring₁]

/--
The machine correctly detects that the first bit is set to one on a two-bit
input.
-/
lemma firstBitTM_accepts_oneZero :
    TM.accepts (M := firstBitTM) (n := 2) (bitstring₂ true false) = true := by
  classical
  have hEval := firstBit_correct (n := 2) (x := bitstring₂ true false)
  have hPos : 0 < 2 := by decide
  simpa [bitstring₂, firstBitLanguage, hPos]
    using hEval

/--
The decider rejects when the first bit is zero, even if later bits are one.
-/
lemma firstBitTM_rejects_zeroOne :
    TM.accepts (M := firstBitTM) (n := 2) (bitstring₂ false true) = false := by
  classical
  have hEval := firstBit_correct (n := 2) (x := bitstring₂ false true)
  have hPos : 0 < 2 := by decide
  simpa [bitstring₂, firstBitLanguage, hPos]
    using hEval

end Tests
end PsubsetPpoly
end Facts
