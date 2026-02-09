import Complexity.Interfaces
import ThirdPartyFacts.PpolyFormula
import Mathlib.Data.Finset.Basic

namespace Pnp3.Tests

open Pnp3
open Pnp3.ComplexityInterfaces

/-- Simple language used to demonstrate a fully explicit structured witness. -/
def constFalseLanguage : Language := fun _ _ => false

/--
Structured `P/poly` witness for `constFalseLanguage`: a single trivial carrier
whose evaluator always returns `false`.
-/
noncomputable def constFalseStructuredWitness :
    Facts.PsubsetPpoly.Complexity.InPpolyStructured.{0} constFalseLanguage where
  Circuit := fun _ => PUnit
  family := fun _ => PUnit.unit
  eval := fun _ _ _ => false
  correct := by
    intro n x
    rfl

theorem constFalse_inPpolyStructured :
    PpolyStructured constFalseLanguage := by
  exact ⟨constFalseStructuredWitness, trivial⟩

/--
Carrier-specific locality proof with no external axioms:
the empty alive-set suffices for the constant-false language.
-/
theorem constFalse_locality_no_axiom (n : Nat) :
    ∃ (alive : Finset (Fin n)),
      alive.card ≤ n / 4 ∧
      ∀ x y : Core.BitVec n,
        (∀ i ∈ alive, x i = y i) → constFalseLanguage n x = constFalseLanguage n y := by
  refine ⟨∅, ?_, ?_⟩
  · simp
  · intro x y hAgree
    simp [constFalseLanguage]

/--
The same locality shape can be obtained through the current structured bridge.
This theorem is here only to show interface compatibility with the active
pipeline signatures.
-/
theorem constFalse_locality_via_bridge (n : Nat) :
    ∃ (alive : Finset (Fin n)),
      alive.card ≤ n / 4 ∧
      ∀ x y : Core.BitVec n,
        (∀ i ∈ alive, x i = y i) → constFalseLanguage n x = constFalseLanguage n y := by
  exact
    ThirdPartyFacts.ppolyStructured_circuit_locality
      constFalseLanguage constFalse_inPpolyStructured n

end Pnp3.Tests
