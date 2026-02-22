import Complexity.Interfaces

/-!
  pnp3/Barrier/NaturalProofs.lean

  Minimal formal interface for Razborov-Rudich style natural-proof barriers.

  This file does not assert that the active pipeline already bypasses natural
  proofs; it only provides explicit contracts for proving such a claim.
-/

namespace Pnp3
namespace Barrier

open ComplexityInterfaces

/--
Abstract "natural proof conditions" for a target language.
The fields correspond to the classical triad: constructivity, largeness,
usefulness against `P/poly`.
-/
structure NaturalProofConditions (L : Language) : Type where
  constructive : Prop
  large : Prop
  usefulAgainstPpoly : Prop

/-- A language hits the natural-proofs barrier if all three conditions hold. -/
def SatisfiesNaturalProofBarrier (L : Language) : Prop :=
  ∃ P : NaturalProofConditions L,
    P.constructive ∧ P.large ∧ P.usefulAgainstPpoly

/-- A language avoids the natural-proofs barrier if the triad cannot hold. -/
def AvoidsNaturalProofBarrier (L : Language) : Prop :=
  ¬ SatisfiesNaturalProofBarrier L

/-- Explicit witness package for natural-proofs bypass at language `L`. -/
structure NaturalProofBypassWitness (L : Language) : Prop where
  blocks :
    ∀ P : NaturalProofConditions L,
      P.constructive → P.large → P.usefulAgainstPpoly → False

/-- A bypass witness implies the formal "avoids barrier" predicate. -/
theorem avoidsNaturalProofBarrier_of_witness
    {L : Language}
    (hBypass : NaturalProofBypassWitness L) :
    AvoidsNaturalProofBarrier L := by
  intro hNat
  rcases hNat with ⟨P, hC, hL, hU⟩
  exact hBypass.blocks P hC hL hU

end Barrier
end Pnp3
