import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter

/-!
# V2-A Phase 2: non-vacuity witness

Progress classification: side-track audit formalization.  This file supplies a
minimal named admitted family (`const false`) so the Phase-2 filter is not empty.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape

/-- The simplest named honest smoke family: the constantly false formula. -/
def honestConstFalseFamily (n : Nat) : FormulaCircuit n :=
  FormulaCircuit.const false

/-- The language decided by the constant-false family. -/
def honestConstFalseLanguage : Language :=
  fun n x => FormulaCircuit.eval (honestConstFalseFamily n) x

/-- Constant one size bound for the constant-false family. -/
def honestConstFalsePolyBound (_n : Nat) : Nat := 1

/-- The constant size bound is polynomial. -/
theorem honestConstFalsePolyBound_poly :
    ∃ c : Nat, ∀ n, honestConstFalsePolyBound n ≤ n ^ c + c := by
  refine ⟨1, ?_⟩
  intro n
  unfold honestConstFalsePolyBound
  simp

/-- Strict `InPpolyFormula` package for the constant-false smoke family. -/
def honestConstFalseWitness : InPpolyFormula honestConstFalseLanguage where
  polyBound := honestConstFalsePolyBound
  polyBound_poly := honestConstFalsePolyBound_poly
  family := honestConstFalseFamily
  family_size_le := by intro n; simp [honestConstFalseFamily, honestConstFalsePolyBound, FormulaCircuit.size]
  correct := fun _ _ => rfl

/-- The named smoke family is admitted by the Phase-2 V2-A filter. -/
theorem honestConstFalseWitness_admitted :
    ProvenanceFilter_v2_V2_A_gpt55_Filter honestConstFalseWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · right
    intro n
    rfl
  · intro n
    simp [honestConstFalseWitness, honestConstFalseFamily, booleanGateCount,
      notGateCount, andGateCount, orGateCount, FormulaCircuit.support]
  · intro n
    simp [honestConstFalseWitness, honestConstFalseFamily, FormulaCircuit.depth,
      FormulaCircuit.support]
  · intro n
    simp [honestConstFalseWitness, honestConstFalseFamily, andGateCount]

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
