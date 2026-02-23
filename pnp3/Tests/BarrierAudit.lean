import Magnification.Facts_Magnification_Partial
import Magnification.FinalResult
import LowerBounds.AntiChecker_Partial

/-!
  pnp3/Tests/BarrierAudit.lean

  Compile-time barrier audit.

  This file makes the locality route explicit in theorem form:
  from a strict formula witness and a structured locality provider we obtain
  a local solver, and local solvers are impossible for Partial MCSP.

  It does not claim formalized bypass certificates for Natural Proofs,
  relativization, or algebrization; those require additional interfaces.
-/

namespace Pnp3.Tests

open Pnp3
open Pnp3.Models
open Pnp3.LowerBounds
open Pnp3.Magnification
open Pnp3.ComplexityInterfaces

/--
Locality contradiction in one explicit theorem:
provider + strict formula witness + Step-C hypothesis gives `False`.
-/
theorem locality_contradiction_from_provider_witness
    (hProvider : StructuredLocalityProviderPartial)
    {p : GapPartialMCSPParams} {δ : Rat}
    (hHyp : FormulaLowerBoundHypothesisPartial p δ)
    (hFormula : PpolyFormula (gapPartialMCSP_Language p)) :
    False := by
  obtain ⟨T, loc, hT, hℓ⟩ := hProvider p δ hHyp hFormula
  exact noSmallLocalCircuitSolver_partial_v2 loc

/--
Equivalent contra statement used by OPS trigger (spelled out for audit).
-/
theorem locality_contra_np_to_formula
    (hProvider : StructuredLocalityProviderPartial)
    {p : GapPartialMCSPParams} {δ : Rat}
    (hNPstrict : NP_strict (gapPartialMCSP_Language p))
    (hHyp : FormulaLowerBoundHypothesisPartial p δ) :
    ((∀ L : Language, NP_strict L → PpolyFormula L) → False) := by
  intro hAll
  have hFormula :
      PpolyFormula (gapPartialMCSP_Language p) :=
    hAll _ hNPstrict
  exact locality_contradiction_from_provider_witness
    hProvider hHyp hFormula

-- Locality-chain audit prints.
#print axioms locality_contradiction_from_provider_witness
#print axioms locality_contra_np_to_formula
#print axioms OPS_trigger_formulas_partial_of_provider_formula_separation
#print axioms NP_not_subset_PpolyFormula_final
#print axioms P_ne_NP_final

end Pnp3.Tests
