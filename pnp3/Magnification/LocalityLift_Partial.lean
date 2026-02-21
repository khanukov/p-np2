import Mathlib.Data.Finset.Basic
import Core.BooleanBasics
import LowerBounds.AntiChecker_Partial
import Models.Model_PartialMCSP
import Magnification.LocalityInterfaces_Partial
import ThirdPartyFacts.PartialLocalityLift

/-!
  `Magnification.LocalityLift_Partial` is a thin façade delegating to the
  Partial MCSP bridge in `ThirdPartyFacts.PartialLocalityLift`.
-/

namespace Pnp3
namespace Magnification

open Models
open LowerBounds

@[inline] def locality_lift_partial
  {p : Models.GapPartialMCSPParams}
  (solver : SmallGeneralCircuitSolver_Partial p)
  (hStable :
    ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
      r.alive.card ≤ Partial.tableLen p.n / 2 ∧
      ∀ x : Core.BitVec (Models.partialInputLen p),
        solver.decide (r.apply x) = solver.decide x)
  (hProvider :
    Facts.LocalityLift.ShrinkageWitness.Provider
      (p := ThirdPartyFacts.toFactsParamsPartial p)
      (ThirdPartyFacts.toFactsGeneralSolverPartial solver)) :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth :=
  ThirdPartyFacts.locality_lift_partial
    (p := p) (solver := solver) (hStable := hStable) (hProvider := hProvider)

@[inline] def locality_lift_partial_of_certificate
  {p : Models.GapPartialMCSPParams}
  (solver : SmallGeneralCircuitSolver_Partial p)
  [hCert :
    Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.Provider
      (p := ThirdPartyFacts.toFactsParamsPartial p)
      (ThirdPartyFacts.toFactsGeneralSolverPartial solver)
      (ThirdPartyFacts.solverDecideFacts (p := p) solver)]
  (hCardHalf :
    (Facts.LocalityLift.ShrinkageWitness.ShrinkageCertificate.provided
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (general := ThirdPartyFacts.toFactsGeneralSolverPartial solver)
        (generalEval := ThirdPartyFacts.solverDecideFacts (p := p) solver)).restriction.alive.card
      ≤ Partial.tableLen p.n / 2) :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth :=
  ThirdPartyFacts.locality_lift_partial_of_certificate
    (p := p) (solver := solver) hCardHalf

@[inline] def no_general_solver_of_no_local_partial
  {p : Models.GapPartialMCSPParams}
  (H : ∀ _solver : LowerBounds.SmallLocalCircuitSolver_Partial p, False)
  (hGeneralStable :
    ∀ solver : SmallGeneralCircuitSolver_Partial p,
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          solver.decide (r.apply x) = solver.decide x)
  (hProvider :
    ∀ solver : SmallGeneralCircuitSolver_Partial p,
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial solver)) :
  ∀ _solver : SmallGeneralCircuitSolver_Partial p, False :=
  ThirdPartyFacts.no_general_solver_of_no_local_partial
    (p := p) H hGeneralStable hProvider

end Magnification
end Pnp3
