import LowerBounds.LB_LocalCircuits_Partial
import Magnification.LocalityLift_Partial

/-!
  pnp3/LowerBounds/LB_GeneralFromLocal_Partial.lean

  Partial‑версия моста "общие схемы → локальные схемы".
-/

namespace Pnp3
namespace LowerBounds

open Magnification

/--
  Realized version of the localized witness contract.

  In addition to numeric bounds, both the incoming general solver and the
  produced local solver carry explicit circuit implementations.
-/
def LocalizedFamilyWitnessHypothesis_partial_realized
  (p : Models.GapPartialMCSPParams) : Prop :=
  ∀ solver : Magnification.RealizedSmallGeneralCircuitSolver_Partial p,
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : RealizedSmallLocalCircuitSolver_Partial p)
      (_wF : ThirdPartyFacts.LocalCircuitWitness loc.base.params.params
        (Counting.allFunctionsFamily loc.base.params.params.n)),
      T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
      loc.base.params.params.M ≤ solver.base.params.params.size * (T.card.succ) ∧
      loc.base.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
      loc.base.params.params.depth ≤ solver.base.params.params.depth

/--
  Constructive realized witness from locality-lift numerics and a uniform
  `LocalCircuitWitness` for `allFunctionsFamily`.
-/
theorem localizedFamilyWitnessHypothesis_partial_realized_of_locality_lift
  {p : Models.GapPartialMCSPParams}
  (hAllLocalWitness :
    ∀ params : ThirdPartyFacts.LocalCircuitParameters,
      ThirdPartyFacts.LocalCircuitWitness params
        (Counting.allFunctionsFamily params.n)) :
  LocalizedFamilyWitnessHypothesis_partial_realized p := by
  intro solver
  rcases Magnification.locality_lift_partial (p := p) solver.base with
    ⟨T, loc, hT, hM, hℓ, hdepth⟩
  let locR : RealizedSmallLocalCircuitSolver_Partial p :=
    { base := loc
      impl := Models.Circuit.ofFunction (Models.partialInputLen p) loc.decide
      decide_eq_impl := by
        intro x
        simpa using (Models.Circuit.eval_ofFunction loc.decide x).symm }
  refine ⟨T, locR, hAllLocalWitness loc.params.params, hT, ?_, ?_, ?_⟩
  · simpa [locR] using hM
  · simpa [locR] using hℓ
  · simpa [locR] using hdepth

/--
  Realized variant of the general→local contradiction step.
-/
theorem LB_GeneralFromLocal_partial_realized
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.RealizedSmallGeneralCircuitSolver_Partial p)
  (hLocalized : LocalizedFamilyWitnessHypothesis_partial_realized p) : False := by
  classical
  obtain ⟨_T, loc, wF_loc, _hT, _hM, _hℓ, _hdepth⟩ := hLocalized solver
  exact LB_LocalCircuits_core_partial_realized (p := p) (solver := loc) wF_loc

end LowerBounds
end Pnp3
