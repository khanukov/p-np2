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
  Узкий контракт для шага "general -> local":
  для каждого малого общего решателя достаточно предъявить *какой-то*
  локальный решатель с нужным `FamilyIsLocalCircuit`‑свидетельством.

  Это строго слабее прежней глобальной гипотезы `∀ loc, ...`.
-/
def LocalizedFamilyWitnessHypothesis_partial
  (p : Models.GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallGeneralCircuitSolver_Partial p,
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : SmallLocalCircuitSolver_Partial p),
      T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
      loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
      loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
      loc.params.params.depth ≤ solver.params.params.depth ∧
      ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
        (Counting.allFunctionsFamily loc.params.params.n)

/--
  Переход от legacy‑гипотезы `∀ loc, ...` к узкому контракту
  `LocalizedFamilyWitnessHypothesis_partial`.
-/
lemma localizedFamilyWitnessHypothesis_of_hF_all
  {p : Models.GapPartialMCSPParams}
  (hF_all : ∀ loc : SmallLocalCircuitSolver_Partial p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  LocalizedFamilyWitnessHypothesis_partial p := by
  intro solver
  obtain ⟨T, loc, hT, hM, hℓ, hdepth⟩ := locality_lift_partial solver
  exact ⟨T, loc, hT, hM, hℓ, hdepth, hF_all loc⟩

theorem LB_GeneralFromLocal_partial
  {p : Models.GapPartialMCSPParams}
  (solver : SmallGeneralCircuitSolver_Partial p)
  (hLocalized : LocalizedFamilyWitnessHypothesis_partial p) : False := by
  classical
  obtain ⟨_T, loc, _hT, _hM, _hℓ, _hdepth, hF_loc⟩ := hLocalized solver
  exact LB_LocalCircuits_core_partial (p := p) (solver := loc) hF_loc

end LowerBounds
end Pnp3
