import LowerBounds.LB_LocalCircuits_Partial
import Magnification.LocalityLift_Partial

/-!
  pnp3/LowerBounds/LB_GeneralFromLocal_Partial.lean

  Partial‑версия моста "общие схемы → локальные схемы".
-/

namespace Pnp3
namespace LowerBounds

open Magnification

theorem LB_GeneralFromLocal_partial
  {p : Models.GapPartialMCSPParams}
  (solver : SmallGeneralCircuitSolver_Partial p)
  (hF_all : ∀ loc : SmallLocalCircuitSolver_Partial p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) : False := by
  classical
  obtain ⟨T, loc, hT, hM, hℓ, hdepth⟩ := locality_lift_partial solver
  exact LB_LocalCircuits_core_partial (p := p) (solver := loc) (hF_all loc)

end LowerBounds
end Pnp3
