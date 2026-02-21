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
  (hGeneralStable :
    ∀ s : SmallGeneralCircuitSolver_Partial p,
      ∃ (r : Facts.LocalityLift.Restriction (Models.partialInputLen p)),
        r.alive.card ≤ Models.Partial.tableLen p.n / 2 ∧
        ∀ x : Core.BitVec (Models.partialInputLen p),
          s.decide (r.apply x) = s.decide x)
  (hProvider :
    ∀ s : SmallGeneralCircuitSolver_Partial p,
      Facts.LocalityLift.ShrinkageWitness.Provider
        (p := ThirdPartyFacts.toFactsParamsPartial p)
        (ThirdPartyFacts.toFactsGeneralSolverPartial s)) :
  False :=
  no_general_solver_of_no_local_partial
    (fun loc => noSmallLocalCircuitSolver_partial_v2 loc)
    hGeneralStable hProvider solver

end LowerBounds
end Pnp3
