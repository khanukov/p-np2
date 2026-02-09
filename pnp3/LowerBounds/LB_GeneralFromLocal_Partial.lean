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
  (solver : SmallGeneralCircuitSolver_Partial p) : False :=
  no_general_solver_of_no_local_partial
    (fun loc => noSmallLocalCircuitSolver_partial_v2 loc) solver

end LowerBounds
end Pnp3
