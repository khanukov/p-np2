import LowerBounds.AntiChecker_Partial
import LowerBounds.LB_Formulas
import Models.Model_PartialMCSP

/-!
  pnp3/LowerBounds/LB_LocalCircuits_Partial.lean

  Partial‑версия ядра нижней оценки для локальных схем.
-/

namespace Pnp3
namespace LowerBounds

open Classical
open Models

theorem LB_LocalCircuits_core_partial
  {p : Models.GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p) :
    False :=
  noSmallLocalCircuitSolver_partial_v2 solver

end LowerBounds
end Pnp3
