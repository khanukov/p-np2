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
  (solver : SmallGeneralCircuitSolver_Partial p) :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth :=
  ThirdPartyFacts.locality_lift_partial (p := p) (solver := solver)

@[inline] def no_general_solver_of_no_local_partial
  {p : Models.GapPartialMCSPParams}
  (H : ∀ _solver : LowerBounds.SmallLocalCircuitSolver_Partial p, False) :
  ∀ _solver : SmallGeneralCircuitSolver_Partial p, False :=
  ThirdPartyFacts.no_general_solver_of_no_local_partial (p := p) H

end Magnification
end Pnp3
