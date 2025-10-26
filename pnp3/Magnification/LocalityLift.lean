import Mathlib.Data.Finset.Basic
import Core.BooleanBasics
import LowerBounds.AntiChecker
import Models.Model_GapMCSP
import Magnification.LocalityInterfaces
import ThirdPartyFacts.LocalityLift

/-!
  `Magnification.LocalityLift` is now a thin façade that delegates the heavy
  lifting to the stand-alone package located in `Facts/LocalityLift`.  The module
  keeps the historical notation used throughout the pipeline while importing the
  verified interfaces from the external package via
  `ThirdPartyFacts.LocalityLift`.
-/

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ThirdPartyFacts

/-- Convenience alias to the external locality-lift interface. -/
@[inline] def locality_lift
  {p : Models.GapMCSPParams}
  (solver : SmallGeneralCircuitSolver p) :
    ∃ (T : Finset (Core.BitVec (Models.inputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver p),
        T.card ≤ Models.polylogBudget (Models.inputLen p) ∧
        loc.params.M ≤ solver.params.size * (T.card.succ) ∧
        loc.params.ℓ ≤ Models.polylogBudget (Models.inputLen p) ∧
        loc.params.depth ≤ solver.params.depth :=
  ThirdPartyFacts.locality_lift (p := p) (solver := solver)

/-- Contrapositive wrapper delegating to the external package. -/
@[inline] def no_general_solver_of_no_local
  {p : Models.GapMCSPParams}
  (H : ∀ _solver : LowerBounds.SmallLocalCircuitSolver p, False) :
  ∀ _solver : SmallGeneralCircuitSolver p, False :=
  ThirdPartyFacts.no_general_solver_of_no_local (p := p) H

end Magnification
end Pnp3
