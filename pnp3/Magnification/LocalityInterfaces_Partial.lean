import Mathlib.Data.Finset.Basic
import Complexity.Promise
import Complexity.Interfaces
import Core.BooleanBasics
import Models.Model_PartialMCSP

/-!
  Partial MCSP analog of `Magnification.LocalityInterfaces`.

  We keep only numeric parameters (input length, size, depth) and a solver
  wrapper with correctness for the Partial MCSP promise.

  This wrapper intentionally stores only global-solver data
  (input length/size/depth + correctness).  Any locality information must be
  provided separately by a locality-lift witness, not baked into the solver.
-/

namespace Pnp3
namespace Magnification

open Models
open Complexity
open ComplexityInterfaces

structure GeneralCircuitParametersPartial where
  n     : Nat
  size  : Nat
  depth : Nat
  deriving Repr

structure SmallGeneralCircuitParamsPartial (p : Models.GapPartialMCSPParams) where
  params : GeneralCircuitParametersPartial
  same_n : params.n = Models.partialInputLen p
  deriving Repr

structure SmallGeneralCircuitSolver_Partial (p : Models.GapPartialMCSPParams) where
  params : SmallGeneralCircuitParamsPartial p
  sem : ComplexityInterfaces.SemanticDecider (Models.partialInputLen p)
  witness : sem.Carrier
  correct : SolvesPromise (Models.GapPartialMCSPPromise p) (fun x => sem.eval witness x)

/-- Evaluator induced by the semantic witness of a general solver. -/
@[simp] def SmallGeneralCircuitSolver_Partial.decide
    {p : Models.GapPartialMCSPParams}
    (solver : SmallGeneralCircuitSolver_Partial p) :
    Core.BitVec (Models.partialInputLen p) → Bool :=
  fun x => solver.sem.eval solver.witness x

/-- Convenience view of `correct` through `solver.decide`. -/
lemma SmallGeneralCircuitSolver_Partial.correct_decide
    {p : Models.GapPartialMCSPParams}
    (solver : SmallGeneralCircuitSolver_Partial p) :
    SolvesPromise (Models.GapPartialMCSPPromise p) solver.decide := by
  simpa [SmallGeneralCircuitSolver_Partial.decide] using solver.correct

end Magnification
end Pnp3
