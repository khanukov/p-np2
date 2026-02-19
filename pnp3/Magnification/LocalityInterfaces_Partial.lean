import Complexity.Promise
import Core.BooleanBasics
import Models.Model_PartialMCSP

/-!
  Partial MCSP analog of `Magnification.LocalityInterfaces`.

  We keep only numeric parameters (input length, size, depth) and a solver
  wrapper with correctness for the Partial MCSP promise.

  This file now also exposes a stricter "realized" wrapper where `decide`
  is connected to an explicit circuit implementation.  The current pipeline
  still accepts the lightweight wrappers, but new developments should prefer
  the realized form to avoid vacuous parameter-only reasoning.
-/

namespace Pnp3
namespace Magnification

open Models
open Complexity

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
  decide : Core.BitVec (Models.partialInputLen p) → Bool
  correct : SolvesPromise (Models.GapPartialMCSPPromise p) decide

/--
  Stronger semantic wrapper for a general solver.

  Besides promise-correctness, we require an explicit circuit implementation
  and a pointwise equality proof connecting `decide` with circuit evaluation.
-/
structure RealizedSmallGeneralCircuitSolver_Partial
    (p : Models.GapPartialMCSPParams) where
  base : SmallGeneralCircuitSolver_Partial p
  impl : Models.Circuit (Models.partialInputLen p)
  decide_eq_impl : ∀ x, base.decide x = Models.Circuit.eval impl x

@[simp] theorem realized_general_correct
    {p : Models.GapPartialMCSPParams}
    (solver : RealizedSmallGeneralCircuitSolver_Partial p) :
    SolvesPromise (Models.GapPartialMCSPPromise p) solver.base.decide :=
  solver.base.correct

end Magnification
end Pnp3
