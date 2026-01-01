import Complexity.Promise
import Core.BooleanBasics
import Models.Model_PartialMCSP

/-!
  Partial MCSP analog of `Magnification.LocalityInterfaces`.

  We keep only numeric parameters (input length, size, depth) and a solver
  wrapper with correctness for the Partial MCSP promise.
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

end Magnification
end Pnp3
