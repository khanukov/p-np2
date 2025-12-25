import Complexity.Promise
import Core.BooleanBasics
import Models.Model_GapMCSP

/-!
  Minimal wrappers describing hypothetical GapMCSP solvers.  The structures are
  intentionally light-weight: only numeric parameters (input length, size, depth)
  are recorded so that they can be transported to the external locality-lift
  package without depending on concrete circuit encodings.
-/

namespace Pnp3
namespace Magnification

open Models
open Complexity

/-- Parameters of a general (non-local) GapMCSP solver. -/
structure GeneralCircuitParameters where
  n     : Nat
  size  : Nat
  depth : Nat
  deriving Repr

/-- Параметры «малого» общего решателя GapMCSP. -/
structure SmallGeneralCircuitParams (p : Models.GapMCSPParams) where
  params : GeneralCircuitParameters
  same_n : params.n = Models.inputLen p
  deriving Repr

/-- Корректный общий решатель GapMCSP. -/
structure SmallGeneralCircuitSolver (p : Models.GapMCSPParams) where
  params : SmallGeneralCircuitParams p
  decide : Core.BitVec (Models.inputLen p) → Bool
  correct : SolvesPromise (Models.GapMCSPPromise p) decide

end Magnification
end Pnp3
