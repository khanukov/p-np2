import Mathlib.Data.Finset.Basic
import Complexity.Promise
import Core.BooleanBasics
import Models.Model_PartialMCSP

/-!
  Partial MCSP analog of `Magnification.LocalityInterfaces`.

  We keep only numeric parameters (input length, size, depth) and a solver
  wrapper with correctness for the Partial MCSP promise.

  The `decideLocal` field witnesses that the decision function depends on
  at most `partialInputLen p / 4` of its input coordinates.  This locality
  proof is provided by the axiom `ppoly_circuit_locality` when the solver
  is constructed from a P/poly hypothesis, and is preserved by the locality
  lift.
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
  decideLocal : ∃ (alive : Finset (Fin (Models.partialInputLen p))),
    alive.card ≤ Models.partialInputLen p / 4 ∧
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ alive, x i = y i) → decide x = decide y

end Magnification
end Pnp3
