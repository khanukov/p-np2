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

/-- Parameters of a general (non-local) GapMCSP solver. -/
structure GeneralCircuitParameters where
  n     : Nat
  size  : Nat
  depth : Nat
  deriving Repr

/-- Wrapper expressing the existence of a small general solver. -/
structure SmallGeneralCircuitSolver (p : Models.GapMCSPParams) where
  params : GeneralCircuitParameters
  same_n : params.n = Models.inputLen p
  deriving Repr

end Magnification
end Pnp3
