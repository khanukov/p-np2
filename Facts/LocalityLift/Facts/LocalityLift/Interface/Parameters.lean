import Mathlib.Data.Nat.Log

/-!
# Basic parameter records for the locality-lift interface

This module fixes the light-weight structures shared between the stand-alone
`Facts/LocalityLift` package and the `pnp3` pipeline.  Only the *numeric*
parameters of hypothetical GapMCSP solvers are recorded here; the concrete
encoding of circuits is irrelevant for the locality-lift theorem.
-/

namespace Facts
namespace LocalityLift

/-- Boolean vectors of length `n`.  We keep the alias explicit to avoid pulling
in the whole `pnp3` core just for this type. -/
abbrev BitVec (n : Nat) := Fin n → Bool

/-- Parameters of the GapMCSP instance under consideration. -/
structure GapMCSPParams where
  /-- Number of input bits. -/
  n : Nat
  deriving Repr

/-- Truth-table length `N = 2^n` for a GapMCSP instance. -/
def inputLen (p : GapMCSPParams) : Nat := Nat.pow 2 p.n

/--
Polylogarithmic budget shared across Step C/Step D.  The exponent `4` is fixed to
match the conventions already used in the main repository.
-/
def polylogBudget (N : Nat) : Nat := (Nat.log2 (N + 1) + 1) ^ 4

/-- Numeric parameters of a general (non-local) GapMCSP solver. -/
structure GeneralCircuitParameters where
  /-- Number of input bits seen by the solver. -/
  n : Nat
  /-- Total size (number of gates) of the circuit. -/
  size : Nat
  /-- Circuit depth. -/
  depth : Nat
  deriving Repr

/-- Wrapper asserting the existence of a small general solver. -/
structure SmallGeneralCircuitSolver (p : GapMCSPParams) where
  /-- Concrete parameters of the solver. -/
  params : GeneralCircuitParameters
  /-- The solver operates on the same truth-table length as the instance. -/
  same_n : params.n = inputLen p
  deriving Repr

/-- Numeric parameters of a local GapMCSP solver. -/
structure LocalCircuitParameters where
  /-- Number of input bits seen by the solver. -/
  n : Nat
  /-- Size of the circuit. -/
  M : Nat
  /-- Locality bound (number of input bits inspected by each gate). -/
  ℓ : Nat
  /-- Circuit depth. -/
  depth : Nat
  deriving Repr

/--
Smallness predicate for local solvers.

We require that the effective trunk bound appearing in shrinkage estimates
is at most half of the input length.  This numeric assumption is the same as
in the main `pnp3` pipeline and is strong enough to drive the local
anti-checker contradiction.
-/
def LocalCircuitSmallEnough (params : LocalCircuitParameters) : Prop :=
  params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ≤ params.n / 2

/-- Wrapper asserting the existence of a small local solver. -/
structure SmallLocalCircuitSolver (p : GapMCSPParams) where
  /-- Concrete parameters of the local solver. -/
  params : LocalCircuitParameters
  /-- The local solver shares the truth-table length with the instance. -/
  same_n : params.n = inputLen p
  /-- The numeric smallness condition for locality-based anti-checkers. -/
  small : LocalCircuitSmallEnough params
  deriving Repr

end LocalityLift
end Facts
