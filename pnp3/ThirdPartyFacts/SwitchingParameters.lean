import Core.BooleanBasics

/-!
  Shared parameter records for switching and shrinkage statements.  The goal is
  to centralise the bookkeeping types so that both the axiomatisation of the
  multi-switching lemma and its eventual constructive proof can reuse exactly
  the same definitions.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core

/-- Parameters describing the size and depth of an AC⁰ formula. -/
structure AC0Parameters where
  /-- Number of input bits. -/
  n : Nat
  /-- Formula size (e.g. gate count or leaf count). -/
  M : Nat
  /-- Depth of the formula. -/
  d : Nat
  deriving Repr

/-- Parameters for the class of local circuits used in the SAL pipeline. -/
structure LocalCircuitParameters where
  /-- Number of input bits. -/
  n      : Nat
  /-- Overall circuit size. -/
  M      : Nat
  /-- Locality parameter bounding the fan-in of each output. -/
  ℓ      : Nat
  /-- Circuit depth. -/
  depth  : Nat
  deriving Repr

/--
  Helper structure storing the quantitative bounds delivered by shrinkage
  results.  The fields are intentionally lightweight so that later modules can
  plug in explicit polylogarithmic formulas.
-/
structure ShrinkageBounds where
  depthBound : Nat
  errorBound : Q
  deriving Repr

end ThirdPartyFacts
end Pnp3
