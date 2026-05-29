import Complexity.PsubsetPpolyInternal.Bitstring
import Complexity.PsubsetPpolyInternal.TuringEncoding

universe u

/-!
# Complexity interfaces for the `P ⊆ P/poly` fact

This file exposes the minimal, *constructive* core needed to *state* the
`P ⊆ P/poly` fact: a meaningful definition of `P` based on a polynomial-time
Turing machine (`polyTimeDecider`).

The canonical non-uniform class is **not** defined here.  It is `PpolyDAG`
(genuine acyclic Boolean circuits with a real size measure) in
`Complexity/Interfaces.lean`, and the genuine machine-checked inclusion
`P ⊆ PpolyDAG` is `Complexity.Simulation.proved_P_subset_PpolyDAG_internal`
(`Complexity/Simulation/Circuit_Compiler.lean`).

A previous *degenerate* lightweight interface (`InPpoly`, `Ppoly`,
`InPpolyStructured`, `PpolyStructured`, and the vacuous
`complexity_P_subset_Ppoly`, in which a "circuit" was an arbitrary Boolean
function with no size measure) used to live in this file.  It was unused by the
proof and was archived to
`archive/pnp3/Complexity/PsubsetPpolyInternal_Lightweight_Ppoly.lean`
to remove the two-competing-`P/poly`-notations confusion from the active tree.

The development lives inside the namespace `Pnp3.Internal.PsubsetPpoly`, which
prevents name clashes with the `PnP3` definitions.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly

-- Namespace collecting the lightweight complexity-theoretic objects
-- required by the external fact.  The definitions are intentionally
-- minimal; they merely provide enough structure to state the inclusion
-- `P ⊆ P/poly` in a form compatible with the surrounding project.
-- We stick to simple line comments here because Lean does not allow
-- docstrings directly on namespaces.
namespace Complexity

open Boolcube
open TM

/-- Bitstrings of length `n` are Boolean vectors from the standalone package. -/
abbrev Bitstring (n : Nat) := Boolcube.Bitstring n

/-- A language is a family of predicates on bitstrings. -/
abbrev Language := ∀ n, Bitstring n → Bool

/--
Polynomial-time decidability for a language `L`: there exists a deterministic
one-tape Turing machine that decides `L` within a polynomial time bound
`n ↦ n^c + c`.
-/
def polyTimeDecider (L : Language) : Prop :=
  ∃ (M : TM.{u}) (c : ℕ),
    (∀ n, M.runTime n ≤ n ^ c + c) ∧
    (∀ n (x : Bitstring n), TM.accepts (M := M) (n := n) x = L n x)

/-- The class `P` of polynomial-time decidable languages. -/
def P (L : Language) : Prop := polyTimeDecider.{u} L

end Complexity

end PsubsetPpoly
end Internal
end Pnp3
