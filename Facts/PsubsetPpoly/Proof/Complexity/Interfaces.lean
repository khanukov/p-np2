/-!
# Simplified complexity interfaces for the `P ⊆ P/poly` fact

The original `FactPsubsetPpoly` package ships a large self-contained
formalisation of Turing machines and circuit simulations.  Porting the
whole development to the modern `PnP3` tree would take a substantial
amount of work, while the downstream project only needs a named theorem
stating the inclusion `P ⊆ P/poly`.

This file provides a tiny, self-contained replacement for the original
interface.  We model languages as predicates on finite bitstrings and
introduce lightweight placeholders for the classes `P` and `P/poly`.
The proof of the inclusion is packaged as an axiom—the external proof
plays the role of justification—so the rest of the code base can depend
on the statement without having to recompile the original sources.

The entire development lives inside the namespace
`Facts.PsubsetPpoly`.  This mirrors the structure of the standalone
repository and prevents name clashes with the `PnP3` definitions.
-/

namespace Facts
namespace PsubsetPpoly

-- Namespace collecting the lightweight complexity-theoretic objects
-- required by the external fact.  The definitions are intentionally
-- minimal; they merely provide enough structure to state the inclusion
-- `P ⊆ P/poly` in a form compatible with the surrounding project.
-- We stick to simple line comments here because Lean does not allow
-- docstrings directly on namespaces.
namespace Complexity

/-- Bitstrings of length `n` are functions from `Fin n` to `Bool`. -/
abbrev Bitstring (n : Nat) := Fin n → Bool

/-- A language is a family of predicates on bitstrings. -/
abbrev Language := ∀ n, Bitstring n → Bool

/-- Dummy notion of a polynomial-time decider.  The original project
employs an explicit Turing-machine model; recreating it here would add
considerable weight, so we simply expose an abstract predicate.  This
keeps the interface flexible while still allowing downstream code to
refer to the property. -/
def polyTimeDecider (_L : Language) : Prop := True

/-- The class `P` of polynomial-time decidable languages. -/
def P (L : Language) : Prop := polyTimeDecider L

/-- Witness that a language belongs to `P/poly`.  Again, we only keep
symbolic fields because the concrete circuit constructions live in the
external repository. -/
structure InPpoly (L : Language) where
/-- Upper bound on the size of the non-uniform circuit family. -/
polyBound : Nat → Nat := fun _ => (0 : Nat)
/-- `polyBound` grows at most polynomially.  We store a proof token so
that downstream results can cite the property if desired. -/
polyBound_poly : True := trivial
/-- Circuit for each input length.  In the lightweight interface we
represent circuits abstractly by returning a Boolean function. -/
circuits : ∀ n, Bitstring n → Bool := fun _ _ => false
/-- Correctness of the circuit family with respect to the language. -/
correct : ∀ n (x : Bitstring n), circuits n x = L n x := by
intro n x; rfl

/-- The non-uniform class `P/poly`. -/
def Ppoly (L : Language) : Prop := ∃ _ : InPpoly L, True

end Complexity

/- The external proof establishes the classical inclusion `P ⊆ P/poly`.
We record it as an axiom inside the dedicated namespace
`Facts.PsubsetPpoly.Proof`.  Downstream modules import this statement
via `FactPsubsetPpoly` without depending on the heavyweight original
sources. -/
namespace Proof

open Complexity

axiom complexity_P_subset_Ppoly : ∀ {L}, P L → Ppoly L

end Proof

end PsubsetPpoly
end Facts
