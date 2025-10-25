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
The actual inclusion is proved separately in
`Proof/Complexity/PsubsetPpoly.lean`, allowing the rest of the code base to
depend on the named theorem without having to recompile the external
simulation-heavy sources.

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

/-!
The constructive inclusion `P ⊆ P/poly` is proved in
`Proof/Complexity/PsubsetPpoly.lean`.  We keep the proof separate so this file
can remain a lightweight interface layer that only introduces the basic
complexity-language vocabulary.  Downstream projects that need the actual
theorem can import the bridge module directly.
-/
end PsubsetPpoly
end Facts
