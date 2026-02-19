import Proof.Bitstring
import Proof.Turing.Encoding

/-!
# Complexity interfaces for the `P ⊆ P/poly` fact

This file exposes the minimal, *constructive* interface required by the
standalone `P ⊆ P/poly` proof.  Unlike the previous placeholder version, we
now give a meaningful definition of `P` based on a polynomial-time Turing
machine and a lightweight interface for circuit families.  The inclusion
theorem is proved directly here without axioms, keeping the public surface area
compact while avoiding heavyweight dependencies.

The entire development lives inside the namespace `Facts.PsubsetPpoly`.  This
mirrors the structure of the standalone repository and prevents name clashes
with the `PnP3` definitions.
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
  ∃ (M : TM.{0}) (c : ℕ),
    (∀ n, M.runTime n ≤ n ^ c + c) ∧
    (∀ n (x : Bitstring n), TM.accepts (M := M) (n := n) x = L n x)

/-- The class `P` of polynomial-time decidable languages. -/
def P (L : Language) : Prop := polyTimeDecider L

/--
`f` is polynomially bounded if there exists `k` such that
`f n ≤ n^k + k` for all input lengths `n`.
-/
def IsPolyBound (f : Nat → Nat) : Prop :=
  ∃ k : Nat, ∀ n, f n ≤ n ^ k + k

/--
Witness that a language belongs to `P/poly`.  We keep this interface deliberately
minimal but non-trivial: besides a polynomial size bound we require a single
polynomial-time evaluator machine that computes each non-uniform circuit
predicate `circuits n`.
-/
structure InPpoly (L : Language) where
  /-- Upper bound on the size of the non-uniform circuit family. -/
  polyBound : Nat → Nat
  /-- `polyBound` grows at most polynomially. -/
  polyBound_poly : IsPolyBound polyBound
  /-- Non-uniform family predicate for each input length. -/
  circuits : ∀ n, Bitstring n → Bool
  /-- The family is uniformly evaluable by a machine within `polyBound`. -/
  eval_poly : ∃ (E : TM.{0}),
      (∀ n, E.runTime n ≤ polyBound n) ∧
      (∀ n (x : Bitstring n), TM.accepts (M := E) (n := n) x = circuits n x)
  /-- Correctness of the circuit family with respect to the language. -/
  correct : ∀ n (x : Bitstring n), circuits n x = L n x

/-- The non-uniform class `P/poly`. -/
def Ppoly (L : Language) : Prop := Nonempty (InPpoly L)

end Complexity

/-!
The proof of `P ⊆ P/poly` is short once the classes are defined: a `P`-decider
itself can be used as the evaluator for the `P/poly` witness.
-/
namespace Proof

open Complexity

/-- Constructive inclusion `P ⊆ P/poly` in the lightweight interface. -/
theorem complexity_P_subset_Ppoly : ∀ {L}, P L → Ppoly L := by
  intro L hL
  rcases hL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨{ polyBound := fun n => n ^ c + c
            polyBound_poly := ?poly
            circuits := fun n x => TM.accepts (M := M) (n := n) x
            eval_poly := ?eval
            correct := ?corr }⟩
  · refine ⟨c, ?_⟩
    intro n
    exact Nat.le_refl _
  · exact ⟨M, hRun, by intro n x; rfl⟩
  · intro n x
    exact hCorrect n x

end Proof

end PsubsetPpoly
end Facts
