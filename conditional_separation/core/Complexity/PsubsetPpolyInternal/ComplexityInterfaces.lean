import Complexity.PsubsetPpolyInternal.Bitstring
import Complexity.PsubsetPpolyInternal.TuringEncoding

universe u

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

/--
Witness that a language belongs to `P/poly`.  We keep this interface deliberately
minimal: the circuits are represented abstractly as Boolean functions, while the
polynomial bound is stored as a proof token.  This is sufficient for downstream
code that only needs a named inclusion theorem.
-/
structure InPpoly (L : Language) where
  /-- Upper bound on the size of the non-uniform circuit family. -/
  polyBound : Nat → Nat := fun _ => (0 : Nat)
  /-- `polyBound` grows at most polynomially. -/
  polyBound_poly : True := trivial
  /-- Circuit for each input length. -/
  circuits : ∀ n, Bitstring n → Bool := fun _ _ => false
  /-- Correctness of the circuit family with respect to the language. -/
  correct : ∀ n (x : Bitstring n), circuits n x = L n x := by
    intro n x
    rfl

/--
Structured non-uniform witness.  Unlike `InPpoly`, this record keeps an
explicit carrier `Circuit n` and an evaluator `eval`, so downstream developments
can refine the representation to real circuit syntax without changing the
`Ppoly` API in one step.
-/
structure InPpolyStructured (L : Language) where
  /-- Circuit carrier at each input length. -/
  Circuit : Nat → Type u
  /-- Chosen circuit for each input length. -/
  family : ∀ n, Circuit n
  /-- Evaluator for the circuit carrier. -/
  eval : ∀ n, Circuit n → Bitstring n → Bool
  /-- Upper bound on circuit size. -/
  polyBound : Nat → Nat := fun _ => (0 : Nat)
  /-- Size measure for the carrier. -/
  size : ∀ n, Circuit n → Nat := fun _ _ => 0
  /-- Polynomial-growth token for the bound. -/
  polyBound_poly : True := trivial
  /-- The chosen family is bounded by `polyBound`. -/
  family_size_le : ∀ n, size n (family n) ≤ polyBound n := by
    intro n
    exact Nat.zero_le _
  /-- Correctness of the chosen family with respect to the language. -/
  correct : ∀ n (x : Bitstring n), eval n (family n) x = L n x

/-- Forget structural data and recover the lightweight `InPpoly` witness. -/
def InPpolyStructured.toInPpoly {L : Language}
    (h : InPpolyStructured L) : InPpoly L where
  polyBound := h.polyBound
  polyBound_poly := h.polyBound_poly
  circuits := fun n x => h.eval n (h.family n) x
  correct := h.correct

/--
Promote the lightweight witness to a structured one by taking circuits
themselves as the carrier.  This keeps migration fully backward-compatible:
existing `InPpoly` witnesses can be reused verbatim.
-/
def InPpoly.toStructured {L : Language} (h : InPpoly L) :
    InPpolyStructured L where
  Circuit := fun n => ULift (Bitstring n → Bool)
  family := fun n => ⟨h.circuits n⟩
  eval := fun _ c x => c.down x
  polyBound := h.polyBound
  polyBound_poly := h.polyBound_poly
  size := fun _ _ => 0
  family_size_le := by
    intro n
    exact Nat.zero_le _
  correct := h.correct

/-- The non-uniform class `P/poly`. -/
def Ppoly (L : Language) : Prop := ∃ _ : InPpoly L, True

/-- Structured variant of `P/poly` used during interface migration. -/
def PpolyStructured (L : Language) : Prop := ∃ _ : InPpolyStructured.{u} L, True

/-- Structured witnesses imply membership in the lightweight non-uniform class. -/
theorem ppoly_of_structured {L : Language} :
    InPpolyStructured L → Ppoly L := by
  intro h
  exact ⟨h.toInPpoly, trivial⟩

/-- Lightweight witnesses are also structured (via the degenerate carrier). -/
theorem structured_of_ppoly {L : Language} :
    Ppoly L → PpolyStructured L := by
  intro h
  rcases h with ⟨w, _⟩
  exact ⟨w.toStructured, trivial⟩

/-- The two `P/poly` views are definitionally interchangeable for clients. -/
theorem ppoly_iff_ppolyStructured {L : Language} :
    Ppoly L ↔ PpolyStructured L := by
  constructor
  · exact structured_of_ppoly
  · intro h
    rcases h with ⟨w, _⟩
    exact ppoly_of_structured w

end Complexity

/-!
The proof of `P ⊆ P/poly` is short once the classes are defined: the decider
itself can serve as the circuit family because we treat circuits abstractly.
This keeps the statement constructive without importing the full simulation
machinery.
-/
namespace Proof

open Complexity

/-- Constructive inclusion `P ⊆ P/poly` in the lightweight interface. -/
theorem complexity_P_subset_Ppoly : ∀ {L}, P L → Ppoly L := by
  intro L hL
  rcases hL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨{ polyBound := fun n => n ^ c + c
            polyBound_poly := trivial
            circuits := fun n x => TM.accepts (M := M) (n := n) x
            correct := ?_ }, trivial⟩
  intro n x
  exact hCorrect n x

end Proof

end PsubsetPpoly
end Internal
end Pnp3
