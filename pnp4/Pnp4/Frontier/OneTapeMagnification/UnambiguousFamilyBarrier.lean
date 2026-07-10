import Mathlib.Data.Bool.Basic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Abstract unambiguity is not enough

The Viola simulation of a deterministic one-tape computation is stronger than
an arbitrary union of branching programs: every accepted input has one
canonical accepting path transcript.  It is tempting to use only this
unambiguity when constructing a collective HSG.  The lemmas here record why
that abstraction loses all useful information.

Every Boolean predicate has a family of singleton components indexed by its
own input space.  On an accepted input exactly one component accepts, on a
rejected input none accepts, and existentially combining the components
recovers the original predicate.  Thus abstract disjointness or unambiguity
alone permits every predicate.  A successful CHMY improvement must retain the
additional coherence and uniform local-transition structure of canonical
one-tape path transcripts.

This module does not claim that the singleton components have the width,
locality, or machine-derived structure of the branching programs in the
Viola/CHMY simulation.
-/

/-- The component indexed by `index` accepts only its matching input, and only
when the ambient Boolean predicate accepts that input. -/
def singletonComponent {α : Type*} [DecidableEq α]
    (f : α → Bool) (index input : α) : Bool :=
  decide (index = input) && f input

theorem singletonComponent_eq_true_iff {α : Type*} [DecidableEq α]
    (f : α → Bool) (index input : α) :
    singletonComponent f index input = true ↔
      index = input ∧ f input = true := by
  simp [singletonComponent]

/-- Two different singleton components cannot accept the same input. -/
theorem singletonComponents_disjoint {α : Type*} [DecidableEq α]
    (f : α → Bool) {left right input : α}
    (hne : left ≠ right) :
    ¬ (singletonComponent f left input = true ∧
       singletonComponent f right input = true) := by
  rintro ⟨hLeft, hRight⟩
  apply hne
  calc
    left = input := (singletonComponent_eq_true_iff f left input).mp hLeft |>.1
    _ = right := ((singletonComponent_eq_true_iff f right input).mp hRight).1.symm

/-- Existentially combining all singleton components recovers the original
predicate exactly. -/
theorem exists_singletonComponent_eq_true_iff {α : Type*} [DecidableEq α]
    (f : α → Bool) (input : α) :
    (∃ index, singletonComponent f index input = true) ↔
      f input = true := by
  constructor
  · rintro ⟨index, hIndex⟩
    exact (singletonComponent_eq_true_iff f index input).mp hIndex |>.2
  · intro hInput
    exact ⟨input,
      (singletonComponent_eq_true_iff f input input).2 ⟨rfl, hInput⟩⟩

/-- On every accepted input the singleton decomposition is unambiguous: there
is exactly one accepting component. -/
theorem existsUnique_singletonComponent_iff {α : Type*} [DecidableEq α]
    (f : α → Bool) (input : α) :
    (∃ index,
      singletonComponent f index input = true ∧
      ∀ other, singletonComponent f other input = true → other = index) ↔
      f input = true := by
  constructor
  · rintro ⟨index, hIndex, _⟩
    exact (singletonComponent_eq_true_iff f index input).mp hIndex |>.2
  · intro hInput
    refine ⟨input, ?_, ?_⟩
    · exact (singletonComponent_eq_true_iff f input input).2 ⟨rfl, hInput⟩
    · intro index hIndex
      exact (singletonComponent_eq_true_iff f index input).mp hIndex |>.1

/-- On a rejected input every singleton component rejects. -/
theorem singletonComponent_eq_false_of_function_eq_false
    {α : Type*} [DecidableEq α]
    (f : α → Bool) (input : α) (hInput : f input = false) :
    ∀ index, singletonComponent f index input = false := by
  intro index
  simp [singletonComponent, hInput]

end OneTapeMagnification
end Frontier
end Pnp4
