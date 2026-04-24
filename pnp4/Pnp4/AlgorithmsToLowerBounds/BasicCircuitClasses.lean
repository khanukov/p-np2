import Core.BooleanBasics

universe u

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Local bit-vector language used by the algorithms-to-lower-bounds track.

This stays independent from the `pnp3` `ComplexityInterfaces.Language` surface
until the final bridge module.
-/
abbrev BitVec (n : Nat) := Pnp3.Core.BitVec n

/-- A Boolean language over fixed-length bit-vectors. -/
abbrev BitVecLanguage := ∀ n : Nat, BitVec n → Bool

/--
Minimal non-uniform circuit-class interface for the new `pnp4` track.

This is intentionally neutral: no depth, modulus, DAG, or SAT-specific data
appears here.
-/
structure CircuitFamilyClass where
  Family : Nat → Type u
  eval : ∀ {n : Nat}, Family n → BitVec n → Bool
  size : ∀ {n : Nat}, Family n → Nat

/--
The class `C` computes the language `L` non-uniformly if every input length has
some witness circuit computing the corresponding slice.
-/
def NonuniformComputes
    (C : CircuitFamilyClass)
    (L : BitVecLanguage) : Prop :=
  ∀ n : Nat, ∃ c : C.Family n, ∀ x : BitVec n, C.eval c x = L n x

/--
Pointwise lower-bound surface: every exact circuit for `L` at input length `n`
must have size at least `lower n`.
-/
def SizeLowerBound
    (C : CircuitFamilyClass)
    (L : BitVecLanguage)
    (lower : Nat → Nat) : Prop :=
  ∀ n : Nat, ∀ c : C.Family n,
    (∀ x : BitVec n, C.eval c x = L n x) →
      lower n ≤ C.size c

/-- The language `L` is not in the non-uniform class `C`. -/
def NotInClass
    (C : CircuitFamilyClass)
    (L : BitVecLanguage) : Prop :=
  ¬ NonuniformComputes C L

end AlgorithmsToLowerBounds
end Pnp4
