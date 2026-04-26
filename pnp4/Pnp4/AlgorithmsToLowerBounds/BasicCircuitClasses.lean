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

/-- One-bit input masking used by the coin-translation route. -/
def maskBit (keep x : Bool) : Bool :=
  keep && x

@[simp] theorem maskBit_true (x : Bool) :
    maskBit true x = x := by
  cases x <;> rfl

@[simp] theorem maskBit_false (x : Bool) :
    maskBit false x = false :=
  rfl

/--
Coordinatewise input masking.

`keep i = false` substitutes the `i`-th input by `0`; `keep i = true` keeps
the original input bit.
-/
def maskVec {n : Nat} (keep x : BitVec n) : BitVec n :=
  fun i => maskBit (keep i) (x i)

@[simp] theorem maskVec_apply
    {n : Nat} (keep x : BitVec n) (i : Fin n) :
    maskVec keep x i = maskBit (keep i) (x i) :=
  rfl

/--
Circuit classes closed under substituting arbitrary inputs by `0`.

This is the class/size side of the masking-translation argument: applying an
input mask to a circuit keeps the result in the same family and does not
increase size.
-/
structure ClosedUnderInputMasking (C : CircuitFamilyClass) where
  maskCircuit :
    ∀ {n : Nat}, BitVec n → C.Family n → C.Family n
  eval_maskCircuit :
    ∀ {n : Nat} (keep : BitVec n) (c : C.Family n) (x : BitVec n),
      C.eval (maskCircuit keep c) x = C.eval c (maskVec keep x)
  size_maskCircuit :
    ∀ {n : Nat} (keep : BitVec n) (c : C.Family n),
      C.size (maskCircuit keep c) ≤ C.size c

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
