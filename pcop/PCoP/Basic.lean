/-!
# Basic definitions: bit strings, languages, complement

This file is dependency-free (Lean core only).

A *language* is, for every input length `n`, a Boolean predicate on bit
strings of length `n`.  Using `Bool` (rather than `Prop`) makes the
complement a total, purely syntactic operation `x ↦ !(L n x)` — no
decidability side conditions are needed anywhere in the development.
-/

namespace PCoP

/-- A bit string of length `n`. -/
def Bitstring (n : Nat) : Type := Fin n → Bool

/-- A language: one Boolean predicate per input length. -/
def Language : Type := (n : Nat) → Bitstring n → Bool

namespace Language

/-- The complement language: pointwise Boolean negation. -/
def complement (L : Language) : Language := fun n x => !(L n x)

@[simp] theorem complement_apply (L : Language) (n : Nat) (x : Bitstring n) :
    L.complement n x = !(L n x) := rfl

/-- Complement is an involution. -/
@[simp] theorem complement_complement (L : Language) :
    L.complement.complement = L := by
  funext n x
  simp [complement]

end Language

end PCoP
