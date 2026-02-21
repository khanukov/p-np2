import Core.BooleanBasics
import AC0.AC0FormulaFamily

/-!
  pnp3/AC0/AC0FormulaWitness.lean

  Witness for AC0 families via explicit AC0 formulas of fixed depth.
  This is the interface used by depth-induction for polylog bounds.
-/

namespace Pnp3
namespace AC0

open Core

/-!
### Witness for AC0 formulas (fixed depth)

We keep this separate from the existing `AC0FamilyWitness` (depth-2 DNF),
so downstream code remains untouched while depth-induction is built on top
of a uniform AC0 syntax.
-/

structure AC0FormulaWitness (d n : Nat) (M : Nat) (F : Family n) where
  /-- Concrete AC0 formulas of depth `d`. -/
  formulas : AC0FormulaFamily d n
  /-- Semantics coincide with the target family. -/
  family_eq : AC0FormulaFamily.eval formulas = F
  /-- Total syntactic size bound. -/
  size_le : AC0FormulaFamily.size formulas ≤ M

/-- Existence of an AC0 formula witness at fixed depth and size bound. -/
def FamilyIsAC0Formula (d n : Nat) (M : Nat) (F : Family n) : Prop :=
  Nonempty (AC0FormulaWitness d n M F)

end AC0
end Pnp3
