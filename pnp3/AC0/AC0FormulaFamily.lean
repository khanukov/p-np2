import AC0.AC0Formula
import Core.SAL_Core

/-!
  pnp3/AC0/AC0FormulaFamily.lean

  Families of AC0 formulas (fixed depth), with evaluation and size helpers.
-/

namespace Pnp3
namespace AC0

open Core

/-- Family of AC0 formulas of fixed depth. -/
abbrev AC0FormulaFamily (d n : Nat) := List (AC0Formula n d)

namespace AC0FormulaFamily

/-- Evaluate a family of AC0 formulas into a family of Boolean functions. -/
@[simp] def eval {d n : Nat} (F : AC0FormulaFamily d n) : Family n :=
  F.map (fun f => AC0Formula.eval n d f)

/-- Total syntactic size of a family (sum of formula sizes). -/
@[simp] def size {d n : Nat} (F : AC0FormulaFamily d n) : Nat :=
  (F.map AC0Formula.size).sum

@[simp] lemma size_nil {d n : Nat} : size (d := d) (n := n) [] = 0 := by
  rfl

@[simp] lemma size_cons {d n : Nat} (f : AC0Formula n d) (fs : AC0FormulaFamily d n) :
    size (d := d) (n := n) (f :: fs) = AC0Formula.size f + size fs := by
  rfl

@[simp] lemma eval_nil {d n : Nat} : eval (d := d) (n := n) [] = [] := by
  rfl

@[simp] lemma eval_cons {d n : Nat} (f : AC0Formula n d) (fs : AC0FormulaFamily d n) :
    eval (d := d) (n := n) (f :: fs) = AC0Formula.eval n d f :: eval fs := by
  rfl

end AC0FormulaFamily

end AC0
end Pnp3
