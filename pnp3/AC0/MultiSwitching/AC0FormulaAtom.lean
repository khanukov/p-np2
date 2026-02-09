import AC0.AC0Formula
import AC0.MultiSwitching.IHInterface
import AC0.MultiSwitching.Atoms

/-!
  pnp3/AC0/MultiSwitching/AC0FormulaAtom.lean

  Atoms built from AC0 subformulas equipped with an IH deciding tree.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-- Atom as a subformula together with a deciding-tree witness. -/
structure AC0FormulaAtom (d n : Nat) where
  formula : AC0Formula n d
  witness : AtomTailWitness n
  witness_eval_eq : witness.eval = AC0Formula.eval n d formula

namespace AC0FormulaAtom

/-- Evaluate the atom as its underlying formula. -/
@[simp] def eval {d n : Nat} (A : AC0FormulaAtom d n) : Core.BitVec n → Bool :=
  A.witness.eval

/-- View an AC0FormulaAtom as a MultiSwitching Atom. -/
@[simp] def toAtom {d n : Nat} (A : AC0FormulaAtom d n) : Atom n :=
  A.witness.toAtom

@[simp] lemma eval_eq_formula_eval {d n : Nat} (A : AC0FormulaAtom d n) :
    A.eval = AC0Formula.eval n d A.formula := by
  simpa [AC0FormulaAtom.eval] using A.witness_eval_eq

end AC0FormulaAtom

end MultiSwitching
end AC0
end Pnp3
