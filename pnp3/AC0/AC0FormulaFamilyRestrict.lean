import AC0.AC0FormulaFamily
import AC0.AC0FormulaRestrict
import Core.BooleanBasics

/-!
  pnp3/AC0/AC0FormulaFamilyRestrict.lean

  Restriction-aware operations for families of AC0 formulas.
-/

namespace Pnp3
namespace AC0

open Core

namespace AC0FormulaFamily

/-- Apply a restriction to each formula in a family. -/
@[simp] def restrictFamily {d n : Nat} (ρ : Restriction n)
    (F : AC0FormulaFamily d n) : AC0FormulaFamily d n :=
  F.map (AC0Formula.restrictFormula ρ)

/-- Pointwise evaluation commutes with restriction via `override`. -/
lemma eval_restrictFamily_pointwise {d n : Nat} (ρ : Restriction n)
    (F : AC0FormulaFamily d n) (x : Core.BitVec n) :
    (AC0FormulaFamily.eval (restrictFamily (ρ := ρ) F)).map (fun g => g x)
      = (AC0FormulaFamily.eval F).map (fun g => g (ρ.override x)) := by
  classical
  unfold AC0FormulaFamily.eval restrictFamily
  -- map by map; use `eval_restrictFormula` pointwise.
  simp [AC0Formula.eval_restrictFormula]

end AC0FormulaFamily

end AC0
end Pnp3
