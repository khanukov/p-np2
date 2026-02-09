import AC0.AC0FormulaFamilyRestrict

/-!
  pnp3/AC0/AC0FormulaResidual.lean

  Residualization for AC0 formulas under restrictions.
  At this stage, residualization is defined as syntactic restriction
  (via `restrictFormula`), which preserves depth but fixes variables
  through `Restriction.override`. This is the stable foundation for
  depth-induction; depth reduction will be handled by the switching
  step (CCDT) rather than by this definition.
-/-

namespace Pnp3
namespace AC0

open Core

namespace AC0Formula

/-- Residual of an AC0 formula under a restriction (syntax-level). -/
@[simp] def residual {n d : Nat} (ρ : Restriction n) (F : AC0Formula n d) : AC0Formula n d :=
  restrictFormula ρ F

@[simp] lemma eval_residual {n d : Nat} (ρ : Restriction n)
    (F : AC0Formula n d) (x : Core.BitVec n) :
    AC0Formula.eval (residual (ρ := ρ) F) x =
      AC0Formula.eval F (ρ.override x) := by
  simp [residual, AC0Formula.eval_restrictFormula]

end AC0Formula

namespace AC0FormulaFamily

/-- Residual of an AC0 formula family under a restriction. -/
@[simp] def residual {n d : Nat} (ρ : Restriction n)
    (F : AC0FormulaFamily d n) : AC0FormulaFamily d n :=
  restrictFamily (ρ := ρ) F

@[simp] lemma eval_residual_pointwise {n d : Nat} (ρ : Restriction n)
    (F : AC0FormulaFamily d n) (x : Core.BitVec n) :
    (AC0FormulaFamily.eval (residual (ρ := ρ) F)).map (fun g => g x)
      = (AC0FormulaFamily.eval F).map (fun g => g (ρ.override x)) := by
  simpa [residual] using
    (AC0FormulaFamily.eval_restrictFamily_pointwise (ρ := ρ) (F := F) (x := x))

end AC0FormulaFamily

end AC0
end Pnp3
