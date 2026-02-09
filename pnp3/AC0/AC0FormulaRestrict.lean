import Core.BooleanBasics
import AC0.AC0Formula
import Mathlib.Order.WellFounded

/-!
  pnp3/AC0/AC0FormulaRestrict.lean

  Restriction-aware operations for AC0 formulas.
  These utilities are a lightweight foundation for depth induction:
  we can push a restriction through a formula and reason about evaluation
  via `Restriction.override`.
-/

namespace Pnp3
namespace AC0

open Core

namespace AC0Formula

/-- Apply a restriction to an AC0 formula by overriding inputs. -/
def restrictFormula {n d : Nat} (ρ : Restriction n) : AC0Formula n d → AC0Formula n d
  | AC0Formula.atom f => AC0Formula.atom (fun x => f (ρ.override x))
  | AC0Formula.and fs => AC0Formula.and (AC0FormulaList.map (restrictFormula ρ) fs)
  | AC0Formula.or fs  => AC0Formula.or  (AC0FormulaList.map (restrictFormula ρ) fs)

@[simp] def restrictEvalArg {n : Nat} (ρ : Restriction n) : AC0Formula.EvalArg n → AC0Formula.EvalArg n
  | AC0Formula.EvalArg.form f => AC0Formula.EvalArg.form (restrictFormula ρ f)
  | AC0Formula.EvalArg.allC fs => AC0Formula.EvalArg.allC (AC0FormulaList.map (restrictFormula ρ) fs)
  | AC0Formula.EvalArg.anyC fs => AC0Formula.EvalArg.anyC (AC0FormulaList.map (restrictFormula ρ) fs)

def evalMeasureWF (n : Nat) :
    WellFounded (fun b a : AC0Formula.EvalArg n => AC0Formula.evalMeasure n b < AC0Formula.evalMeasure n a) :=
  InvImage.wf (fun a => AC0Formula.evalMeasure n a) (Nat.lt_wfRel).wf

@[simp] lemma restrictFormula_atom {n : Nat} (ρ : Restriction n)
    (f : Core.BitVec n → Bool) :
    restrictFormula (n := n) (d := 0) ρ (AC0Formula.atom f)
      = AC0Formula.atom (fun x => f (ρ.override x)) := by
  rfl

@[simp] lemma restrictFormula_and {n d : Nat} (ρ : Restriction n)
    (fs : AC0FormulaList n d) :
    restrictFormula (n := n) (d := Nat.succ d) ρ (AC0Formula.and fs)
      = AC0Formula.and (AC0FormulaList.map (restrictFormula ρ) fs) := by
  rfl

@[simp] lemma restrictFormula_or {n d : Nat} (ρ : Restriction n)
    (fs : AC0FormulaList n d) :
    restrictFormula (n := n) (d := Nat.succ d) ρ (AC0Formula.or fs)
      = AC0Formula.or (AC0FormulaList.map (restrictFormula ρ) fs) := by
  rfl

/-! Evaluation commutes with restriction (via WF recursion on EvalArg). -/

theorem evalCore_restrict_arg {n : Nat} (ρ : Restriction n) :
    ∀ a : AC0Formula.EvalArg n, ∀ x : Core.BitVec n,
      AC0Formula.evalCore n (restrictEvalArg (n := n) ρ a) x =
        AC0Formula.evalCore n a (ρ.override x) := by
  classical
  let wf := evalMeasureWF (n := n)
  refine wf.fix (C := fun a =>
      ∀ x : Core.BitVec n,
        AC0Formula.evalCore n (restrictEvalArg (n := n) ρ a) x =
          AC0Formula.evalCore n a (ρ.override x)) (fun a rec => ?_)
  · intro x
    cases a with
    | form f =>
        cases f with
        | atom g =>
            simp [restrictEvalArg, restrictFormula, AC0Formula.evalCore]
        | and fs =>
            have h := rec (.allC fs) (by
              simpa using (AC0Formula.evalMeasure_all_lt_form_and n _ fs)) x
            simpa [restrictEvalArg, restrictFormula, AC0Formula.evalCore] using h
        | or fs =>
            have h := rec (.anyC fs) (by
              simpa using (AC0Formula.evalMeasure_any_lt_form_or n _ fs)) x
            simpa [restrictEvalArg, restrictFormula, AC0Formula.evalCore] using h
    | allC fs =>
        cases fs with
        | nil =>
            simp [restrictEvalArg, AC0Formula.evalCore]
        | cons f fs =>
            have h1 := rec (.form f) (by
              simpa using (AC0Formula.evalMeasure_form_lt_all_cons n _ f fs)) x
            have h2 := rec (.allC fs) (by
              simpa using (AC0Formula.evalMeasure_all_lt_all_cons n _ f fs)) x
            have h1' : AC0Formula.evalCore n (AC0Formula.EvalArg.form (restrictFormula ρ f)) x =
                AC0Formula.evalCore n (AC0Formula.EvalArg.form f) (ρ.override x) := by
              simpa [restrictEvalArg] using h1
            have h2' : AC0Formula.evalCore n (AC0Formula.EvalArg.allC (AC0FormulaList.map (restrictFormula ρ) fs)) x =
                AC0Formula.evalCore n (AC0Formula.EvalArg.allC fs) (ρ.override x) := by
              simpa [restrictEvalArg] using h2
            simp [restrictEvalArg, AC0Formula.evalCore, h1', h2']
    | anyC fs =>
        cases fs with
        | nil =>
            simp [restrictEvalArg, AC0Formula.evalCore]
        | cons f fs =>
            have h1 := rec (.form f) (by
              simpa using (AC0Formula.evalMeasure_form_lt_any_cons n _ f fs)) x
            have h2 := rec (.anyC fs) (by
              simpa using (AC0Formula.evalMeasure_any_lt_any_cons n _ f fs)) x
            have h1' : AC0Formula.evalCore n (AC0Formula.EvalArg.form (restrictFormula ρ f)) x =
                AC0Formula.evalCore n (AC0Formula.EvalArg.form f) (ρ.override x) := by
              simpa [restrictEvalArg] using h1
            have h2' : AC0Formula.evalCore n (AC0Formula.EvalArg.anyC (AC0FormulaList.map (restrictFormula ρ) fs)) x =
                AC0Formula.evalCore n (AC0Formula.EvalArg.anyC fs) (ρ.override x) := by
              simpa [restrictEvalArg] using h2
            simp [restrictEvalArg, AC0Formula.evalCore, h1', h2']

/-- Evaluation commutes with restriction for formulas. -/
theorem eval_restrictFormula {n d : Nat} (ρ : Restriction n)
    (F : AC0Formula n d) (x : Core.BitVec n) :
    AC0Formula.eval n d (restrictFormula ρ F) x =
      AC0Formula.eval n d F (ρ.override x) := by
  simpa [AC0Formula.eval, AC0Formula.evalCore] using
    (evalCore_restrict_arg (ρ := ρ) (a := AC0Formula.EvalArg.form F) (x := x))

/-- Evaluation commutes with restriction for "all" lists. -/
theorem evalAll_restrictList {n d : Nat} (ρ : Restriction n)
    (fs : AC0FormulaList n d) (x : Core.BitVec n) :
    AC0Formula.evalAll n d (AC0FormulaList.map (restrictFormula ρ) fs) x =
      AC0Formula.evalAll n d fs (ρ.override x) := by
  simpa [AC0Formula.evalAll, AC0Formula.evalCore] using
    (evalCore_restrict_arg (ρ := ρ) (a := AC0Formula.EvalArg.allC fs) (x := x))

/-- Evaluation commutes with restriction for "any" lists. -/
theorem evalAny_restrictList {n d : Nat} (ρ : Restriction n)
    (fs : AC0FormulaList n d) (x : Core.BitVec n) :
    AC0Formula.evalAny n d (AC0FormulaList.map (restrictFormula ρ) fs) x =
      AC0Formula.evalAny n d fs (ρ.override x) := by
  simpa [AC0Formula.evalAny, AC0Formula.evalCore] using
    (evalCore_restrict_arg (ρ := ρ) (a := AC0Formula.EvalArg.anyC fs) (x := x))

end AC0Formula

end AC0
end Pnp3
