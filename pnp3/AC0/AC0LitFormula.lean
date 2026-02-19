import Core.BooleanBasics

/-!
  pnp3/AC0/AC0LitFormula.lean

  AC0 formulas with literal atoms: depth-0 nodes are positive literals,
  negative literals, or Boolean constants (not arbitrary functions).

  This is the correct type for multi-switching: Håstad's switching lemma
  applies to bounded-depth formulas where the bottom layer consists of
  actual input literals, not arbitrary Boolean functions.

  The structure mirrors `AC0Formula` but replaces the `atom` constructor
  (which wraps an arbitrary `Core.BitVec n → Bool`) with three constructors
  that enforce the literal restriction.
-/

namespace Pnp3
namespace AC0

open Core

mutual

/-- AC0 formula with literal atoms, indexed by depth `d` over `n` input bits. -/
inductive AC0LitFormula (n : Nat) : Nat → Type
  | posLit : Fin n → AC0LitFormula n 0
  | negLit : Fin n → AC0LitFormula n 0
  | constLit : Bool → AC0LitFormula n 0
  | and : AC0LitFormulaList n d → AC0LitFormula n (d + 1)
  | or : AC0LitFormulaList n d → AC0LitFormula n (d + 1)

/-- List of literal formulas at a fixed depth. -/
inductive AC0LitFormulaList (n : Nat) : Nat → Type
  | nil : AC0LitFormulaList n d
  | cons : AC0LitFormula n d → AC0LitFormulaList n d → AC0LitFormulaList n d

end

namespace AC0LitFormulaList

variable {n d : Nat}

@[simp] def toList : AC0LitFormulaList n d → List (AC0LitFormula n d)
  | nil => []
  | cons f fs => f :: toList fs

end AC0LitFormulaList

namespace AC0LitFormula

variable {n d : Nat}

/-! ### Structural size -/

mutual

def structSize (n : Nat) (d : Nat) : AC0LitFormula n d → Nat
  | AC0LitFormula.posLit _ => 1
  | AC0LitFormula.negLit _ => 1
  | AC0LitFormula.constLit _ => 1
  | @AC0LitFormula.and _ d' fs => 1 + structSizeList n d' fs
  | @AC0LitFormula.or _ d' fs  => 1 + structSizeList n d' fs

def structSizeList (n : Nat) (d : Nat) : AC0LitFormulaList n d → Nat
  | AC0LitFormulaList.nil => 0
  | AC0LitFormulaList.cons f fs => structSize n d f + structSizeList n d fs

end

def size {n d : Nat} : AC0LitFormula n d → Nat := structSize n d

def sizeList {n d : Nat} : AC0LitFormulaList n d → Nat := structSizeList n d

lemma structSize_pos (f : AC0LitFormula n d) : 0 < structSize n d f := by
  cases f <;> simp [structSize]

/-! ### Evaluation -/

inductive EvalArg (n : Nat) : Type
  | form : {d : Nat} → AC0LitFormula n d → EvalArg n
  | allC  : {d : Nat} → AC0LitFormulaList n d → EvalArg n
  | anyC  : {d : Nat} → AC0LitFormulaList n d → EvalArg n

def evalMeasure (n : Nat) : EvalArg n → Nat
  | EvalArg.form f => 2 * structSize n _ f
  | EvalArg.allC fs => 2 * structSizeList n _ fs + 1
  | EvalArg.anyC fs => 2 * structSizeList n _ fs + 1

private lemma evalMeasure_all_lt_form_and (n d : Nat) (fs : AC0LitFormulaList n d) :
    evalMeasure n (.allC fs) < evalMeasure n (.form (AC0LitFormula.and fs)) := by
  simp [evalMeasure, structSize]; omega

private lemma evalMeasure_any_lt_form_or (n d : Nat) (fs : AC0LitFormulaList n d) :
    evalMeasure n (.anyC fs) < evalMeasure n (.form (AC0LitFormula.or fs)) := by
  simp [evalMeasure, structSize]; omega

private lemma evalMeasure_form_lt_all_cons (n d : Nat) (f : AC0LitFormula n d) (fs : AC0LitFormulaList n d) :
    evalMeasure n (.form f) < evalMeasure n (.allC (AC0LitFormulaList.cons f fs)) := by
  simp [evalMeasure, structSizeList]; omega

private lemma evalMeasure_form_lt_any_cons (n d : Nat) (f : AC0LitFormula n d) (fs : AC0LitFormulaList n d) :
    evalMeasure n (.form f) < evalMeasure n (.anyC (AC0LitFormulaList.cons f fs)) := by
  simp [evalMeasure, structSizeList]; omega

private lemma evalMeasure_all_lt_all_cons (n d : Nat) (f : AC0LitFormula n d) (fs : AC0LitFormulaList n d) :
    evalMeasure n (.allC fs) < evalMeasure n (.allC (AC0LitFormulaList.cons f fs)) := by
  have := structSize_pos (n := n) (d := d) f
  simp [evalMeasure, structSizeList]; omega

private lemma evalMeasure_any_lt_any_cons (n d : Nat) (f : AC0LitFormula n d) (fs : AC0LitFormulaList n d) :
    evalMeasure n (.anyC fs) < evalMeasure n (.anyC (AC0LitFormulaList.cons f fs)) := by
  have := structSize_pos (n := n) (d := d) f
  simp [evalMeasure, structSizeList]; omega

def evalCore (n : Nat) (arg : EvalArg n) : Core.BitVec n → Bool :=
  match arg with
  | EvalArg.form f =>
      match f with
      | AC0LitFormula.posLit i => fun x => x i
      | AC0LitFormula.negLit i => fun x => !(x i)
      | AC0LitFormula.constLit b => fun _ => b
      | @AC0LitFormula.and _ d' fs => evalCore n (.allC fs)
      | @AC0LitFormula.or _ d' fs  => evalCore n (.anyC fs)
  | EvalArg.allC fs =>
      match fs with
      | AC0LitFormulaList.nil => fun _ => true
      | AC0LitFormulaList.cons f fs' => fun x => evalCore n (.form f) x && evalCore n (.allC fs') x
  | EvalArg.anyC fs =>
      match fs with
      | AC0LitFormulaList.nil => fun _ => false
      | AC0LitFormulaList.cons f fs' => fun x => evalCore n (.form f) x || evalCore n (.anyC fs') x
termination_by evalMeasure n arg
decreasing_by
  all_goals
    first
      | exact evalMeasure_all_lt_form_and n _ fs
      | exact evalMeasure_any_lt_form_or n _ fs
      | exact evalMeasure_form_lt_all_cons n _ f fs
      | exact evalMeasure_form_lt_any_cons n _ f fs
      | exact evalMeasure_all_lt_all_cons n _ f fs

/-- Evaluate a literal formula. -/
def eval (n : Nat) (d : Nat) (f : AC0LitFormula n d) : Core.BitVec n → Bool :=
  evalCore n (.form f)

/-- Conjunction of all subformulas. -/
def evalAll (n : Nat) (d : Nat) (fs : AC0LitFormulaList n d) : Core.BitVec n → Bool :=
  evalCore n (.allC fs)

/-- Disjunction of all subformulas. -/
def evalAny (n : Nat) (d : Nat) (fs : AC0LitFormulaList n d) : Core.BitVec n → Bool :=
  evalCore n (.anyC fs)

end AC0LitFormula

end AC0
end Pnp3
