import Core.BooleanBasics

/-!
  pnp3/AC0/AC0Formula.lean

  Минимальное представление AC0‑формул глубины `d` как деревьев.
  Это закрывает пункт Phase 5.1 плана: явный тип `AC0Formula n d`
  и базовые функции `eval` и `size`.

  Конструкция **осознанно простая**:
  - depth = 0: атомарная функция (литерал/константа/любой булевый атом);
  - depth = d+1: AND/OR над списком подформул глубины `d`.

  Чтобы сохранить индекс по глубине без ограничений ядра, используем
  взаимную индукцию с собственным списком подформул.
-/

namespace Pnp3
namespace AC0

open Core

mutual

/-- AC0‑формула глубины `d` над `n` входными битами. -/
inductive AC0Formula (n : Nat) : Nat → Type
  | atom : (Core.BitVec n → Bool) → AC0Formula n 0
  | and : AC0FormulaList n d → AC0Formula n (Nat.succ d)
  | or  : AC0FormulaList n d → AC0Formula n (Nat.succ d)
  

/-- Список подформул фиксированной глубины. -/
inductive AC0FormulaList (n : Nat) : Nat → Type
  | nil : AC0FormulaList n d
  | cons : AC0Formula n d → AC0FormulaList n d → AC0FormulaList n d
  

end

namespace AC0FormulaList

variable {n d : Nat}

@[simp] def toList : AC0FormulaList n d → List (AC0Formula n d)
  | nil => []
  | cons f fs => f :: toList fs

@[simp] def map (g : AC0Formula n d → AC0Formula n d) : AC0FormulaList n d → AC0FormulaList n d
  | nil => nil
  | cons f fs => cons (g f) (map g fs)

end AC0FormulaList

namespace AC0Formula

variable {n d : Nat}

mutual

/-- Структурный размер формулы. -/
def structSize (n : Nat) (d : Nat) : AC0Formula n d → Nat
  | AC0Formula.atom _ => 1
  | @AC0Formula.and _ d' fs => 1 + structSizeList n d' fs
  | @AC0Formula.or _ d' fs  => 1 + structSizeList n d' fs

/-- Структурный размер списка подформул. -/
def structSizeList (n : Nat) (d : Nat) : AC0FormulaList n d → Nat
  | AC0FormulaList.nil => 0
  | AC0FormulaList.cons f fs => structSize n d f + structSizeList n d fs

end

/-- Helper: size of head is strictly below size of cons list (plus one). -/
lemma structSize_lt_cons (n d : Nat) (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    structSize n d f < structSizeList n d (AC0FormulaList.cons f fs) + 1 := by
  have h : structSize n d f ≤ structSize n d f + structSizeList n d fs := by
    exact Nat.le_add_right _ _
  have h' : structSize n d f < structSize n d f + structSizeList n d fs + 1 := by
    exact Nat.lt_succ_of_le h
  simpa [structSizeList, Nat.add_assoc] using h'

/-- Helper: tail size plus one is strictly below size of cons list (plus one). -/
lemma structSizeList_tail_lt_cons (n d : Nat) (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    structSizeList n d fs + 1 < structSizeList n d (AC0FormulaList.cons f fs) + 1 := by
  have hpos : 0 < structSize n d f := by
    cases f <;> simp [structSize, structSizeList]
  have h : structSizeList n d fs < structSize n d f + structSizeList n d fs := by
    exact Nat.lt_add_of_pos_left hpos
  have h' : structSizeList n d fs + 1 < structSize n d f + structSizeList n d fs + 1 := by
    exact Nat.add_lt_add_right h 1
  simpa [structSizeList, Nat.add_assoc] using h'

lemma structSize_lt_cons_forall (n d : Nat) (fs : AC0FormulaList n d) :
    ∀ f : AC0Formula n d,
      structSize n d f < structSizeList n d (AC0FormulaList.cons f fs) + 1 := by
  intro f
  exact structSize_lt_cons n d f fs

lemma structSizeList_tail_lt_cons_forall (n d : Nat) (fs : AC0FormulaList n d) :
    ∀ f : AC0Formula n d,
      structSizeList n d fs + 1 < structSizeList n d (AC0FormulaList.cons f fs) + 1 := by
  intro f
  exact structSizeList_tail_lt_cons n d f fs

@[simp] lemma structSize_atom (f : Core.BitVec n → Bool) :
    structSize n 0 (AC0Formula.atom f) = 1 := by rfl

@[simp] lemma structSize_and (fs : AC0FormulaList n d) :
    structSize n (Nat.succ d) (AC0Formula.and fs) = 1 + structSizeList n d fs := by rfl

@[simp] lemma structSize_or (fs : AC0FormulaList n d) :
    structSize n (Nat.succ d) (AC0Formula.or fs) = 1 + structSizeList n d fs := by rfl

@[simp] lemma structSizeList_nil :
    structSizeList n d AC0FormulaList.nil = 0 := by rfl

@[simp] lemma structSizeList_cons (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    structSizeList n d (AC0FormulaList.cons f fs) = structSize n d f + structSizeList n d fs := by rfl

lemma structSize_pos (f : AC0Formula n d) : 0 < structSize n d f := by
  cases f <;> simp [structSize, structSizeList]

inductive EvalArg (n : Nat) : Type
  | form : {d : Nat} → AC0Formula n d → EvalArg n
  | allC  : {d : Nat} → AC0FormulaList n d → EvalArg n
  | anyC  : {d : Nat} → AC0FormulaList n d → EvalArg n

def evalMeasure (n : Nat) : EvalArg n → Nat
  | EvalArg.form f => 2 * structSize n _ f
  | EvalArg.allC fs => 2 * structSizeList n _ fs + 1
  | EvalArg.anyC fs => 2 * structSizeList n _ fs + 1

lemma evalMeasure_all_lt_form_and (n d : Nat) (fs : AC0FormulaList n d) :
    evalMeasure n (.allC fs) < evalMeasure n (.form (AC0Formula.and fs)) := by
  have h : 2 * structSizeList n d fs + 1 < 2 * structSizeList n d fs + 1 + 1 := by
    exact Nat.lt_succ_self _
  simpa [evalMeasure, structSize, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma evalMeasure_all_lt_form_or (n d : Nat) (fs : AC0FormulaList n d) :
    evalMeasure n (.allC fs) < evalMeasure n (.form (AC0Formula.or fs)) := by
  have h : 2 * structSizeList n d fs + 1 < 2 * structSizeList n d fs + 1 + 1 := by
    exact Nat.lt_succ_self _
  simpa [evalMeasure, structSize, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma evalMeasure_any_lt_form_or (n d : Nat) (fs : AC0FormulaList n d) :
    evalMeasure n (.anyC fs) < evalMeasure n (.form (AC0Formula.or fs)) := by
  have h : 2 * structSizeList n d fs + 1 < 2 * structSizeList n d fs + 1 + 1 := by
    exact Nat.lt_succ_self _
  simpa [evalMeasure, structSize, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma evalMeasure_form_lt_all_cons (n d : Nat) (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    evalMeasure n (.form f) < evalMeasure n (.allC (AC0FormulaList.cons f fs)) := by
  have hpos : 0 < 2 * structSizeList n d fs + 1 := by
    exact Nat.succ_pos _
  have h : 2 * structSize n d f < 2 * structSize n d f + (2 * structSizeList n d fs + 1) := by
    exact Nat.lt_add_of_pos_right hpos
  simpa [evalMeasure, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma evalMeasure_form_lt_any_cons (n d : Nat) (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    evalMeasure n (.form f) < evalMeasure n (.anyC (AC0FormulaList.cons f fs)) := by
  have hpos : 0 < 2 * structSizeList n d fs + 1 := by
    exact Nat.succ_pos _
  have h : 2 * structSize n d f < 2 * structSize n d f + (2 * structSizeList n d fs + 1) := by
    exact Nat.lt_add_of_pos_right hpos
  simpa [evalMeasure, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma evalMeasure_all_lt_all_cons (n d : Nat) (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    evalMeasure n (.allC fs) < evalMeasure n (.allC (AC0FormulaList.cons f fs)) := by
  have h2 : 0 < (2 : Nat) := by decide
  have hpos : 0 < 2 * structSize n d f := by
    exact Nat.mul_pos h2 (structSize_pos (n := n) (d := d) f)
  have h : 2 * structSizeList n d fs + 1 < 2 * structSizeList n d fs + (2 * structSize n d f) + 1 := by
    exact Nat.add_lt_add_right (Nat.lt_add_of_pos_right hpos) 1
  simpa [evalMeasure, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma evalMeasure_any_lt_any_cons (n d : Nat) (f : AC0Formula n d) (fs : AC0FormulaList n d) :
    evalMeasure n (.anyC fs) < evalMeasure n (.anyC (AC0FormulaList.cons f fs)) := by
  have h2 : 0 < (2 : Nat) := by decide
  have hpos : 0 < 2 * structSize n d f := by
    exact Nat.mul_pos h2 (structSize_pos (n := n) (d := d) f)
  have h : 2 * structSizeList n d fs + 1 < 2 * structSizeList n d fs + (2 * structSize n d f) + 1 := by
    exact Nat.add_lt_add_right (Nat.lt_add_of_pos_right hpos) 1
  simpa [evalMeasure, structSizeList, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

def evalCore (n : Nat) (arg : EvalArg n) : Core.BitVec n → Bool :=
  match arg with
  | EvalArg.form f =>
      match f with
      | AC0Formula.atom g => g
      | @AC0Formula.and _ d' fs => evalCore n (.allC fs)
      | @AC0Formula.or _ d' fs  => evalCore n (.anyC fs)
  | EvalArg.allC fs =>
      match fs with
      | AC0FormulaList.nil => fun _ => true
      | AC0FormulaList.cons f fs' => fun x => evalCore n (.form f) x && evalCore n (.allC fs') x
  | EvalArg.anyC fs =>
      match fs with
      | AC0FormulaList.nil => fun _ => false
      | AC0FormulaList.cons f fs' => fun x => evalCore n (.form f) x || evalCore n (.anyC fs') x
termination_by evalMeasure n arg
decreasing_by
  all_goals
    first
      | simpa using (evalMeasure_all_lt_form_and n _ fs)
      | simpa using (evalMeasure_any_lt_form_or n _ fs)
      | simpa using (evalMeasure_form_lt_all_cons n _ f fs)
      | simpa using (evalMeasure_form_lt_any_cons n _ f fs)
      | simpa using (evalMeasure_all_lt_all_cons n _ f fs)
      | simpa using (evalMeasure_any_lt_any_cons n _ f fs)

/-- Вычисление значения формулы. -/
def eval (n : Nat) (d : Nat) (f : AC0Formula n d) : Core.BitVec n → Bool :=
  evalCore n (.form f)

/-- Все подформулы истинны. -/
def evalAll (n : Nat) (d : Nat) (fs : AC0FormulaList n d) : Core.BitVec n → Bool :=
  evalCore n (.allC fs)

/-- Хотя бы одна подформула истинна. -/
def evalAny (n : Nat) (d : Nat) (fs : AC0FormulaList n d) : Core.BitVec n → Bool :=
  evalCore n (.anyC fs)

/-- Размер формулы как число узлов дерева. -/
def size {n d : Nat} : AC0Formula n d → Nat := structSize n d

/-- Размер списка подформул. -/
def sizeList {n d : Nat} : AC0FormulaList n d → Nat := structSizeList n d

@[simp] lemma size_atom (f : Core.BitVec n → Bool) :
    size (AC0Formula.atom f) = 1 := by rfl

@[simp] lemma size_and (fs : AC0FormulaList n d) :
    size (AC0Formula.and fs) = 1 + sizeList (n := n) (d := d) fs := by rfl

@[simp] lemma size_or (fs : AC0FormulaList n d) :
    size (AC0Formula.or fs) = 1 + sizeList (n := n) (d := d) fs := by rfl

end AC0Formula

end AC0
end Pnp3
