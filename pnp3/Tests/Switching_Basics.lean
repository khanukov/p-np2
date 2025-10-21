import Core.BooleanBasics
import AC0.Formulas
import Mathlib.Data.Fin.Basic

open Pnp3
open Core
open scoped Classical

-- This block ensures the basic width-monotonicity lemmas for restrictions behave
-- as expected on a hand-crafted example.  Такие проверки помогают нам не
-- ошибиться, прежде чем подключать более тяжёлую комбинаторику switching-лемм.

namespace WidthSanity

/-!
  На этой площадке мы работаем только с объектами из пространства `AC0`.
  Чтобы избежать двусмысленности между `Core.Literal` и `AC0.Literal`,
  все конструкции пишем с явно указанным пространством имён.
-/

open AC0

private def lit0 : AC0.Literal 3 := ⟨⟨0, by decide⟩, true⟩
private def lit1 : AC0.Literal 3 := ⟨⟨1, by decide⟩, false⟩

private def clause : AC0.Clause 3 := ⟨[lit0, lit1]⟩

private def subcube : Subcube 3 :=
  fun
  | ⟨0, _⟩ => some false -- первый литерал конфликтует
  | ⟨1, _⟩ => none       -- второй остаётся свободным
  | ⟨2, _⟩ => none

lemma clause_restrict_pending_width_le :
    (Clause.restrict (C := clause) (β := subcube)).pendingWidth ≤ clause.width := by
  classical
  cases hres : Clause.restrict (C := clause) (β := subcube) with
  | satisfied =>
      -- В случае тождественной истинности остаточная ширина равна нулю.
      simpa [Clause.RestrictResult.pendingWidth, clause, Clause.width, hres]
  | falsified =>
      -- Противоположный случай: пустая дизъюнкция также даёт ширину 0.
      simpa [Clause.RestrictResult.pendingWidth, clause, Clause.width, hres]
  | pending pending =>
      -- Интересная ветка: применяем новую оценку ширины и разворачиваем определения.
      have := Clause.restrict_pending_width_le (C := clause) (β := subcube)
        (pending := pending) hres
      simpa [Clause.RestrictResult.pendingWidth, clause, Clause.width, hres]
        using this

private def term : AC0.Term 3 := ⟨[lit0, lit1]⟩

lemma term_restrict_pending_width_le :
    (Term.restrict (T := term) (β := subcube)).pendingWidth ≤ term.width := by
  classical
  cases hres : Term.restrict (T := term) (β := subcube) with
  | satisfied =>
      simpa [Term.RestrictResult.pendingWidth, term, Term.width, hres]
  | falsified =>
      simpa [Term.RestrictResult.pendingWidth, term, Term.width, hres]
  | pending pending =>
      have := Term.restrict_pending_width_le (T := term) (β := subcube)
        (pending := pending) hres
      simpa [Term.RestrictResult.pendingWidth, term, Term.width, hres]
        using this

end WidthSanity

namespace Pnp3.Tests

/-- Простейший тест: CNF из одной клаузы `x₀ = true`. -/
private def literal₀ : Literal 2 :=
  { idx := ⟨0, by decide⟩, value := true }

private def clause₀ : CnfClause 2 :=
  { literals := [literal₀],
    nodupIdx := by
      simpa using (List.nodup_singleton (literal₀.idx)) }

private def cnf₀ : CNF 2 1 :=
  { clauses := [clause₀],
    width_le := by
      intro C hC
      rcases List.mem_singleton.mp hC with rfl
      simp [CnfClause.width, clause₀] }

/-- Две точки на кубе: совместимая и несовместимая с клаузой. -/
private def xTrue : Core.BitVec 2 := fun i => Fin.cases true (fun _ => false) i
private def xFalse : Core.BitVec 2 := fun _ => false

@[simp] lemma clause₀_eval_true : clause₀.eval xTrue = true := by
  classical
  refine
    (CnfClause.eval_eq_true_iff (C := clause₀) (x := xTrue)).2 ?_
  refine ⟨literal₀, ?_, ?_⟩
  · simp [clause₀]
  · simp [Literal.holds, literal₀, xTrue, Fin.cases]

@[simp] lemma clause₀_eval_false : clause₀.eval xFalse = false := by
  classical
  refine
    (CnfClause.eval_eq_false_iff (C := clause₀) (x := xFalse)).2 ?_
  intro ℓ hℓ
  have hℓ' : ℓ = literal₀ := by
    simpa [clause₀] using hℓ
  subst hℓ'
  simp [Literal.eval, literal₀, xFalse]

@[simp] lemma cnf₀_eval_true : cnf₀.eval xTrue = true := by
  classical
  refine (CNF.eval_eq_true_iff (F := cnf₀) (x := xTrue)).2 ?_
  intro C hC
  rcases List.mem_singleton.mp hC with rfl
  simpa using (CnfClause.eval_eq_true_iff (C := clause₀) (x := xTrue)).1 clause₀_eval_true

@[simp] lemma cnf₀_eval_false : cnf₀.eval xFalse = false := by
  classical
  refine (CNF.eval_eq_false_iff (F := cnf₀) (x := xFalse)).2 ?_
  refine ⟨clause₀, ?_, ?_⟩
  · simp [cnf₀]
  · simpa using clause₀_eval_false

/-- Пример ограничения: фиксируем `x₀ := true`, `x₁` оставляем свободным. -/
private def restriction₀ : Restriction 2 :=
  { mask := fun
      | ⟨0, _⟩ => some true
      | ⟨1, _⟩ => none }

/-- Ограничения, дополнительно фиксирующие второй бит. -/
private def restriction₀_fix (b : Bool) : Restriction 2 :=
  { mask := fun
      | ⟨0, _⟩ => some true
      | ⟨1, _⟩ => some b }

/-- Ограничение, фиксирующее оба бита. -/
private def restriction_all_fixed : Restriction 2 :=
  { mask := fun
      | ⟨0, _⟩ => some true
      | ⟨1, _⟩ => some false }

lemma restriction_all_fixed_freeCount :
    restriction_all_fixed.freeCount = 0 := by
  classical
  unfold Restriction.freeCount Restriction.freeIndicesList restriction_all_fixed
  decide

lemma restriction_all_fixed_constant :
    restriction_all_fixed.isConstantOn cnf₀.eval = true := by
  classical
  refine Restriction.isConstantOn_of_freeCount_eq_zero
    (ρ := restriction_all_fixed) (f := cnf₀.eval) ?_
  simpa using restriction_all_fixed_freeCount

/-- Ограничение совместимо с точкой `xTrue`. -/
lemma restriction₀_compatible_true :
    restriction₀.compatible xTrue = true := by
  classical
  have hover : restriction₀.override xTrue = xTrue := by
    funext i
    fin_cases i <;> simp [Restriction.override, restriction₀, xTrue, Fin.cases]
  exact
    (Restriction.compatible_iff_override_eq (ρ := restriction₀) (x := xTrue)).2 hover

/-- Ограничение не совместимо с `xFalse`. -/
lemma restriction₀_not_compatible_false :
    restriction₀.compatible xFalse = false := by
  classical
  have hover : restriction₀.override xFalse ≠ xFalse := by
    intro h
    have hx := congrArg (fun f => f ⟨0, by decide⟩) h
    simpa [Restriction.override, restriction₀, xFalse, Fin.cases] using hx
  have hx : restriction₀.compatible xFalse = true → False := by
    intro hcompat
    have :=
      (Restriction.compatible_iff_override_eq (ρ := restriction₀) (x := xFalse)).1 hcompat
    exact hover this
  cases hbool : restriction₀.compatible xFalse
  · simpa [hbool]
  · exact (hx (by simpa [hbool])).elim

/-- При совместимой точке `restrict` оставляет значение функции. -/
lemma restriction₀_preserves_eval :
    restriction₀.restrict cnf₀.eval xTrue = cnf₀.eval xTrue := by
  have h := restriction₀_compatible_true
  simpa using Restriction.restrict_agree_of_compatible restriction₀ cnf₀.eval h

/-- После применения `restriction₀` формула `cnf₀` становится константой. -/
lemma restriction₀_constant :
    restriction₀.isConstantOn cnf₀.eval = true := by
  classical
  have htrue : ∀ x : Core.BitVec 2,
      restriction₀.restrict cnf₀.eval x = true := by
    intro x
    simp [Restriction.restrict, cnf₀, CNF.eval, clause₀, CnfClause.eval,
      Literal.eval, restriction₀, Restriction.override, literal₀]
  have hprop : ∀ x y : Core.BitVec 2,
      restriction₀.restrict cnf₀.eval x = restriction₀.restrict cnf₀.eval y := by
    intro x y
    have hx := htrue x
    have hy := htrue y
    simpa [hx, hy]
  simpa [Restriction.isConstantOn, hprop]

/-- Следовательно, PDT глубины ноль уже достаточен. -/
lemma restriction₀_depth_zero :
    Restriction.hasDecisionTreeOfDepth restriction₀ cnf₀.eval 0 = true := by
  classical
  -- По лемме `hasDecisionTreeOfDepth_zero` достаточно установить константность.
  simpa using
    (restriction₀_constant : restriction₀.isConstantOn cnf₀.eval = true)

/-- Попытка зафиксировать `x₀ := false` приводит к конфликту с маской. -/
@[simp] lemma restriction₀_assign_index0_false :
    restriction₀.assign ⟨0, by decide⟩ false = (none : Option (Restriction 2)) := by
  classical
  simp [Restriction.assign, restriction₀, Core.Subcube.assign]

/-- Проверяем, что глубины один достаточно для всех ограничений. -/
def checkAllRestrictionsDepthOne : Bool :=
  ((Restriction.enumerate 2).map
      (fun ρ => Restriction.hasDecisionTreeOfDepth ρ cnf₀.eval 1)).all
    (fun b => b)

-- Контролируем, что суммарная масса распределения `𝓡_p` действительно равна 1.
#eval Restriction.totalWeight 2 (1 / 2 : Rat)

#eval checkAllRestrictionsDepthOne

#eval
  (((Restriction.enumerate 2).filter
        (fun ρ => ρ.mask 0 = none)).map
      (fun ρ => ρ.weight (1 / 2 : Rat))).sum

-- Проверка новой леммы: свободная координата `1` в трёхмерном случае даёт ту же массу.
#eval
  (((Restriction.enumerate 3).filter
        (fun ρ => ρ.mask ⟨1, by decide⟩ = none)).map
      (fun ρ => ρ.weight (1 / 2 : Rat))).sum

#eval (1 / 2 : Rat) * Restriction.totalWeight 2 (1 / 2 : Rat)

-- Контрольное вычисление вероятности провала при `t = 0` и `p = 1/2`.
#eval CNF.failureProbability cnf₀ (1 / 2 : Rat) 0

/-- Уточняем: формула из леммы `failureProbability_eq_failureSet_sum` совпадает с прямым вычислением. -/
lemma cnf₀_failureProbability_eq_failureSet_sum :
    CNF.failureProbability cnf₀ (1 / 2 : Rat) 0 =
      ((cnf₀.failureSet 0).map fun ρ => ρ.weight (1 / 2 : Rat)).sum := by
  simpa using
    (CNF.failureProbability_eq_failureSet_sum
      (F := cnf₀) (p := (1 / 2 : Rat)) (t := 0))

/-- Илллюстрация общей оценки: вероятность неудачи не превосходит 1. -/
lemma cnf₀_failureProbability_le_one :
    CNF.failureProbability cnf₀ (1 / 2 : Rat) 0 ≤ 1 := by
  have hp₀ : 0 ≤ (1 / 2 : Rat) := by norm_num
  have hp₁ : (1 / 2 : Rat) ≤ 1 := by norm_num
  simpa using
    (CNF.failureProbability_le_one (F := cnf₀) (p := (1 / 2 : Rat))
      (t := 0) hp₀ hp₁)

/-- Проверяем и нижнюю границу: вероятность не опускается ниже нуля. -/
lemma cnf₀_failureProbability_nonneg :
    0 ≤ CNF.failureProbability cnf₀ (1 / 2 : Rat) 0 := by
  have hp₀ : 0 ≤ (1 / 2 : Rat) := by norm_num
  have hp₁ : (1 / 2 : Rat) ≤ 1 := by norm_num
  simpa using
    (CNF.failureProbability_nonneg (F := cnf₀) (p := (1 / 2 : Rat))
      (t := 0) hp₀ hp₁)

/-- Проверяем формулу суммы весов при `choice = none`. -/
lemma sum_weights_mask_none_zero_example :
    (((Restriction.enumerate 1).filter
        (fun ρ => ρ.mask 0 = none)).map (fun ρ => ρ.weight (1 / 3 : Rat))).sum
      = (1 / 3 : Rat) := by
  simpa using
    (Restriction.sum_weights_mask_none_zero (n := 0) (p := (1 / 3 : Rat)))

--
-- Дополнительная проверка новых конструктивных лемм для ограничений AC⁰-формул:
-- подкуб, фиксирующий первую переменную в `true`, превращает простые формулы в
-- константы.  Это обеспечивает корректность вспомогательных лемм, используемых
-- в конструктивном доказательстве multi-switching-леммы.
--
section AC0Restriction

open AC0

private def litAC0 : AC0.Literal 2 := ⟨⟨0, by decide⟩, true⟩

private def clauseAC0 : AC0.Clause 2 := ⟨[litAC0]⟩

private def termAC0 : AC0.Term 2 := ⟨[litAC0]⟩

private def cnfAC0 : AC0.CNF 2 := ⟨[clauseAC0]⟩

private def dnfAC0 : AC0.DNF 2 := ⟨[termAC0]⟩

private def beta : Core.Subcube 2
  | ⟨0, _⟩ => some true
  | _       => none

private def vecTrue : Core.BitVec 2
  | ⟨0, _⟩ => true
  | _       => false

lemma clauseAC0_restrict_satisfied :
    Clause.restrict (β := beta) clauseAC0 =
      Clause.RestrictResult.satisfied := by
  classical
  have hβ : beta ⟨0, by decide⟩ = some true := by simp [beta]
  simpa [clauseAC0, litAC0, hβ] using
    Clause.restrict_singleton_satisfied (β := beta)
      (i := ⟨0, by decide⟩) (b := true) (h := hβ)

lemma termAC0_restrict_satisfied :
    Term.restrict (β := beta) termAC0 =
      Term.RestrictResult.satisfied := by
  classical
  have hβ : beta ⟨0, by decide⟩ = some true := by simp [beta]
  simpa [termAC0, litAC0, hβ] using
    Term.restrict_singleton_satisfied (β := beta)
      (i := ⟨0, by decide⟩) (b := true) (h := hβ)

end AC0Restriction

end Pnp3.Tests
