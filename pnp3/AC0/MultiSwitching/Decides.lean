import Core.BooleanBasics
import AC0.MultiSwitching.Definitions

/-!
  pnp3/AC0/MultiSwitching/Decides.lean

  Леммы о решённости CNF под ограничением: когда `clauseStatus` достаточно
  чтобы гарантировать константность `CNF.eval` на `ρ.override`.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core
open Restriction

variable {n w : Nat}

/-- Формула решена под ограничением, если она уже константна после `override`. -/
@[simp] def DecidesCNFOn (ρ : Restriction n) (F : CNF n w) : Prop :=
  ρ.isConstantOn (CNF.eval F) = true

/-- Семейство решено под ограничением, если решена каждая формула. -/
def DecidesFamilyOn (ρ : Restriction n) (F : FormulaFamily n w) : Prop :=
  ∀ i : Fin F.length, DecidesCNFOn (ρ := ρ) (F := F.get i)

/-!
  Restriction-aware family: outside `ρ` функции обнуляются.
-/

@[simp] def restrictFun (ρ : Restriction n) (f : Core.BitVec n → Bool) :
    Core.BitVec n → Bool :=
  fun x => if ρ.compatible x then f x else false

@[simp] def restrictFamily (ρ : Restriction n) (F : Core.Family n) :
    Core.Family n :=
  F.map (restrictFun ρ)

@[simp] def evalFamilyRestrict (ρ : Restriction n) (F : FormulaFamily n w) :
    Core.Family n :=
  restrictFamily (ρ := ρ) (F := evalFamily F)

lemma mem_evalFamilyRestrict_iff
    {ρ : Restriction n} {F : FormulaFamily n w} {f : Core.BitVec n → Bool} :
    f ∈ evalFamilyRestrict (ρ := ρ) (F := F) ↔
      ∃ g ∈ evalFamily F, f = restrictFun ρ g := by
  classical
  unfold evalFamilyRestrict restrictFamily
  constructor
  · intro hf
    rcases List.mem_map.1 hf with ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact List.mem_map.2 ⟨g, hg, rfl⟩

/-- Из `clauseStatus = satisfied` извлекаем удовлетворяющий литерал. -/
lemma clauseStatus_satisfied_exists_literal
    {ρ : Restriction n} {C : CnfClause n}
    (h : ρ.clauseStatus C = ClauseStatus.satisfied) :
    ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied := by
  classical
  by_cases hsat : ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied
  · exact hsat
  · by_cases hfree : ρ.freeLiterals C = []
    · have hs : ρ.clauseStatus C = ClauseStatus.falsified := by
        simp [Restriction.clauseStatus, hsat, hfree,
          -Restriction.literalStatus, -Restriction.freeLiterals]
      have : (ClauseStatus.satisfied (ρ := ρ) (C := C)) =
          (ClauseStatus.falsified (ρ := ρ) (C := C)) := by
        exact h.symm.trans hs
      cases this
    · have h' := h
      have h'' : (ClauseStatus.falsified (ρ := ρ) (C := C)) =
          (ClauseStatus.satisfied (ρ := ρ) (C := C)) := by
        simpa [Restriction.clauseStatus, hsat, hfree,
          -Restriction.literalStatus, -Restriction.freeLiterals] using h'
      cases h''

/-- Если клауза удовлетворена, то она истинна на всех `ρ.override x`. -/
lemma clauseStatus_satisfied_eval_override_true
    {ρ : Restriction n} {C : CnfClause n} {x : Core.BitVec n}
    (h : ρ.clauseStatus C = ClauseStatus.satisfied) :
    C.eval (ρ.override x) = true := by
  classical
  rcases clauseStatus_satisfied_exists_literal (ρ := ρ) (C := C) h with
    ⟨ℓ, hℓ, hstatus⟩
  have hval : Literal.eval ℓ (ρ.override x) = true := by
    exact Restriction.literalStatus_eval_override_true
      (ρ := ρ) (ℓ := ℓ) (x := x) hstatus
  exact CnfClause.holds_of_mem_eval_true (C := C) (x := ρ.override x) hℓ hval

/-- Если клауза фальсифицирована, то каждый её литерал лжив на `ρ.override`. -/
lemma clauseStatus_falsified_all_literals_falsified
    {ρ : Restriction n} {C : CnfClause n}
    (h : ρ.clauseStatus C = ClauseStatus.falsified) :
    ∀ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.falsified := by
  classical
  -- Разворачиваем `clauseStatus`: falsified возможно только при
  -- `hsat = false` и `free = []`.
  have hsat : ¬ ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied := by
    intro hsat
    have hs : ρ.clauseStatus C = ClauseStatus.satisfied := by
      simp [Restriction.clauseStatus, hsat,
        -Restriction.literalStatus, -Restriction.freeLiterals]
    have : (ClauseStatus.falsified (ρ := ρ) (C := C)) =
        (ClauseStatus.satisfied (ρ := ρ) (C := C)) := by
      exact h.symm.trans hs
    cases this
  have hfree : ρ.freeLiterals C = [] := by
    by_contra hfree
    have h' := h
    have : False := by
      simpa [Restriction.clauseStatus, hsat, hfree,
        -Restriction.literalStatus, -Restriction.freeLiterals] using h'
    exact this.elim
  -- Из `free = []` получаем отсутствие `unassigned`.
  have hno_unassigned :
      ∀ ℓ ∈ C.literals, ρ.literalStatus ℓ ≠ LiteralStatus.unassigned := by
    exact (Restriction.freeLiterals_eq_nil_iff (ρ := ρ) (C := C)).1 hfree
  -- И из `hsat = false` получаем отсутствие `satisfied`.
  have hno_satisfied :
      ∀ ℓ ∈ C.literals, ρ.literalStatus ℓ ≠ LiteralStatus.satisfied := by
    intro ℓ hℓ hstat
    exact hsat ⟨ℓ, hℓ, hstat⟩
  intro ℓ hℓ
  -- Остаётся единственная возможность: `falsified`.
  have hcases :=
    LiteralStatus.eq_satisfied_or_eq_falsified_or_eq_unassigned
      (ρ.literalStatus ℓ)
  rcases hcases with hsat' | hfal' | hun'
  · exact (hno_satisfied ℓ hℓ hsat').elim
  · exact hfal'
  · exact (hno_unassigned ℓ hℓ hun').elim

/-- Если клауза фальсифицирована, то она ложна на всех `ρ.override x`. -/
lemma clauseStatus_falsified_eval_override_false
    {ρ : Restriction n} {C : CnfClause n} {x : Core.BitVec n}
    (h : ρ.clauseStatus C = ClauseStatus.falsified) :
    C.eval (ρ.override x) = false := by
  classical
  have hall : ∀ ℓ ∈ C.literals, Literal.eval ℓ (ρ.override x) = false := by
    intro ℓ hℓ
    have hstat := clauseStatus_falsified_all_literals_falsified
      (ρ := ρ) (C := C) h ℓ hℓ
    exact Restriction.literalStatus_eval_override_false
      (ρ := ρ) (ℓ := ℓ) (x := x) hstat
  exact (CnfClause.eval_eq_false_iff (C := C) (x := ρ.override x)).2 hall

/-- Если все клаузы удовлетворены, КНФ истинна на всех `ρ.override x`. -/
lemma cnf_eval_override_true_of_all_satisfied
    {ρ : Restriction n} {F : CNF n w} {x : Core.BitVec n}
    (h : ∀ C ∈ F.clauses, ρ.clauseStatus C = ClauseStatus.satisfied) :
    F.eval (ρ.override x) = true := by
  classical
  -- `CNF.eval` — это `all` по клаузам.
  unfold CNF.eval
  apply List.all_eq_true.mpr
  intro C hC
  exact clauseStatus_satisfied_eval_override_true
    (ρ := ρ) (C := C) (x := x) (h C hC)

/-- Если существует фальсифицированная клауза, КНФ ложна на всех `ρ.override x`. -/
lemma cnf_eval_override_false_of_falsified
    {ρ : Restriction n} {F : CNF n w} {x : Core.BitVec n}
    (h : ∃ C ∈ F.clauses, ρ.clauseStatus C = ClauseStatus.falsified) :
    F.eval (ρ.override x) = false := by
  classical
  rcases h with ⟨C, hC, hstat⟩
  -- Если хотя бы одна клауза ложна, то `all` даёт false.
  apply (CNF.eval_eq_false_iff (F := F) (x := ρ.override x)).2
  exact ⟨C, hC,
    clauseStatus_falsified_eval_override_false
      (ρ := ρ) (C := C) (x := x) hstat⟩

/-- Решённость CNF (в смысле статусов клауз) даёт константность после ограничения. -/
lemma decidesCNFOn_of_clauseStatus
    {ρ : Restriction n} {F : CNF n w}
    (h : (∃ C ∈ F.clauses, ρ.clauseStatus C = ClauseStatus.falsified)
      ∨ (∀ C ∈ F.clauses, ρ.clauseStatus C = ClauseStatus.satisfied)) :
    DecidesCNFOn (ρ := ρ) (F := F) := by
  classical
  -- Показываем, что `ρ.restrict` возвращает константу на всех входах.
  have hconst : ∀ x y : Core.BitVec n,
      ρ.restrict (CNF.eval F) x = ρ.restrict (CNF.eval F) y := by
    intro x y
    unfold Restriction.restrict
    cases h with
    | inl hfals =>
        have hx := cnf_eval_override_false_of_falsified
          (ρ := ρ) (F := F) (x := x) hfals
        have hy := cnf_eval_override_false_of_falsified
          (ρ := ρ) (F := F) (x := y) hfals
        rw [hx, hy]
    | inr hall =>
        have hx := cnf_eval_override_true_of_all_satisfied
          (ρ := ρ) (F := F) (x := x) hall
        have hy := cnf_eval_override_true_of_all_satisfied
          (ρ := ρ) (F := F) (x := y) hall
        rw [hx, hy]
  -- Превращаем в `isConstantOn`.
  have := (Restriction.isConstantOn_iff (ρ := ρ) (f := CNF.eval F)).mpr hconst
  simpa [DecidesCNFOn] using this

/-!
  Связь с `firstPendingClause?`: если pending не найден, то либо есть
  фальсифицированная клауза, либо все удовлетворены.
-/

lemma clauseStatus_cases
    {ρ : Restriction n} {C : CnfClause n} :
    (ρ.clauseStatus C = ClauseStatus.satisfied) ∨
      (ρ.clauseStatus C = ClauseStatus.falsified) ∨
      (∃ w, ρ.clauseStatus C = ClauseStatus.pending w) := by
  cases h : ρ.clauseStatus C with
  | satisfied =>
      exact Or.inl rfl
  | falsified =>
      exact Or.inr (Or.inl rfl)
  | pending w =>
      exact Or.inr (Or.inr ⟨w, rfl⟩)

lemma no_pendingClauseStatus_of_firstPending_none
    {ρ : Restriction n} :
    ∀ clauses : List (CnfClause n),
      Restriction.firstPendingClause? (ρ := ρ) clauses = none →
        (∃ C ∈ clauses, ρ.clauseStatus C = ClauseStatus.falsified) ∨
        (∀ C ∈ clauses, ρ.clauseStatus C = ClauseStatus.satisfied)
  | [], _ => by
      right
      intro C hC
      cases hC
  | C :: rest, hnone => by
      -- Разбираем статус первой клаузы через none-iff лемму.
      have hcases :=
        (Restriction.firstPendingClause?_cons_none_iff
          (ρ := ρ) (C := C) (rest := rest)).1 hnone
      rcases hcases with hfals | ⟨hsat, hrest⟩
      · exact Or.inl ⟨C, by simp, hfals⟩
      · have hIH := no_pendingClauseStatus_of_firstPending_none rest hrest
        cases hIH with
        | inl hf =>
            rcases hf with ⟨C', hC', hstat⟩
            exact Or.inl ⟨C', by simp [hC'], hstat⟩
        | inr hall =>
            right
            intro C' hC'
            have hC'cases := List.mem_cons.mp hC'
            cases hC'cases with
            | inl hC' =>
                subst hC'
                exact hsat
            | inr hC' =>
                exact hall _ hC'

lemma decidesCNFOn_of_firstPendingClause?_none
    {ρ : Restriction n} {F : CNF n w}
    (h : Restriction.firstPendingClause? (ρ := ρ) F.clauses = none) :
    DecidesCNFOn (ρ := ρ) (F := F) := by
  have hcases := no_pendingClauseStatus_of_firstPending_none (ρ := ρ) F.clauses h
  exact decidesCNFOn_of_clauseStatus (ρ := ρ) (F := F) hcases

end MultiSwitching
end AC0
end Pnp3
