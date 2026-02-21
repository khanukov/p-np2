import AC0.MultiSwitching.Trace
import AC0.MultiSwitching.CanonicalDT

/-!
  pnp3/AC0/MultiSwitching/TraceBridge.lean

  Мост между “канонической трассой” и глубиной детерминированного
  канонического дерева `canonicalDT_CNF`.  Это закрывает узел 4.1:
  если глубина дерева не меньше `t`, то существует каноническая
  трасса длины `t`.

  Мы используем ту же детерминизацию, что и в `CanonicalDT.lean`:
  * выбираем первую pending‑клауза,
  * берём первый свободный литерал,
  * ветвимся по значению.

  Важно: доказательство строится по индукции на `t` и использует
  разбор глубины PDT для узла (`node`).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n w : Nat}

/-!
### Детерминированная версия трассы

`CanonicalTrace` в ядре хранит «первую pending‑клаузу», но **не**
фиксирует, какой свободный литерал внутри неё выбирается.
Для корректного моста к детерминированному `canonicalDT_CNF`
нам нужен усиленный вариант, где каждый шаг использует
`chooseFreeLiteral` (первый свободный литерал).

Мы не меняем основное определение `BadCNF`, а вводим явный
предикат согласованности трассы с `canonicalDT_CNF`.  Это позволяет
получить формально корректный мост:

* `depth ≥ t → BadCNF_deterministic`;
* `BadCNF_deterministic → depth ≥ t`.

При этом `BadCNF_deterministic` очевидно сильнее `BadCNF`.
-/

def traceStepDeterministic
    {n w : Nat} {F : CNF n w} {ρ : Restriction n}
    (selection : Restriction.PendingClauseSelection (ρ := ρ) F.clauses)
    (choice : ClausePendingWitness.Selection selection.witness) : Prop :=
  Restriction.firstPendingClause? ρ F.clauses = some selection
    ∧ choice.literal = chooseFreeLiteral (w := selection.witness)

def traceDeterministic
    {n w : Nat} {F : CNF n w} :
    {ρ : Restriction n} → {t : Nat} →
      Core.CNF.CanonicalTrace (F := F) ρ t → Prop
  | _, _, Core.CNF.CanonicalTrace.nil => True
  | _, _, Core.CNF.CanonicalTrace.cons selection choice tail =>
      traceStepDeterministic (selection := selection) (choice := choice)
        ∧ traceDeterministic (F := F) tail

lemma traceDeterministic_cast
    {n w : Nat} {F : CNF n w} {ρ ρ' : Restriction n} {t : Nat}
    (h : ρ = ρ')
    (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    traceDeterministic (F := F) (ρ := ρ') (t := t)
        (cast (by cases h; rfl) trace) ↔
      traceDeterministic (F := F) (ρ := ρ) (t := t) trace := by
  cases h
  rfl

def BadCNF_deterministic (F : CNF n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ trace : Core.CNF.CanonicalTrace (F := F) ρ t,
    traceDeterministic (F := F) (ρ := ρ) (t := t) trace

lemma badCNF_deterministic_implies_bad
    {n w : Nat} {F : CNF n w} {t : Nat} {ρ : Restriction n} :
    BadCNF_deterministic (F := F) t ρ → BadCNF (F := F) t ρ := by
  intro h
  rcases h with ⟨trace, _⟩
  exact ⟨trace⟩

/-!
### Детерминированный `Bad` для семейства формул

Мы переносим детерминированное определение на семейство CNF:
«плохая» рестрикция — та, для которой существует формула,
имеющая детерминированную каноническую трассу длины `t`.
Для encoding удобнее всегда выбирать *первую* плохую формулу.
-/

def BadFamily_deterministic
    {n w : Nat} (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ i, ∃ hi : i < F.length,
    BadCNF_deterministic (F := F.get ⟨i, hi⟩) t ρ

lemma badFamily_deterministic_implies_badFamily
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n} :
    BadFamily_deterministic (F := F) t ρ → BadFamily (F := F) t ρ := by
  intro h
  rcases h with ⟨i, hi, hbad⟩
  exact ⟨i, hi, badCNF_deterministic_implies_bad (F := F.get ⟨i, hi⟩) (t := t) (ρ := ρ) hbad⟩

noncomputable def firstBadIndexDet
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) : Nat := by
  classical
  exact Nat.find hbad

lemma firstBadIndexDet_spec
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) :
    ∃ hi : firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad < F.length,
      BadCNF_deterministic
        (F := F.get ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad, hi⟩)
        t ρ := by
  classical
  simpa [firstBadIndexDet] using (Nat.find_spec hbad)

noncomputable def firstBadTraceDet
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) :
    Core.CNF.CanonicalTrace
      (F := F.get
        ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad,
          (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩) ρ t := by
  classical
  exact Classical.choose (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).2

/-!
### Вспомогательный выбор ветви

Из доказательства `depth(node) ≥ t+1` получаем, что глубина одной
из ветвей ≥ t.  Это стандартная лемма для `PDT.depth`.
-/

lemma depth_ge_succ_iff {n : Nat} {i : Fin n} {L R : PDT n} {t : Nat} :
    PDT.depth (PDT.node i L R) ≥ Nat.succ t ↔
      PDT.depth L ≥ t ∨ PDT.depth R ≥ t := by
  constructor
  · intro h
    -- depth(node) = succ (max depth L R)
    have h' : Nat.max (PDT.depth L) (PDT.depth R) ≥ t := by
      exact Nat.le_of_succ_le_succ h
    exact (le_max_iff.mp h')
  · intro h
    -- max ≥ t ⇒ succ max ≥ succ t
    have hmax : Nat.max (PDT.depth L) (PDT.depth R) ≥ t := by
      exact le_max_iff.mpr h
    exact Nat.succ_le_succ hmax

/-!
### Выбор `ClausePendingWitness.Selection` для первого свободного литерала

`chooseFreeLiteral` в `CanonicalDT` выбирает первый элемент списка `w.free`.
Поэтому мы можем построить выбор с индексом `0` и произвольным значением
ветви `b`.
-/

noncomputable def chooseFreeLiteralChoice
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) (b : Bool) :
    ClausePendingWitness.Selection w := by
  classical
  -- Индекс 0 корректен по длине списка (список непуст).
  have hlen : 0 < w.free.length := by
    exact List.length_pos_of_ne_nil w.nonempty
  refine
    { index := ⟨0, hlen⟩
      value := b }

lemma chooseFreeLiteralChoice_literal
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) (b : Bool) :
    (chooseFreeLiteralChoice (w := w) b).literal =
      chooseFreeLiteral (w := w) := by
  classical
  cases hlist : w.free with
  | nil =>
      cases (w.nonempty (by simp [hlist]))
  | cons head tail =>
      -- При индексе 0 литерал совпадает с головой списка.
      dsimp [ClausePendingWitness.Selection.literal, chooseFreeLiteralChoice]
      simp [chooseFreeLiteral, hlist]

/-!
### Основная лемма: depth ≥ t → BadCNF

Мы доказываем по индукции по `t`, что глубина канонического дерева
не меньше `t` ⇒ существует трасса длины `t`.
-/

theorem badCNF_of_depth_ge_canonicalDT_aux
    (F : CNF n w) :
    ∀ {t fuel : Nat} {ρ : Restriction n},
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) →
      BadCNF (F := F) t ρ
  | 0, fuel, ρ, _ =>
      -- Пустая трасса существует всегда.
      ⟨Core.CNF.CanonicalTrace.nil⟩
  | Nat.succ t, fuel, ρ, hdepth => by
      classical
      -- Раскрываем определение `canonicalDT_CNF_aux`.
      cases hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          -- В этом случае дерево — лист, глубина 0 ⇒ противоречие.
          have : PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) = 0 := by
            cases fuel <;> simp [canonicalDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have hzero : Nat.succ t ≤ 0 := by
              -- После подстановки глубина листа равна нулю.
              have hdepth' := hdepth
              simp [this] at hdepth'
            exact (Nat.not_succ_le_zero _ hzero)
          exact (False.elim hcontr)
      | some selection =>
          -- Ветвление по первому свободному литералу.
          let w := selection.witness
          let ℓ := chooseFreeLiteral (w := w)
          have hmem : ℓ ∈ w.free := chooseFreeLiteral_mem (w := w)
          have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := w) (ℓ := ℓ) hmem
          let choiceFalse := chooseFreeLiteralChoice (w := w) false
          let choiceTrue := chooseFreeLiteralChoice (w := w) true
          -- Поддеревья после присваивания выбранной переменной.
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          have hchoiceFalse : choiceFalse.literal = ℓ := by
            simpa [choiceFalse, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := false)
          have hchoiceTrue : choiceTrue.literal = ℓ := by
            simpa [choiceTrue, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := true)
          have hassign0 :
              ρ.assign ℓ.idx false = some ρ0 := by
            simpa [ρ0] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
          have hassign1 :
              ρ.assign ℓ.idx true = some ρ1 := by
            simpa [ρ1] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
          have hchoiceFalseNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) = ρ0 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)
            have hchoice_idx : choiceFalse.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceFalse
            -- Переписываем индекс выбранного литерала.
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse))
                  = ρ.assign ℓ.idx false := by
                    simpa using hassign_choice'.symm
              _ = some ρ0 := hassign0
          have hchoiceTrueNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) = ρ1 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)
            have hchoice_idx : choiceTrue.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceTrue
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue))
                  = ρ.assign ℓ.idx true := by
                    simpa using hassign_choice'.symm
              _ = some ρ1 := hassign1
          -- Переписываем дерево в форме `node`.
          have hdepth_root :
              PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
                ≥ Nat.succ t := hdepth
          have hnode :
              canonicalDT_CNF_aux (F := F) fuel ρ =
                PDT.node ℓ.idx
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
            -- Разворачиваем `canonicalDT_CNF_aux` и фиксируем те же параметры.
            cases fuel with
            | zero =>
                have : PDT.depth (canonicalDT_CNF_aux (F := F) 0 ρ) = 0 := by
                  simp [canonicalDT_CNF_aux, PDT.depth]
                have hzero : Nat.succ t ≤ 0 := by
                  -- В случае листа глубина равна нулю.
                  have hdepth' := hdepth
                  simp [this] at hdepth'
                exact (False.elim (Nat.not_succ_le_zero _ hzero))
            | succ fuel =>
                simp [canonicalDT_CNF_aux, hsel, ℓ, ρ0, ρ1, w]
          have hbranch :
              PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) ≥ t
                ∨ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) ≥ t := by
            -- Используем лемму про глубину узла.
            have hdepth' :
                PDT.depth
                    (PDT.node ℓ.idx
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))
                  ≥ Nat.succ t := by
              have hdepth' := hdepth_root
              simp [hnode] at hdepth'
              exact hdepth'
            exact (depth_ge_succ_iff
              (i := ℓ.idx)
              (L := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
              (R := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1)
              (t := t)).1 hdepth'
          -- Выбираем ветку и строим трассу длины `t` для хвоста.
          cases hbranch with
          | inl hleft =>
              have htail : BadCNF (F := F) t ρ0 :=
                badCNF_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ0) hleft
              rcases htail with ⟨tail⟩
              have tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) t := by
                simpa [hchoiceFalseNext] using tail
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceFalse) tail'⟩
          | inr hright =>
              have htail : BadCNF (F := F) t ρ1 :=
                badCNF_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ1) hright
              rcases htail with ⟨tail⟩
              have tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) t := by
                simpa [hchoiceTrueNext] using tail
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceTrue) tail'⟩

theorem badCNF_of_depth_ge_canonicalDT
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) →
      BadCNF (F := F) t ρ := by
  intro hdepth
  -- `canonicalDT_CNF` использует `fuel = freeCount`.
  simpa [canonicalDT_CNF] using
    (badCNF_of_depth_ge_canonicalDT_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) hdepth)

/-!
### Усиленная версия: depth ≥ t → BadCNF_deterministic

В конструктивном доказательстве мы **сами** выбираем первый свободный
литерал (через `chooseFreeLiteralChoice`). Поэтому получаем детерминированную
трассу, совместимую с `canonicalDT_CNF`.
-/

theorem badCNF_deterministic_of_depth_ge_canonicalDT_aux
    (F : CNF n w) :
    ∀ {t fuel : Nat} {ρ : Restriction n},
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) →
      BadCNF_deterministic (F := F) t ρ
  | 0, fuel, ρ, _ =>
      ⟨Core.CNF.CanonicalTrace.nil, by simp [traceDeterministic]⟩
  | Nat.succ t, fuel, ρ, hdepth => by
      classical
      cases hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          have : PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) = 0 := by
            cases fuel <;> simp [canonicalDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have hzero : Nat.succ t ≤ 0 := by
              -- После подстановки глубина листа равна нулю.
              have hdepth' := hdepth
              simp [this] at hdepth'
            exact (Nat.not_succ_le_zero _ hzero)
          exact (False.elim hcontr)
      | some selection =>
          let w := selection.witness
          let ℓ := chooseFreeLiteral (w := w)
          have hmem : ℓ ∈ w.free := chooseFreeLiteral_mem (w := w)
          have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := w) (ℓ := ℓ) hmem
          let choiceFalse := chooseFreeLiteralChoice (w := w) false
          let choiceTrue := chooseFreeLiteralChoice (w := w) true
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          have hchoiceFalse : choiceFalse.literal = ℓ := by
            simpa [choiceFalse, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := false)
          have hchoiceTrue : choiceTrue.literal = ℓ := by
            simpa [choiceTrue, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := true)
          have hassign0 :
              ρ.assign ℓ.idx false = some ρ0 := by
            simpa [ρ0] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
          have hassign1 :
              ρ.assign ℓ.idx true = some ρ1 := by
            simpa [ρ1] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
          have hchoiceFalseNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) = ρ0 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)
            have hchoice_idx : choiceFalse.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceFalse
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse))
                  = ρ.assign ℓ.idx false := by
                    simpa using hassign_choice'.symm
              _ = some ρ0 := hassign0
          have hchoiceTrueNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) = ρ1 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)
            have hchoice_idx : choiceTrue.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceTrue
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue))
                  = ρ.assign ℓ.idx true := by
                    simpa using hassign_choice'.symm
              _ = some ρ1 := hassign1
          have hnode :
              canonicalDT_CNF_aux (F := F) fuel ρ =
                PDT.node ℓ.idx
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
            cases fuel with
            | zero =>
                have : (PDT.depth (canonicalDT_CNF_aux (F := F) 0 ρ)) = 0 := by
                  simp [canonicalDT_CNF_aux, PDT.depth]
                have hzero : Nat.succ t ≤ 0 := by
                  -- В случае листа глубина равна нулю.
                  have hdepth' := hdepth
                  simp [this] at hdepth'
                exact (False.elim (Nat.not_succ_le_zero _ hzero))
            | succ fuel =>
                simp [canonicalDT_CNF_aux, hsel, ℓ, ρ0, ρ1, w]
          have hbranch :
              PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) ≥ t
                ∨ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) ≥ t := by
            have hdepth' :
                PDT.depth
                    (PDT.node ℓ.idx
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))
                  ≥ Nat.succ t := by
              have hdepth'' := hdepth
              simp [hnode] at hdepth''
              exact hdepth''
            exact (depth_ge_succ_iff (i := ℓ.idx) (L := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
              (R := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) (t := t)).1 hdepth'
          cases hbranch with
          | inl hleft =>
              have htail :=
                badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ0) hleft
              rcases htail with ⟨tail, htail_det⟩
              -- Приводим хвост к нужному типу через равенство `nextRestriction`.
              have hcast_eq :
                  Core.CNF.CanonicalTrace (F := F) ρ0 t =
                    Core.CNF.CanonicalTrace (F := F)
                      (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) t := by
                simpa using
                  congrArg
                    (fun ρ =>
                      Core.CNF.CanonicalTrace (F := F) ρ t)
                    hchoiceFalseNext.symm
              let tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) t :=
                cast hcast_eq tail
              have htail_det' :
                  traceDeterministic (F := F) (ρ := _)
                    (t := t) tail' := by
                have hcast :=
                  (traceDeterministic_cast (F := F)
                    (ρ := ρ0)
                    (ρ' := ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse))
                    (t := t) (h := hchoiceFalseNext.symm) (trace := tail)).2 htail_det
                simpa [tail'] using hcast
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceFalse) tail', ?_⟩
              · constructor
                · exact ⟨hsel, hchoiceFalse⟩
                · exact htail_det'
          | inr hright =>
              have htail :=
                badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ1) hright
              rcases htail with ⟨tail, htail_det⟩
              -- Приводим хвост к нужному типу через равенство `nextRestriction`.
              have hcast_eq :
                  Core.CNF.CanonicalTrace (F := F) ρ1 t =
                    Core.CNF.CanonicalTrace (F := F)
                      (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) t := by
                simpa using
                  congrArg
                    (fun ρ =>
                      Core.CNF.CanonicalTrace (F := F) ρ t)
                    hchoiceTrueNext.symm
              let tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) t :=
                cast hcast_eq tail
              have htail_det' :
                  traceDeterministic (F := F) (ρ := _)
                    (t := t) tail' := by
                have hcast :=
                  (traceDeterministic_cast (F := F)
                    (ρ := ρ1)
                    (ρ' := ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue))
                    (t := t) (h := hchoiceTrueNext.symm) (trace := tail)).2 htail_det
                simpa [tail'] using hcast
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceTrue) tail', ?_⟩
              · constructor
                · exact ⟨hsel, hchoiceTrue⟩
                · exact htail_det'

theorem badCNF_deterministic_of_depth_ge_canonicalDT
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) →
    BadCNF_deterministic (F := F) t ρ := by
  intro hdepth
  simpa [canonicalDT_CNF] using
    (badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) hdepth)

/-!
### Обратный мост: детерминированная трасса ⇒ depth ≥ t
-/

theorem depth_ge_of_badCNF_deterministic_aux
    (F : CNF n w) :
    ∀ {t fuel : Nat} {ρ : Restriction n}
      (trace : Core.CNF.CanonicalTrace (F := F) ρ t),
      traceDeterministic (F := F) (ρ := ρ) (t := t) trace →
      t ≤ fuel →
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
  | 0, fuel, ρ, _, _, _ => by
      simp
  | Nat.succ t, fuel, ρ,
      Core.CNF.CanonicalTrace.cons selection choice tail, hdet, hfuel => by
      -- При `t+1 ≤ fuel` обязаны находиться в ветке `succ`.
      cases fuel with
      | zero =>
          exact (Nat.not_succ_le_zero _ hfuel).elim
      | succ fuel =>
      rcases hdet with ⟨⟨hsel, hchoice⟩, htail⟩
      -- Разворачиваем каноническое дерево по тем же параметрам.
      let w := selection.witness
      let ℓ := chooseFreeLiteral (w := w)
      have hmem : ℓ ∈ w.free := chooseFreeLiteral_mem (w := w)
      have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
        Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
          (ρ := ρ) (C := selection.clause) (w := w) (ℓ := ℓ) hmem
      have hchoice' : choice.literal = ℓ := by simpa [ℓ] using hchoice
      -- Определяем поддеревья `ρ0`/`ρ1` так же, как в `canonicalDT_CNF_aux`.
      let ρ0 := Classical.choose
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
      let ρ1 := Classical.choose
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
      have hnode :
          canonicalDT_CNF_aux (F := F) (Nat.succ fuel) ρ =
            PDT.node ℓ.idx
              (canonicalDT_CNF_aux (F := F) fuel ρ0)
              (canonicalDT_CNF_aux (F := F) fuel ρ1) := by
        simp [canonicalDT_CNF_aux, hsel, ℓ, ρ0, ρ1, w]
      have hassign_choice :
          ρ.assign ℓ.idx choice.value =
            some (ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
        -- Сначала переписываем индекс выбранного литерала.
        have hchoice_idx : choice.literal.idx = ℓ.idx := by
          simpa using congrArg Literal.idx hchoice'
        have hassign :=
          ClausePendingWitness.Selection.assign_eq
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
        -- Переписываем `choice.literal.idx` в `ℓ.idx` без раскрытия `assign`.
        rw [hchoice_idx] at hassign
        exact hassign
      -- Сравниваем `nextRestriction` с выбранным поддеревом.
      have hρchoice :
          ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
            = if choice.value = false then ρ0 else ρ1 := by
        cases hval : choice.value with
        | false =>
            have hassign0 :
                ρ.assign ℓ.idx false = some ρ0 := by
              simpa [ρ0] using
                (Classical.choose_spec
                  (Restriction.assign_some_of_mem_freeIndicesList
                    (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
            have hnext0 :
                ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
                  = ρ0 := by
              apply Option.some.inj
              have h1 : ρ.assign ℓ.idx false =
                  some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
                simpa [hval] using hassign_choice
              calc
                some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
                    = ρ.assign ℓ.idx false := by simpa using h1.symm
                _ = some ρ0 := hassign0
            simp [hnext0]
        | true =>
            have hassign1 :
                ρ.assign ℓ.idx true = some ρ1 := by
              simpa [ρ1] using
                (Classical.choose_spec
                  (Restriction.assign_some_of_mem_freeIndicesList
                    (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
            have hnext1 :
                ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
                  = ρ1 := by
              apply Option.some.inj
              have h1 : ρ.assign ℓ.idx true =
                  some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
                simpa [hval] using hassign_choice
              calc
                some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
                    = ρ.assign ℓ.idx true := by simpa using h1.symm
                _ = some ρ1 := hassign1
            simp [hnext1]
      have htail_depth :
          t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel
            (if choice.value = false then ρ0 else ρ1)) := by
        -- Индукционный шаг на хвосте.
        have hfuel_tail : t ≤ fuel := by
          -- Из `t+1 ≤ fuel+1` получаем `t ≤ fuel`.
          omega
        have htail' :=
          depth_ge_of_badCNF_deterministic_aux (F := F)
            (t := t) (fuel := fuel)
            (ρ := ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
            tail htail hfuel_tail
        simpa [hρchoice] using htail'
      -- Поднимаем на уровень `node`.
      have hdepth_node :
          t ≤
            Nat.max
              (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ0))
              (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ1)) := by
        cases hval : choice.value with
        | false =>
            have htail' :
                t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ0) := by
              simpa [hval] using htail_depth
            exact Nat.le_trans htail' (Nat.le_max_left _ _)
        | true =>
            have htail' :
                t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ1) := by
              simpa [hval] using htail_depth
            exact Nat.le_trans htail' (Nat.le_max_right _ _)
      have hdepth :
          Nat.succ t ≤
            PDT.depth (canonicalDT_CNF_aux (F := F) (Nat.succ fuel) ρ) := by
        -- `depth(node) = succ (max ...)`.
        have : PDT.depth (canonicalDT_CNF_aux (F := F) (Nat.succ fuel) ρ)
              = Nat.succ
                  (Nat.max
                    (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ0))
                    (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ1))) := by
          simp [hnode, PDT.depth]
        simpa [this] using Nat.succ_le_succ hdepth_node
      exact hdepth

theorem depth_ge_of_badCNF_deterministic
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    BadCNF_deterministic (F := F) t ρ →
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) := by
  intro hbad
  rcases hbad with ⟨trace, hdet⟩
  have hfuel : t ≤ ρ.freeCount := by
    -- Каноническая трасса длины `t` не может превышать число свободных координат.
    exact Core.CNF.CanonicalTrace.length_le_freeCount (trace := trace)
  simpa [canonicalDT_CNF] using
    (depth_ge_of_badCNF_deterministic_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) trace hdet hfuel)

end MultiSwitching
end AC0
end Pnp3
