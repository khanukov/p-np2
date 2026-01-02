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
  | ρ, _, Core.CNF.CanonicalTrace.cons selection choice tail =>
      traceStepDeterministic (selection := selection) (choice := choice)
        ∧ traceDeterministic (F := F) tail

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
  -- `w.free` непуст, значит он имеет вид `head :: tail`.
  rcases Classical.choose_spec (List.exists_cons_of_ne_nil w.nonempty) with
    ⟨tail, hfree⟩
  -- Индекс 0 корректен по длине списка.
  refine
    { index := ⟨0, by simpa [hfree]⟩
      value := b }

lemma chooseFreeLiteralChoice_literal
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) (b : Bool) :
    (chooseFreeLiteralChoice (w := w) b).literal =
      chooseFreeLiteral (w := w) := by
  classical
  rcases Classical.choose_spec (List.exists_cons_of_ne_nil w.nonempty) with
    ⟨tail, hfree⟩
  -- При индексе 0 литерал совпадает с головой списка.
  simp [chooseFreeLiteralChoice, chooseFreeLiteral, hfree]

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
            simp [canonicalDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have hzero : Nat.succ t ≤ 0 := by simpa [this] using hdepth
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
          let ρ0 := ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)
          let ρ1 := ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)
          have hchoiceFalse : choiceFalse.literal = ℓ := by
            simpa [choiceFalse, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := false)
          have hchoiceTrue : choiceTrue.literal = ℓ := by
            simpa [choiceTrue, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := true)
          -- Переписываем дерево в форме `node`.
          have hdepth' :
              PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
                ≥ Nat.succ t := hdepth
          have hnode :
              canonicalDT_CNF_aux (F := F) fuel ρ =
                PDT.node ℓ.idx
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
            -- Разворачиваем `canonicalDT_CNF_aux` и фиксируем те же параметры.
            simp [canonicalDT_CNF_aux, hsel, ℓ, hmem, hfree, ρ0, ρ1,
              choiceFalse, choiceTrue]
          have hbranch :
              PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) ≥ t
                ∨ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) ≥ t := by
            -- Используем формулу глубины для узла.
            have hrewrite :
                PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
                  = Nat.succ
                    (Nat.max
                      (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0))
                      (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))) := by
              simpa [hnode, PDT.depth]
            have hge :
                Nat.max
                  (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0))
                  (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1)) ≥ t := by
              have := (Nat.le_of_succ_le_succ (by simpa [hrewrite] using hdepth'))
              simpa using this
            exact (Nat.le_max_iff.mp hge)
          -- Выбираем ветку и строим трассу длины `t` для хвоста.
          cases hbranch with
          | inl hleft =>
              have htail : BadCNF (F := F) t ρ0 :=
                badCNF_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ0) hleft
              rcases htail with ⟨tail⟩
              refine ⟨Core.CNF.CanonicalTrace.cons selection ?_ tail⟩
              -- Выбор соответствует ветви `false`.
              exact choiceFalse
          | inr hright =>
              have htail : BadCNF (F := F) t ρ1 :=
                badCNF_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ1) hright
              rcases htail with ⟨tail⟩
              refine ⟨Core.CNF.CanonicalTrace.cons selection ?_ tail⟩
              -- Выбор соответствует ветви `true`.
              exact choiceTrue

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
            simp [canonicalDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have hzero : Nat.succ t ≤ 0 := by simpa [this] using hdepth
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
          let ρ0 := ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)
          let ρ1 := ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)
          have hchoiceFalse : choiceFalse.literal = ℓ := by
            simpa [choiceFalse, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := false)
          have hchoiceTrue : choiceTrue.literal = ℓ := by
            simpa [choiceTrue, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := true)
          have hnode :
              canonicalDT_CNF_aux (F := F) fuel ρ =
                PDT.node ℓ.idx
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
            simp [canonicalDT_CNF_aux, hsel, ℓ, hmem, hfree, ρ0, ρ1,
              choiceFalse, choiceTrue]
          have hbranch :
              PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) ≥ t
                ∨ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) ≥ t := by
            have hrewrite :
                PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
                  = Nat.succ
                    (Nat.max
                      (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0))
                      (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))) := by
              simpa [hnode, PDT.depth]
            have hge :
                Nat.max
                  (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0))
                  (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1)) ≥ t := by
              have := (Nat.le_of_succ_le_succ (by simpa [hrewrite] using hdepth))
              simpa using this
            exact (Nat.le_max_iff.mp hge)
          cases hbranch with
          | inl hleft =>
              have htail :=
                badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ0) hleft
              rcases htail with ⟨tail, htail_det⟩
              refine ⟨Core.CNF.CanonicalTrace.cons selection ?_ tail, ?_⟩
              · exact choiceFalse
              · constructor
                · exact ⟨hsel, hchoiceFalse⟩
                · simpa using htail_det
          | inr hright =>
              have htail :=
                badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ1) hright
              rcases htail with ⟨tail, htail_det⟩
              refine ⟨Core.CNF.CanonicalTrace.cons selection ?_ tail, ?_⟩
              · exact choiceTrue
              · constructor
                · exact ⟨hsel, hchoiceTrue⟩
                · simpa using htail_det

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
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
  | 0, fuel, ρ, _, _ => by
      simp [PDT.depth]
  | Nat.succ t, fuel, ρ,
      Core.CNF.CanonicalTrace.cons selection choice tail, hdet => by
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
          canonicalDT_CNF_aux (F := F) fuel ρ =
            PDT.node ℓ.idx
              (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
              (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
        simp [canonicalDT_CNF_aux, hsel, ℓ, hmem, hfree, ρ0, ρ1]
      have hassign_choice :
          ρ.assign ℓ.idx choice.value =
            some (ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
        simpa [hchoice'] using
          ClausePendingWitness.Selection.assign_eq
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
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
              exact h1.trans hassign0.symm
            simpa [hval, hnext0]
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
              exact h1.trans hassign1.symm
            simpa [hval, hnext1]
      have htail_depth :
          t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1)
            (if choice.value = false then ρ0 else ρ1)) := by
        -- Индукционный шаг на хвосте.
        have htail' :=
          depth_ge_of_badCNF_deterministic_aux (F := F)
            (t := t) (fuel := fuel - 1)
            (ρ := ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
            tail htail
        simpa [hρchoice] using htail'
      -- Поднимаем на уровень `node`.
      have hdepth_node :
          t ≤
            Nat.max
              (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0))
              (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1)) := by
        cases hval : choice.value with
        | false =>
            have htail' :
                t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) := by
              simpa [hval] using htail_depth
            exact Nat.le_max_left_of_le htail'
        | true =>
            have htail' :
                t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
              simpa [hval] using htail_depth
            exact Nat.le_max_right_of_le htail'
      have hdepth :
          Nat.succ t ≤
            PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) := by
        -- `depth(node) = succ (max ...)`.
        have : PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
              = Nat.succ
                  (Nat.max
                    (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0))
                    (PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))) := by
          simpa [hnode, PDT.depth]
        simpa [this] using Nat.succ_le_succ hdepth_node
      exact hdepth

theorem depth_ge_of_badCNF_deterministic
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    BadCNF_deterministic (F := F) t ρ →
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) := by
  intro hbad
  rcases hbad with ⟨trace, hdet⟩
  simpa [canonicalDT_CNF] using
    (depth_ge_of_badCNF_deterministic_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) trace hdet)

end MultiSwitching
end AC0
end Pnp3
