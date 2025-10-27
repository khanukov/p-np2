/-
  pnp3/AC0/Formulas.lean

  Формализация базовых булевых формул, появляющихся в классических
  switching-леммах: конъюнктивные и дизъюнктивные термы, а также их
  ограничение случайными подкубами.  Этот модуль служит подготовительным
  этапом к устранению внешних аксиом `shrinkage_for_AC0` и
  `shrinkage_for_localCircuit`: после определения синтаксиса формул можно
  строить непосредственные деревья решений и проводить оценку ошибок.

  Основная идея — работать с произвольными списками литералов.  Мы не
  накладываем немедленно ограничений на ширину, поэтому подход применим
  и в более сложных сценариях (например, при анализе локальных схем).
-/

import Core.BooleanBasics

namespace Pnp3
namespace AC0

open Core

namespace List

variable {α : Type _}

/-- Если два булевых предиката совпадают на каждом элементе списка, то и
    результат `all` одинаков. -/
lemma all_congr {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  -- Аккуратно раскручиваем список: для пустого случая всё очевидно.
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      -- На голове списка равенства предикатов следуют из предположения `h`.
      have hhead : p a = q a := by
        exact h a (by simp)
      -- На хвосте — по индуктивному предположению и условию `h`.
      have htail : ∀ x ∈ t, p x = q x := by
        intro x hx
        exact h x (List.mem_cons_of_mem _ hx)
      have hrest := ih htail
      -- Собираем результат, пользуясь раскрытой формулой для `List.all`.
      simpa [List.all_cons, hhead, hrest]

/-- Аналогичное утверждение для дизъюнкции по списку. -/
lemma any_congr {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  -- Аналогичный разбор, но для дизъюнкции по списку.
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      have hhead : p a = q a := by
        exact h a (by simp)
      have htail : ∀ x ∈ t, p x = q x := by
        intro x hx
        exact h x (List.mem_cons_of_mem _ hx)
      have hrest := ih htail
      simpa [List.any_cons, hhead, hrest]

end List

/-! ### Литералы -/

/-- Литерал — указание индекса входной переменной и требуемого булевого
    значения.  В ДНФ термы строятся как конъюнкции литералов, а в КНФ
    клаузы — как дизъюнкции. -/
structure Literal (n : Nat) where
  idx : Fin n
  val : Bool
  deriving DecidableEq, Repr

namespace Literal

variable {n : Nat}

/-- Истинность литерала на данном входе в булевой форме.  Мы явно
    используем `decide`, чтобы без труда подключать `List.any` и
    `List.all`. -/
@[simp] def holds (ℓ : Literal n) (x : Core.BitVec n) : Bool :=
  decide (x ℓ.idx = ℓ.val)

/-- Удобное представление литерала как пары `BitFix`. -/
@[simp] def toBitFix (ℓ : Literal n) : BitFix n :=
  (ℓ.idx, ℓ.val)

/-- Построение литерала из пары индекса и значения. -/
@[simp] def ofBitFix (pair : BitFix n) : Literal n :=
  ⟨pair.1, pair.2⟩

@[simp] lemma ofBitFix_toBitFix (ℓ : Literal n) :
    ofBitFix (toBitFix ℓ) = ℓ := by
  cases ℓ
  rfl

@[simp] lemma toBitFix_ofBitFix (pair : BitFix n) :
    toBitFix (ofBitFix pair) = pair := by
  cases pair
  rfl

end Literal

/-! ### Клаузы (дизъюнкции литералов) -/

/-- Клауза в КНФ: дизъюнкция литералов. -/
structure Clause (n : Nat) where
  lits : List (Literal n)
  deriving DecidableEq, Repr

namespace Clause

variable {n : Nat}

/-- Удобная оболочка вокруг `List.any`: значение списка литералов на входе. -/
@[simp] def evalList (lits : List (Literal n)) (x : Core.BitVec n) : Bool :=
  lits.any (fun ℓ => Literal.holds ℓ x)

@[simp] lemma evalList_nil (x : Core.BitVec n) : evalList ([] : List (Literal n)) x = false := by
  unfold evalList
  simp

@[simp] lemma evalList_singleton (ℓ : Literal n) (x : Core.BitVec n) :
    evalList [ℓ] x = Literal.holds ℓ x := by
  unfold evalList
  simp

/-- Значение клаузы на входе `x`.  Используем `List.any`, который
    возвращает `true`, если хотя бы один литерал удовлетворён. -/
@[simp] def eval (C : Clause n) (x : Core.BitVec n) : Bool :=
  evalList C.lits x

/-- Результат ограничения клаузы подкубом: `satisfied` означает, что
    дизъюнкция стала тождественно истинной; `falsified` — тождественно
    ложной; `pending lits` — клауза, зависящая только от оставшихся
    литералов. -/
inductive RestrictResult (n : Nat)
| satisfied : RestrictResult n
| falsified : RestrictResult n
| pending   : List (Literal n) → RestrictResult n
  deriving Repr

namespace RestrictResult

variable {n : Nat}

@[simp] def toClause : RestrictResult n → Option (Clause n)
  | RestrictResult.satisfied    => none
  | RestrictResult.falsified    => some ⟨[]⟩
  | RestrictResult.pending lits => some ⟨lits⟩

end RestrictResult

/-- Вспомогательная функция, реализующая ограничение списка литералов. -/
private def restrictList (β : Subcube n) :
    List (Literal n) → RestrictResult n
  | [] => RestrictResult.falsified
  | ℓ :: rest =>
    match β ℓ.idx with
    | some b =>
        if b = ℓ.val then
          RestrictResult.satisfied
        else
          restrictList β rest
    | none =>
        match restrictList β rest with
        | RestrictResult.satisfied => RestrictResult.satisfied
        | RestrictResult.falsified => RestrictResult.pending [ℓ]
        | RestrictResult.pending L => RestrictResult.pending (ℓ :: L)

/-- Ограничение клаузы подкубом. -/
@[simp] def restrict (C : Clause n) (β : Subcube n) : RestrictResult n :=
  restrictList (β := β) C.lits

namespace RestrictResult

variable {n : Nat}

/-- Интерпретация результата ограничения: для удовлетворённой/опровержённой
    клаузы возвращаем константы, в противном случае оцениваем остаток. -/
@[simp] def eval (res : RestrictResult n) (x : Core.BitVec n) : Bool :=
  match res with
  | RestrictResult.satisfied => true
  | RestrictResult.falsified => false
  | RestrictResult.pending lits => Clause.evalList lits x

end RestrictResult

/-- Если ограничение клаузы даёт `satisfied`, её оценка становится `true`. -/
lemma restrict_eval_satisfied {C : Clause n} {β : Subcube n} {x : Core.BitVec n}
    (h : Clause.restrict C β = Clause.RestrictResult.satisfied) :
    Clause.RestrictResult.eval (Clause.restrict C β) x = true := by
  rw [h]
  simp [Clause.RestrictResult.eval]

/-- Если ограничение клаузы даёт `falsified`, её оценка становится `false`. -/
lemma restrict_eval_falsified {C : Clause n} {β : Subcube n} {x : Core.BitVec n}
    (h : Clause.restrict C β = Clause.RestrictResult.falsified) :
    Clause.RestrictResult.eval (Clause.restrict C β) x = false := by
  rw [h]
  simp [Clause.RestrictResult.eval]

/-- В случае ветки `pending` оценка клаузы совпадает с оценкой остатка. -/
lemma restrict_eval_pending {C : Clause n} {β : Subcube n} {x : Core.BitVec n}
    {lits : List (Literal n)}
    (h : Clause.restrict C β = Clause.RestrictResult.pending lits) :
    Clause.RestrictResult.eval (Clause.restrict C β) x = Clause.eval ⟨lits⟩ x := by
  rw [h]
  simp [Clause.RestrictResult.eval]

/--
  При ограничении дизъюнктивной клаузы длина оставшегося хвоста не превосходит
  исходного числа литералов.  Это свойство пригодится позже, когда будем
  отслеживать, как сужение влияет на ширину формулы: в ветке `pending` мы
  только удаляем литералы.
-/
lemma restrict_pending_length_le {C : Clause n} {β : Subcube n}
    {lits : List (Literal n)}
    (h : Clause.restrict C β = Clause.RestrictResult.pending lits) :
    lits.length ≤ C.lits.length := by
  classical
  -- Обобщаем утверждение до произвольного списка литералов, чтобы провести
  -- индукцию по `restrictList`.
  have hlist :
      ∀ input : List (Literal n),
        match restrictList (β := β) input with
        | Clause.RestrictResult.pending pending => pending.length ≤ input.length
        | Clause.RestrictResult.satisfied => True
        | Clause.RestrictResult.falsified => True := by
    intro input
    induction input with
    | nil =>
        simp [restrictList]
    | cons ℓ rest ih =>
        cases hβ : β ℓ.idx with
        | some b =>
            by_cases hb : b = ℓ.val
            · cases hrest : restrictList (β := β) rest with
              | satisfied =>
                  simp [restrictList, hβ, hb, hrest]
              | falsified =>
                  simp [restrictList, hβ, hb, hrest]
              | pending L =>
                  have ihlen : L.length ≤ rest.length := by
                    simpa [hrest] using ih
                  have hsucc : (ℓ :: L).length ≤ (ℓ :: rest).length := by
                    simpa [List.length_cons] using Nat.succ_le_succ ihlen
                  simpa [restrictList, hβ, hb, hrest, List.length_cons] using hsucc
            ·
                -- Ограничение переходит целиком в хвост; длина не увеличивается.
                cases hrest : restrictList (β := β) rest with
                | satisfied =>
                    simp [restrictList, hβ, hb, hrest]
                | falsified =>
                    simp [restrictList, hβ, hb, hrest]
                | pending L =>
                    have ihlen : L.length ≤ rest.length := by
                      simpa [hrest] using ih
                    have hsucc : L.length ≤ (ℓ :: rest).length := by
                      have hlen_cons : rest.length ≤ (ℓ :: rest).length := by
                        simp [List.length_cons]
                      exact ihlen.trans hlen_cons
                    simpa [restrictList, hβ, hb, hrest, List.length_cons] using hsucc
        | none =>
            cases hrest : restrictList (β := β) rest with
            | satisfied =>
                simp [restrictList, hβ, hrest]
            | falsified =>
                simp [restrictList, hβ, hrest]
            | pending L =>
                have ihlen : L.length ≤ rest.length := by
                  simpa [hrest] using ih
                have hsucc : (ℓ :: L).length ≤ (ℓ :: rest).length := by
                  simpa [List.length_cons] using Nat.succ_le_succ ihlen
                simpa [restrictList, hβ, hrest, List.length_cons] using hsucc
  have hmatch := hlist C.lits
  have hpending : restrictList (β := β) C.lits
      = Clause.RestrictResult.pending lits := by
    simpa [Clause.restrict] using h
  simpa [Clause.restrict, hpending] using hmatch

/--
  Ограничение клаузы корректно «забывает» фиксированные переменные:
  если точка `x` совместима с подкубом `β`, то значение исходной клаузы
  на `x` совпадает со значением результата ограничения.  Лемма доказывается
  по индукции по списку литералов и аккуратно разбирает все случаи из
  определения `Clause.restrictList`.
-/
lemma restrict_eval_mem (C : Clause n) (β : Subcube n) {x : Core.BitVec n}
    (hx : mem β x) :
    Clause.RestrictResult.eval (Clause.restrict C β) x = Clause.eval C x := by
  classical
  -- Рабочая индуктивная формула для списков литералов.
  have hlist :
      ∀ lits : List (Literal n),
        Clause.RestrictResult.eval (restrictList (β := β) lits) x
          = Clause.evalList lits x := by
    -- Инициализация по списку литералов.
    refine List.rec ?hbase ?hstep
    · -- Пустая клауза после ограничения всегда ложна.
      simp [Clause.evalList, restrictList]
    · intro ℓ rest ih
      -- Свойство совместимости `x` с подкубом.
      have hmem := (mem_iff (β := β) (x := x)).mp hx
      -- Разбираем значение подкуба на координате `ℓ.idx`.
      cases hβ : β ℓ.idx with
      | none =>
          -- Координата свободна: рекурсивно переходим к хвосту.
          -- Сохраняем индуктивное предположение.
          have htail := ih
          -- Вспомогательная переменная — результат ограничения хвоста.
          cases hres : restrictList (β := β) rest with
          | satisfied =>
              have hrest : Clause.evalList rest x = true := by
                simpa [Clause.RestrictResult.eval, hres] using htail
              have hrest_any :
                  rest.any (fun t => Literal.holds t x) = true := by
                simpa [Clause.evalList] using hrest
              obtain ⟨ℓ', hmem', hh⟩ := List.any_eq_true.mp hrest_any
              have hcons_true : Clause.evalList (ℓ :: rest) x = true := by
                refine List.any_eq_true.mpr ?_
                exact ⟨ℓ', List.mem_cons.mpr (Or.inr hmem'), hh⟩
              calc
                Clause.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                    = true := by
                      simp [Clause.RestrictResult.eval, restrictList, hβ, hres]
                _ = Clause.evalList (ℓ :: rest) x := hcons_true.symm
          | falsified =>
              have hrest_false : Clause.evalList rest x = false := by
                simpa [Clause.RestrictResult.eval, hres] using htail
              have hrestrict :
                  Clause.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                    = Clause.evalList [ℓ] x := by
                simp [Clause.RestrictResult.eval, restrictList, hβ, hres]
              have hsingle : Clause.evalList [ℓ] x = Literal.holds ℓ x := by
                simpa using (Clause.evalList_singleton (ℓ := ℓ) (x := x))
              have hcons :
                  Clause.evalList (ℓ :: rest) x
                    = (Literal.holds ℓ x || Clause.evalList rest x) := by
                simp [Clause.evalList, List.any_cons, Literal.holds]
              have hgoal :
                  Clause.evalList (ℓ :: rest) x = Clause.evalList [ℓ] x := by
                calc
                  Clause.evalList (ℓ :: rest) x
                      = (Literal.holds ℓ x || Clause.evalList rest x) := hcons
                  _ = Literal.holds ℓ x := by
                        rw [hrest_false, Bool.or_false]
                  _ = Clause.evalList [ℓ] x := by
                        simp [hsingle]
              exact hrestrict.trans hgoal.symm
          | pending L =>
              have hrest : Clause.evalList L x = Clause.evalList rest x := by
                simpa [Clause.RestrictResult.eval, hres] using htail
              have hleft :
                  Clause.evalList (ℓ :: L) x
                    = (Literal.holds ℓ x || Clause.evalList L x) := by
                simp [Clause.evalList, List.any_cons, Literal.holds]
              have hright :
                  Clause.evalList (ℓ :: rest) x
                    = (Literal.holds ℓ x || Clause.evalList rest x) := by
                simp [Clause.evalList, List.any_cons, Literal.holds]
              calc
                Clause.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                    = Clause.evalList (ℓ :: L) x := by
                      simp [Clause.RestrictResult.eval, restrictList, hβ, hres]
                _ = Clause.evalList (ℓ :: rest) x := by
                      calc
                        Clause.evalList (ℓ :: L) x
                            = (Literal.holds ℓ x || Clause.evalList L x) := hleft
                        _ = (Literal.holds ℓ x || Clause.evalList rest x) := by
                              rw [hrest]
                        _ = Clause.evalList (ℓ :: rest) x := hright.symm
      | some b =>
          -- Координата фиксирована, выражаем значение `x` через условие `mem`.
          have hxval : x ℓ.idx = b := hmem ℓ.idx b hβ
          by_cases hb : b = ℓ.val
          · -- Литерал удовлетворён ⇒ клауза истинна.
            calc
              Clause.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                  = true := by
                    simp [Clause.RestrictResult.eval, Clause.evalList,
                      List.any_cons, Literal.holds, restrictList, hβ, hxval, hb]
              _ = Clause.evalList (ℓ :: rest) x := by
                    simp [Clause.evalList, List.any_cons, Literal.holds,
                      hxval, hb]
          · -- Литерал ложен ⇒ переходим к хвосту.
            have htail := ih
            simpa [Clause.evalList, List.any_cons, Literal.holds, restrictList,
              hβ, hxval, hb] using htail
  -- Применяем полученную формулу к списку `C.lits`.
  simpa [Clause.eval, Clause.restrict] using hlist C.lits

end Clause

/-! ### Термы (конъюнкции литералов) -/

/-- Терм в ДНФ: конъюнкция литералов. -/
structure Term (n : Nat) where
  lits : List (Literal n)
  deriving DecidableEq, Repr

namespace Term

variable {n : Nat}

/-- Значение терма на входе `x`: все литералы должны выполняться. -/
@[simp] def eval (T : Term n) (x : Core.BitVec n) : Bool :=
  T.lits.all (fun ℓ => Literal.holds ℓ x)

/-- Удобное разложение значения конъюнкции на головной литерал и хвост. -/
@[simp] lemma eval_cons (ℓ : Literal n) (rest : List (Literal n))
    (x : Core.BitVec n) :
    Term.eval ⟨ℓ :: rest⟩ x
      = (Literal.holds ℓ x && Term.eval ⟨rest⟩ x) := by
  simp [Term.eval, List.all_cons]

/-- Частный случай — терм, состоящий из одного литерала. -/
@[simp] lemma eval_singleton (ℓ : Literal n) (x : Core.BitVec n) :
    Term.eval ⟨[ℓ]⟩ x = Literal.holds ℓ x := by
  simp [Term.eval]

/-- Результат ограничения терма: `satisfied` — терм стал тождественно
    истинным; `falsified` — ложным; `pending lits` — остаточный терм. -/
inductive RestrictResult (n : Nat)
| satisfied : RestrictResult n
| falsified : RestrictResult n
| pending   : List (Literal n) → RestrictResult n
  deriving Repr

namespace RestrictResult

variable {n : Nat}

@[simp] def toTerm : RestrictResult n → Option (Term n)
  | RestrictResult.satisfied    => some ⟨[]⟩
  | RestrictResult.falsified    => none
  | RestrictResult.pending lits => some ⟨lits⟩

end RestrictResult

private def restrictList (β : Subcube n) :
    List (Literal n) → RestrictResult n
  | [] => RestrictResult.satisfied
  | ℓ :: rest =>
    match β ℓ.idx with
    | some b =>
        if b = ℓ.val then
          restrictList β rest
        else
          RestrictResult.falsified
    | none =>
        match restrictList β rest with
        | RestrictResult.satisfied =>
            -- Литерал остаётся «живым»: переносим его в хвост, чтобы
            -- сохранить зависимость терма от свободной переменной.
            RestrictResult.pending [ℓ]
        | RestrictResult.falsified => RestrictResult.falsified
        | RestrictResult.pending L => RestrictResult.pending (ℓ :: L)

@[simp] def restrict (T : Term n) (β : Subcube n) : RestrictResult n :=
  restrictList (β := β) T.lits

namespace RestrictResult

variable {n : Nat}

/-- Интерпретация результата ограничения для термов. -/
@[simp] def eval (res : RestrictResult n) (x : Core.BitVec n) : Bool :=
  match res with
  | RestrictResult.satisfied => true
  | RestrictResult.falsified => false
  | RestrictResult.pending lits => Term.eval ⟨lits⟩ x

end RestrictResult

/-- В ветке `satisfied` ограниченный терм тождественно истинен. -/
lemma restrict_eval_satisfied {T : Term n} {β : Subcube n} {x : Core.BitVec n}
    (h : Term.restrict T β = Term.RestrictResult.satisfied) :
    Term.RestrictResult.eval (Term.restrict T β) x = true := by
  simpa [Term.RestrictResult.eval] using
    congrArg (fun res => Term.RestrictResult.eval res x) h

/-- В ветке `falsified` ограниченный терм тождественно ложен. -/
lemma restrict_eval_falsified {T : Term n} {β : Subcube n} {x : Core.BitVec n}
    (h : Term.restrict T β = Term.RestrictResult.falsified) :
    Term.RestrictResult.eval (Term.restrict T β) x = false := by
  simpa [Term.RestrictResult.eval] using
    congrArg (fun res => Term.RestrictResult.eval res x) h

/-- В ветке `pending` оценка ограниченного терма совпадает с хвостом. -/
lemma restrict_eval_pending {T : Term n} {β : Subcube n} {x : Core.BitVec n}
    {lits : List (Literal n)}
    (h : Term.restrict T β = Term.RestrictResult.pending lits) :
    Term.RestrictResult.eval (Term.restrict T β) x = Term.eval ⟨lits⟩ x := by
  simpa [Term.RestrictResult.eval] using
    congrArg (fun res => Term.RestrictResult.eval res x) h

/--
  При ограничении терма ветка `pending` лишь удаляет фиксированные литералы,
  поэтому длина получившегося списка не превосходит исходной.  Это простой,
  но полезный инвариант для будущих оценок ширины.
-/
lemma restrict_pending_length_le {T : Term n} {β : Subcube n}
    {lits : List (Literal n)}
    (h : Term.restrict T β = Term.RestrictResult.pending lits) :
    lits.length ≤ T.lits.length := by
  classical
  have hlist :
      ∀ input : List (Literal n),
        match restrictList (β := β) input with
        | Term.RestrictResult.pending pending => pending.length ≤ input.length
        | Term.RestrictResult.satisfied => True
        | Term.RestrictResult.falsified => True := by
    intro input
    induction input with
    | nil =>
        simp [restrictList]
    | cons ℓ rest ih =>
        cases hβ : β ℓ.idx with
        | some b =>
            by_cases hb : b = ℓ.val
            ·
                cases hrest : restrictList (β := β) rest with
                | satisfied =>
                    simp [restrictList, hβ, hb, hrest]
                | falsified =>
                    simp [restrictList, hβ, hb, hrest]
                | pending L =>
                    have ihlen : L.length ≤ rest.length := by
                      simpa [hrest] using ih
                    have hsucc : L.length ≤ (ℓ :: rest).length := by
                      have hlen_cons : rest.length ≤ (ℓ :: rest).length := by
                        simp [List.length_cons]
                      exact ihlen.trans hlen_cons
                    simpa [restrictList, hβ, hb, hrest, List.length_cons] using hsucc
            ·
                cases hrest : restrictList (β := β) rest with
                | satisfied =>
                    simp [restrictList, hβ, hb, hrest]
                | falsified =>
                    simp [restrictList, hβ, hb, hrest]
                | pending L =>
                    have ihlen : L.length ≤ rest.length := by
                      simpa [hrest] using ih
                    have hsucc : L.length ≤ (ℓ :: rest).length := by
                      have hlen_cons : rest.length ≤ (ℓ :: rest).length := by
                        simp [List.length_cons]
                      exact ihlen.trans hlen_cons
                    simpa [restrictList, hβ, hb, hrest, List.length_cons] using hsucc
        | none =>
            cases hrest : restrictList (β := β) rest with
            | satisfied =>
                simp [restrictList, hβ, hrest]
            | falsified =>
                simp [restrictList, hβ, hrest]
            | pending L =>
                have ihlen : L.length ≤ rest.length := by
                  simpa [hrest] using ih
                have hsucc : (ℓ :: L).length ≤ (ℓ :: rest).length := by
                  simpa [List.length_cons] using Nat.succ_le_succ ihlen
                simpa [restrictList, hβ, hrest, List.length_cons] using hsucc
  have hmatch := hlist T.lits
  have hpending : restrictList (β := β) T.lits
      = Term.RestrictResult.pending lits := by
    simpa [Term.restrict] using h
  simpa [Term.restrict, hpending] using hmatch

/--
  Ограничение терма сохраняет его значение на совместимых точках.
  Логика полностью аналогична дизъюнктивному случаю: свободные
  литералы переезжают в хвост `pending`, а фиксированные — либо
  замыкают терм в `falsified`, либо сводят его к хвосту.  Мы
  аккуратно разбираем все ветви рекурсивного определения и
  используем совместимость точки `x` с подкубом `β`.
-/
lemma restrict_eval_mem (T : Term n) (β : Subcube n) {x : Core.BitVec n}
    (hx : mem β x) :
    Term.RestrictResult.eval (Term.restrict T β) x = Term.eval T x := by
  classical
  -- Индукция по списку литералов, определяющих терм.
  have hlist :
      ∀ lits : List (Literal n),
        Term.RestrictResult.eval (restrictList (β := β) lits) x
          = Term.eval ⟨lits⟩ x := by
    refine List.rec ?hbase ?hstep
    · -- Пустая конъюнкция всегда истинна, ограничение совпадает.
      simp [Term.eval, restrictList]
    · intro ℓ rest ih
      -- Совместимость точки с подкубом даёт нам значение `x ℓ.idx`.
      have hmem := (mem_iff (β := β) (x := x)).mp hx
      -- Анализируем ветвление `restrictList` по значению маски `β`.
      cases hβ : β ℓ.idx with
      | none =>
          -- Переменная свободна — рекурсия сводится к хвосту.
          have htail := ih
          -- Разбираем результат ограничения хвоста.
          cases hres : restrictList (β := β) rest with
          | satisfied =>
              -- Хвост уже истинен, поэтому терм эквивалентен одиночному литералу.
              have hrest : Term.eval ⟨rest⟩ x = true := by
                simpa [Term.RestrictResult.eval, hres] using htail
              have hresult :
                  restrictList (β := β) (ℓ :: rest)
                    = Term.RestrictResult.pending [ℓ] := by
                simp [restrictList, hβ, hres]
              have hleft_literal :
                  Term.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                    = Literal.holds ℓ x := by
                simp [hresult, Term.RestrictResult.eval, Term.eval_singleton]
              have hcons_literal :
                  Term.eval ⟨ℓ :: rest⟩ x = Literal.holds ℓ x := by
                calc
                  Term.eval ⟨ℓ :: rest⟩ x
                      = (Literal.holds ℓ x && Term.eval ⟨rest⟩ x) := by
                          simp [Term.eval_cons]
                  _ = (Literal.holds ℓ x && true) := by
                          rw [hrest]
                  _ = Literal.holds ℓ x := by simp
              exact hleft_literal.trans hcons_literal.symm
          | falsified =>
              -- Хвост уже противоречив, значение всего терма — `false`.
              have hrest : Term.eval ⟨rest⟩ x = false := by
                simpa [Term.RestrictResult.eval, hres] using htail
              have hleftFalse :
                  Term.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                    = false := by
                simp [Term.RestrictResult.eval, restrictList, hβ, hres]
              have hconsFalse : Term.eval ⟨ℓ :: rest⟩ x = false := by
                calc
                  Term.eval ⟨ℓ :: rest⟩ x
                      = (Literal.holds ℓ x && Term.eval ⟨rest⟩ x) := by
                          simp [Term.eval_cons]
                  _ = (Literal.holds ℓ x && false) := by
                          rw [hrest]
                  _ = false := by simp
              exact hleftFalse.trans hconsFalse.symm
          | pending L =>
              -- Хвост сохранил несколько свободных литералов, переносим равенство.
              have hrest : Term.eval ⟨L⟩ x = Term.eval ⟨rest⟩ x := by
                simpa [Term.RestrictResult.eval, hres] using htail
              have hleft :
                  Term.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                    = Term.eval ⟨ℓ :: L⟩ x := by
                simp [Term.RestrictResult.eval, restrictList, hβ, hres]
              have hswap_bool :
                  (Literal.holds ℓ x && Term.eval ⟨L⟩ x)
                    = (Literal.holds ℓ x && Term.eval ⟨rest⟩ x) := by
                simpa using congrArg (fun b => Literal.holds ℓ x && b) hrest
              have hswap : Term.eval ⟨ℓ :: L⟩ x = Term.eval ⟨ℓ :: rest⟩ x := by
                simpa [Term.eval_cons] using hswap_bool
              exact hleft.trans hswap
      | some b =>
          -- Переменная фиксирована; совместимость `x` с `β` даёт точное значение.
          have hxval : x ℓ.idx = b := hmem ℓ.idx b hβ
          by_cases hb : b = ℓ.val
          · -- Литерал подтверждён ограничением, терм сводится к хвосту.
            have htail := ih
            have hxholds : Literal.holds ℓ x = true := by
              simp [Literal.holds, hxval, hb]
            have hleft :
                Term.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                  = Term.RestrictResult.eval (restrictList (β := β) rest) x := by
              simp [restrictList, hβ, hxval, hb]
            have hright :
                Term.eval ⟨ℓ :: rest⟩ x = Term.eval ⟨rest⟩ x := by
              calc
                Term.eval ⟨ℓ :: rest⟩ x
                    = (Literal.holds ℓ x && Term.eval ⟨rest⟩ x) := by
                        simp [Term.eval_cons]
                _ = (true && Term.eval ⟨rest⟩ x) := by
                        simp [Literal.holds, hxval, hb]
                _ = Term.eval ⟨rest⟩ x := by simp
            calc
              Term.RestrictResult.eval (restrictList (β := β) (ℓ :: rest)) x
                  = Term.RestrictResult.eval (restrictList (β := β) rest) x := hleft
              _ = Term.eval ⟨rest⟩ x := htail
              _ = Term.eval ⟨ℓ :: rest⟩ x := hright.symm
          · -- Ограничение противоречит литералу — терм ложен.
            have hxholds : Literal.holds ℓ x = false := by
              simp [Literal.holds, hxval, hb]
            simp [Term.eval_cons, Literal.holds, hxholds, restrictList,
              hβ, hxval, hb]
  -- Применяем полученную формулу к списку литералов исходного терма.
  simpa [Term.eval, Term.restrict] using hlist T.lits

end Term

/-! ### Полные формулы -/

/-- КНФ-формула как список клауз. -/
structure CNF (n : Nat) where
  clauses : List (Clause n)
  deriving Repr

/-- ДНФ-формула как список термов. -/
structure DNF (n : Nat) where
  terms : List (Term n)
  deriving Repr

namespace CNF

variable {n : Nat}

@[simp] def eval (F : CNF n) (x : Core.BitVec n) : Bool :=
  F.clauses.all (fun C => Clause.eval C x)

/-- Конъюнкция пустого списка клауз тождественно истинна. -/
@[simp] lemma eval_nil (x : Core.BitVec n) :
    eval (n := n) ⟨[]⟩ x = true := by
  simp [eval]

/-- Удобная форма раскрытия головной клаузы в конъюнкции. -/
@[simp] lemma eval_cons (C : Clause n) (rest : List (Clause n))
    (x : Core.BitVec n) :
    eval (n := n) ⟨C :: rest⟩ x
      = (Clause.eval C x && eval (n := n) ⟨rest⟩ x) := by
  simp [eval, List.all_cons]

/-- Оценка CNF после поклаузного ограничения: для каждой клаузы
    используем уже построенный `Clause.restrict`. -/
@[simp] def restrictEval (F : CNF n) (β : Subcube n) (x : Core.BitVec n) : Bool :=
  F.clauses.all (fun C => Clause.RestrictResult.eval (Clause.restrict C β) x)

/-- Совместимые точки оценивают ограниченную CNF так же, как исходную. -/
lemma restrictEval_eq_eval (F : CNF n) (β : Subcube n) {x : Core.BitVec n}
    (hx : mem β x) :
    restrictEval F β x = eval F x := by
  cases F with
  | mk clauses =>
      have hpointwise :
          ∀ C ∈ clauses,
            Clause.RestrictResult.eval (Clause.restrict C β) x = Clause.eval C x := by
        intro C hC
        exact Clause.restrict_eval_mem (C := C) (β := β) (x := x) hx
      simpa [restrictEval, eval] using
        List.all_congr (l := clauses)
          (p := fun C => Clause.RestrictResult.eval (Clause.restrict C β) x)
          (q := fun C => Clause.eval C x) hpointwise

end CNF

namespace DNF

variable {n : Nat}

@[simp] def eval (F : DNF n) (x : Core.BitVec n) : Bool :=
  F.terms.any (fun T => Term.eval T x)

/-- Пустая дизъюнкция термов всегда ложна. -/
@[simp] lemma eval_nil (x : Core.BitVec n) :
    eval (n := n) ⟨[]⟩ x = false := by
  simp [eval]

/-- Разбор головного терма в дизъюнкции: удобно применять при индукциях. -/
@[simp] lemma eval_cons (T : Term n) (rest : List (Term n))
    (x : Core.BitVec n) :
    eval (n := n) ⟨T :: rest⟩ x
      = (Term.eval T x || eval (n := n) ⟨rest⟩ x) := by
  simp [eval, List.any_cons]

/-- Одноэлементная дизъюнкция просто повторяет значение терма. -/
@[simp] lemma eval_singleton (T : Term n) (x : Core.BitVec n) :
    eval (n := n) ⟨[T]⟩ x = Term.eval T x := by
  simp [eval]

/-- Оценка DNF после почленного ограничения по термам. -/
@[simp] def restrictEval (F : DNF n) (β : Subcube n) (x : Core.BitVec n) : Bool :=
  F.terms.any (fun T => Term.RestrictResult.eval (Term.restrict T β) x)

/-- Совместимые точки оценивают ограниченную DNF так же, как исходную. -/
lemma restrictEval_eq_eval (F : DNF n) (β : Subcube n) {x : Core.BitVec n}
    (hx : mem β x) :
    restrictEval F β x = eval F x := by
  cases F with
  | mk terms =>
      have hpointwise :
          ∀ T ∈ terms,
            Term.RestrictResult.eval (Term.restrict T β) x = Term.eval T x := by
        intro T hT
        exact Term.restrict_eval_mem (T := T) (β := β) (x := x) hx
      simpa [restrictEval, eval] using
        List.any_congr (l := terms)
          (p := fun T => Term.RestrictResult.eval (Term.restrict T β) x)
          (q := fun T => Term.eval T x) hpointwise

end DNF

end AC0
end Pnp3
