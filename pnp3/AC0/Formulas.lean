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

/-- Перевод литерала AC⁰ в основной `Core`-формат. -/
@[simp] def toCore (ℓ : Literal n) : Core.Literal n :=
  ⟨ℓ.idx, ℓ.val⟩

/-- Обратное преобразование из core-литерала. -/
@[simp] def ofCore (ℓ : Core.Literal n) : Literal n :=
  ⟨ℓ.idx, ℓ.value⟩

@[simp] lemma toCore_ofCore (ℓ : Core.Literal n) :
    toCore (ofCore (n := n) ℓ) = ℓ := by
  cases ℓ
  rfl

@[simp] lemma ofCore_toCore (ℓ : Literal n) :
    ofCore (n := n) (toCore (n := n) ℓ) = ℓ := by
  cases ℓ
  rfl

@[simp] lemma toCore_idx (ℓ : Literal n) : (toCore (n := n) ℓ).idx = ℓ.idx := rfl

@[simp] lemma toCore_value (ℓ : Literal n) : (toCore (n := n) ℓ).value = ℓ.val := rfl

/-- Core-оценка литерала, полученного из AC⁰-представления, совпадает с `holds`. -/
@[simp] lemma toCore_eval (ℓ : Literal n) (x : Core.BitVec n) :
    (toCore (n := n) ℓ).eval x = holds ℓ x := by
  classical
  simp [toCore, holds, Core.Literal.eval]

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

/-- Ширина клаузы — число литералов в списке `lits`.  Этим определением мы
    будем пользоваться при переносе AC⁰-клауз в core-представление: ширина
    не меняется при отображении `map Literal.toCore`. -/
@[simp] def width (C : Clause n) : Nat := C.lits.length

/-- Перевод AC⁰-клаузы в формат `Core.CnfClause`. -/
@[simp] def toCore (C : Clause n)
    (hnodup : (C.lits.map (·.idx)).Nodup) : Core.CnfClause n :=
  { literals := C.lits.map Literal.toCore
    nodupIdx := by
      simpa [List.map_map, Literal.toCore_idx] using hnodup }

@[simp] lemma toCore_literals (C : Clause n)
    (hnodup : (C.lits.map (·.idx)).Nodup) :
    (toCore (n := n) C hnodup).literals = C.lits.map Literal.toCore := rfl

/-- Ширина core-клаузы, полученной из AC⁰-клаузы, совпадает с длиной исходного
    списка литералов. -/
@[simp] lemma toCore_width (C : Clause n)
    (hnodup : (C.lits.map (·.idx)).Nodup) :
    (Clause.toCore (n := n) C hnodup).width = C.width := by
  simp [Clause.width, Core.CnfClause.width, Clause.toCore]

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

/-- Оценка core-клаузы, полученной из AC⁰-клаузы, совпадает с исходной функцией. -/
@[simp] lemma toCore_eval (C : Clause n)
    (hnodup : (C.lits.map (·.idx)).Nodup) (x : Core.BitVec n) :
    (Clause.toCore (n := n) C hnodup).eval x = Clause.eval C x := by
  classical
  have hfun : ∀ ℓ ∈ C.lits,
      ((fun ℓ' : Core.Literal n => ℓ'.eval x) ∘ Literal.toCore (n := n)) ℓ
        = Literal.holds ℓ x := by
    intro ℓ hℓ
    simp [Function.comp, Literal.toCore_eval]
  have hAny := List.any_congr (l := C.lits) hfun
  simpa [Clause.toCore, Clause.eval, Clause.evalList, Core.CnfClause.eval,
    List.any_map] using hAny

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

/--
  Вспомогательная функция: преобразует список AC⁰-клауз в список core-клауз,
  поддерживая доказательства ограничений на ширину и отсутствие повторяющихся
  индексов.  Реализация устроена рекурсивно, чтобы избежать явного использования
  `List.attach` и всегда иметь под рукой свидетельство принадлежности текущей
  клаузы исходному списку.
-/
private def toCoreClausesAux (w : Nat)
    : ∀ (clauses : List (Clause n)),
        (∀ C ∈ clauses, Clause.width C ≤ w) →
        (∀ C ∈ clauses, (C.lits.map (·.idx)).Nodup) →
        List (Core.CnfClause n)
  | [], _, _ => []
  | C :: rest, hwidth, hnodup =>
      Clause.toCore (n := n) C (hnodup C (by simp))
        :: toCoreClausesAux w rest
            (fun D hD => hwidth D (by simp [List.mem_cons, hD]))
            (fun D hD => hnodup D (by simp [List.mem_cons, hD]))

@[simp] lemma toCoreClausesAux_nil (w : Nat)
    (hwidth : ∀ C ∈ ([] : List (Clause n)), Clause.width C ≤ w)
    (hnodup : ∀ C ∈ ([] : List (Clause n)), (C.lits.map (·.idx)).Nodup) :
    toCoreClausesAux (n := n) w [] hwidth hnodup = [] := rfl

@[simp] lemma toCoreClausesAux_cons (w : Nat) (C : Clause n)
    (rest : List (Clause n))
    (hwidth : ∀ D ∈ C :: rest, Clause.width D ≤ w)
    (hnodup : ∀ D ∈ C :: rest, (D.lits.map (·.idx)).Nodup) :
    toCoreClausesAux (n := n) w (C :: rest) hwidth hnodup
      = Clause.toCore (n := n) C (hnodup C (by simp))
          :: toCoreClausesAux (n := n) w rest
              (fun D hD => hwidth D (by simp [List.mem_cons, hD]))
              (fun D hD => hnodup D (by simp [List.mem_cons, hD])) := rfl

/--
  Любой элемент списка core-клауз, полученного функцией `toCoreClausesAux`, имеет
  ширину, не превосходящую заданного порога `w`.
-/
lemma toCoreClausesAux_mem_width (w : Nat)
    (clauses : List (Clause n))
    (hwidth : ∀ C ∈ clauses, Clause.width C ≤ w)
    (hnodup : ∀ C ∈ clauses, (C.lits.map (·.idx)).Nodup)
    {C : Core.CnfClause n}
    (hC : C ∈ toCoreClausesAux (n := n) w clauses hwidth hnodup) :
    C.width ≤ w := by
  classical
  induction clauses generalizing C with
  | nil => cases hC
  | cons C₀ rest ih =>
      have hwidth_tail : ∀ D ∈ rest, Clause.width D ≤ w := by
        intro D hD
        exact hwidth D (by simp [List.mem_cons, hD])
      have hnodup_tail : ∀ D ∈ rest, (D.lits.map (·.idx)).Nodup := by
        intro D hD
        exact hnodup D (by simp [List.mem_cons, hD])
      simp [toCoreClausesAux, hwidth_tail, hnodup_tail] at hC
      rcases hC with hC | hC
      · subst hC
        simpa [Clause.toCore_width]
          using hwidth C₀ (by simp : C₀ ∈ C₀ :: rest)
      · exact ih hwidth_tail hnodup_tail hC

/--
  После преобразования в core-представление оценка списка клауз через `List.all`
  совпадает с исходной AC⁰-оценкой.
-/
lemma toCoreClausesAux_all_eval (w : Nat)
    (clauses : List (Clause n))
    (hwidth : ∀ C ∈ clauses, Clause.width C ≤ w)
    (hnodup : ∀ C ∈ clauses, (C.lits.map (·.idx)).Nodup)
    (x : Core.BitVec n) :
    List.all (toCoreClausesAux (n := n) w clauses hwidth hnodup)
        (fun C => Core.CnfClause.eval C x)
      = List.all clauses (fun C => Clause.eval C x) := by
  classical
  induction clauses with
  | nil => simp [toCoreClausesAux]
  | cons C rest ih =>
      have hwidth_tail : ∀ D ∈ rest, Clause.width D ≤ w := by
        intro D hD
        exact hwidth D (by simp [List.mem_cons, hD])
      have hnodup_tail : ∀ D ∈ rest, (D.lits.map (·.idx)).Nodup := by
        intro D hD
        exact hnodup D (by simp [List.mem_cons, hD])
      -- Раскрываем определение `toCoreClausesAux` и переводим обе стороны к
      -- явной форме через головной элемент и хвост.
      change
        List.all
            (Clause.toCore (n := n) C (hnodup C (by simp))
              :: toCoreClausesAux (n := n) w rest
                (fun D hD => hwidth D (by simp [List.mem_cons, hD]))
                (fun D hD => hnodup D (by simp [List.mem_cons, hD])))
            (fun C => Core.CnfClause.eval C x)
          =
            (Clause.eval C x && List.all rest (fun C => Clause.eval C x))
      have hheadEval :
          Core.CnfClause.eval
              (Clause.toCore (n := n) C (hnodup C (by simp))) x
            = Clause.eval C x := by
        simpa using Clause.toCore_eval (n := n) (C := C)
          (hnodup := hnodup C (by simp [List.mem_cons])) (x := x)
      -- Эксплицитно переписываем оценку головы через `List.any`, чтобы
      -- сопоставить функции в `List.all_cons` по обе стороны равенства.
      have hheadAny :
          C.lits.any
              (((fun ℓ : Core.Literal n => decide (x ℓ.idx = ℓ.value))
                  ∘ Literal.toCore (n := n)))
            = C.lits.any (fun ℓ => Literal.holds ℓ x) := by
        simpa [Clause.eval, Clause.evalList, Literal.holds, Function.comp,
          Clause.toCore, Core.CnfClause.eval, Core.Literal.eval, List.any_map]
          using hheadEval
      have htailEval :
          List.all
              (toCoreClausesAux (n := n) w rest
                (fun D hD => hwidth D (by simp [List.mem_cons, hD]))
                (fun D hD => hnodup D (by simp [List.mem_cons, hD])))
              (fun C => Core.CnfClause.eval C x)
            = List.all rest (fun C => Clause.eval C x) :=
        ih hwidth_tail hnodup_tail
      -- Аналогично переписываем хвост в терминах `List.any`, чтобы
      -- сопоставить обобщённую оценку `htailEval` с нужным выражением.
      have htailAny :
          List.all
              (toCoreClausesAux (n := n) w rest
                (fun D hD => hwidth D (by simp [List.mem_cons, hD]))
                (fun D hD => hnodup D (by simp [List.mem_cons, hD])))
              (fun C => C.literals.any (fun ℓ => decide (x ℓ.idx = ℓ.value)))
            = List.all rest
                (fun C => C.lits.any (fun ℓ => decide (x ℓ.idx = ℓ.val))) := by
        simpa [Clause.eval, Clause.evalList, Literal.holds, Clause.toCore,
          Core.CnfClause.eval, Core.Literal.eval, Function.comp, List.any_map]
          using htailEval
      -- После подстановки равенств для головы и хвоста обе стороны
      -- сводятся к тождеству `Clause.eval C x && _ = Clause.eval C x && _`.
      -- Используем `simp`, чтобы довести выражение до рефлексивного равенства.
      -- После подстановки `hheadAny` и `htail` обе стороны совпадают.
      simp [List.all_cons, toCoreClausesAux, hwidth_tail, hnodup_tail,
        hheadAny, htailAny]

/--
  Преобразование AC⁰-КНФ в core-КНФ фиксированной ширины.  Доказательства
  ограничений передаются параметрами `hwidth` и `hnodup`.
-/
@[simp] def toCore (F : CNF n) (w : Nat)
    (hwidth : ∀ C ∈ F.clauses, Clause.width C ≤ w)
    (hnodup : ∀ C ∈ F.clauses, (C.lits.map (·.idx)).Nodup) :
    Core.CNF n w where
  clauses := toCoreClausesAux (n := n) w F.clauses hwidth hnodup
  width_le := by
    intro C hC
    exact toCoreClausesAux_mem_width (n := n) w F.clauses hwidth hnodup
      (C := C) hC

/-- Оценка core-КНФ, полученной из AC⁰-КНФ, совпадает с исходной функцией. -/
@[simp] lemma toCore_eval (F : CNF n) (w : Nat)
    (hwidth : ∀ C ∈ F.clauses, Clause.width C ≤ w)
    (hnodup : ∀ C ∈ F.clauses, (C.lits.map (·.idx)).Nodup)
    (x : Core.BitVec n) :
    (CNF.toCore (n := n) F w hwidth hnodup).eval x = eval F x := by
  classical
  cases F with
  | mk clauses =>
      -- Сначала используем предыдущее равенство с `Core.CnfClause.eval`,
      -- после чего переписываем обе стороны через явные `List.any`.
      have hallEval :=
        toCoreClausesAux_all_eval (n := n) w clauses hwidth hnodup x
      have hallAny :
          List.all
              (toCoreClausesAux (n := n) w clauses hwidth hnodup)
              (fun C => C.literals.any (fun ℓ => decide (x ℓ.idx = ℓ.value)))
            = List.all clauses
                (fun C => C.lits.any (fun ℓ => decide (x ℓ.idx = ℓ.val))) := by
        simpa [Clause.eval, Clause.evalList, Literal.holds, Clause.toCore,
          Core.CnfClause.eval, Core.Literal.eval, Function.comp, List.any_map]
          using hallEval
      simp [CNF.toCore, CNF.eval, hallAny]

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


/-!
### Схемы AC⁰ как деревья вентилей

Для дальнейшей индукции по глубине AC⁰ удобно зафиксировать модель схем в виде
дерева вентилей с неограниченным фан-ином.  Листьями выступают литералы (или
константы), а внутренние узлы — вентиль `AND` или `OR`.
-/

/-- Схема AC⁰: листья — литералы и константы, внутренние узлы — AND/OR. -/
inductive AC0Circuit (n : Nat) : Type
  | const : Bool → AC0Circuit n
  | literal : Literal n → AC0Circuit n
  | andGate : List (AC0Circuit n) → AC0Circuit n
  | orGate  : List (AC0Circuit n) → AC0Circuit n
  deriving Inhabited, Repr

namespace AC0Circuit

variable {n : Nat}

/-- Оценка схемы AC⁰ на входе `x`: листья — константы/литералы, внутренние
    вершины агрегируют значения потомков при помощи `foldr`. -/
@[simp] def eval : AC0Circuit n → Core.BitVec n → Bool
  | const b, _ => b
  | literal ℓ, x => Literal.holds ℓ x
  | andGate cs, x => cs.foldr (fun C acc => eval C x && acc) true
  | orGate cs, x => cs.foldr (fun C acc => eval C x || acc) false

/-- Конъюнкция значений подформул, вынесенная в отдельный помощник для удобства
    переписываний. -/
@[simp] def evalListAnd (cs : List (AC0Circuit n)) (x : Core.BitVec n) : Bool :=
  cs.foldr (fun C acc => eval (n := n) C x && acc) true

/-- Дизъюнкция значений подформул в аналогичном формате. -/
@[simp] def evalListOr (cs : List (AC0Circuit n)) (x : Core.BitVec n) : Bool :=
  cs.foldr (fun C acc => eval (n := n) C x || acc) false

@[simp] lemma eval_const (b : Bool) (x : Core.BitVec n) :
    eval (const (n := n) b) x = b := by
  simp [eval]

@[simp] lemma eval_literal (ℓ : Literal n) (x : Core.BitVec n) :
    eval (literal (n := n) ℓ) x = Literal.holds ℓ x := by
  simp [eval]

@[simp] lemma eval_andGate (cs : List (AC0Circuit n)) (x : Core.BitVec n) :
    eval (andGate (n := n) cs) x
      = evalListAnd (n := n) cs x := by
  simpa [eval, evalListAnd]

@[simp] lemma eval_orGate (cs : List (AC0Circuit n)) (x : Core.BitVec n) :
    eval (orGate (n := n) cs) x
      = evalListOr (n := n) cs x := by
  simpa [eval, evalListOr]

@[simp] lemma eval_andGate_nil (x : Core.BitVec n) :
    eval (andGate (n := n) []) x = true := by
  simp [eval, evalListAnd]

@[simp] lemma eval_orGate_nil (x : Core.BitVec n) :
    eval (orGate (n := n) []) x = false := by
  simp [eval, evalListOr]

@[simp] lemma eval_andGate_cons (C : AC0Circuit n) (cs : List (AC0Circuit n))
    (x : Core.BitVec n) :
    eval (andGate (n := n) (C :: cs)) x
      = (eval C x && eval (andGate (n := n) cs) x) := by
  simp [eval_andGate, evalListAnd]

@[simp] lemma eval_orGate_cons (C : AC0Circuit n) (cs : List (AC0Circuit n))
    (x : Core.BitVec n) :
    eval (orGate (n := n) (C :: cs)) x
      = (eval C x || eval (orGate (n := n) cs) x) := by
  simp [eval_orGate, evalListOr]

/--
  Ограничение схемы AC⁰ подкубом `β`.  Мы рекурсивно обходим дерево
  схемы и заменяем фиксированные литералы на константы, в то время как
  остальные узлы остаются прежними.  Такое определение удобно для
  дальнейшего анализа switching-леммы: после фиксации переменных мы
  можем рассуждать о глубине и размере оставшейся схемы, не меняя
  синтаксическую форму.
-/
@[simp] def restrict (C : AC0Circuit n) (β : Core.Subcube n) : AC0Circuit n :=
  match C with
  | const b => const (n := n) b
  | literal ℓ =>
      match β ℓ.idx with
      | some b =>
          if h : b = ℓ.val then
            const (n := n) true
          else
            const (n := n) false
      | none => literal (n := n) ℓ
  | andGate cs => andGate (n := n) (cs.map fun C => restrict C β)
  | orGate cs  => orGate (n := n) (cs.map fun C => restrict C β)

/--
  Ограничение не меняет значение схемы на точках, совместимых с подкубом.
  Это фундаментальная лемма: она гарантирует, что после замены части
  переменных константами схема вычисляет ту же функцию на всех
  продолжениях `β`.
-/
lemma restrict_eval_mem :
    ∀ (C : AC0Circuit n) (β : Core.Subcube n) {x : Core.BitVec n},
      Core.mem β x → eval (restrict (n := n) C β) x = eval C x
  | const b, β, x, hx => by
      simp [restrict]
  | literal ℓ, β, x, hx => by
      classical
      cases hβ : β ℓ.idx with
      | none =>
          simp [restrict, hβ]
      | some b =>
          have hx_idx : x ℓ.idx = b :=
            (Core.mem_iff (β := β) (x := x)).mp hx ℓ.idx b hβ
          by_cases hb : b = ℓ.val
          · subst hb
            simp [Literal.holds, restrict, hβ, hx_idx]
          · have hne : x ℓ.idx ≠ ℓ.val := by
              intro hcontr
              exact hb (by simpa [hx_idx] using hcontr)
            simp [Literal.holds, restrict, hβ, hx_idx, hb, hne]
  | andGate [], β, x, hx => by
      simp [restrict, eval_andGate, evalListAnd]
  | andGate (C :: cs), β, x, hx => by
      classical
      have hC := restrict_eval_mem (C := C) (β := β) (x := x) hx
      have hrest := restrict_eval_mem (C := andGate cs) (β := β) (x := x) hx
      have hrest' :
          eval (andGate (n := n) (cs.map fun D => restrict (n := n) D β)) x
            = eval (andGate (n := n) cs) x := by
        simpa [restrict] using hrest
      have hrest_fold :
          List.foldr (fun C acc => eval (n := n) C x && acc) true
              (cs.map fun D => restrict (n := n) D β)
            = List.foldr (fun C acc => eval (n := n) C x && acc) true cs := by
        simpa [eval_andGate, evalListAnd] using hrest'
      simp [restrict, eval_andGate_cons, hC, hrest_fold]
  | orGate [], β, x, hx => by
      simp [restrict, eval_orGate, evalListOr]
  | orGate (C :: cs), β, x, hx => by
      classical
      have hC := restrict_eval_mem (C := C) (β := β) (x := x) hx
      have hrest := restrict_eval_mem (C := orGate cs) (β := β) (x := x) hx
      have hrest' :
          eval (orGate (n := n) (cs.map fun D => restrict (n := n) D β)) x
            = eval (orGate (n := n) cs) x := by
        simpa [restrict] using hrest
      have hrest_fold :
          List.foldr (fun C acc => eval (n := n) C x || acc) false
              (cs.map fun D => restrict (n := n) D β)
            = List.foldr (fun C acc => eval (n := n) C x || acc) false cs := by
        simpa [eval_orGate, evalListOr] using hrest'
      simp [restrict, eval_orGate_cons, hC, hrest_fold]
/-- Размер схемы AC⁰: суммарное число узлов. -/
@[simp] def size : AC0Circuit n → Nat
  | const _ => 1
  | literal _ => 1
  | andGate cs => 1 + (cs.map size).sum
  | orGate cs  => 1 + (cs.map size).sum

@[simp] lemma size_const (b : Bool) :
    size (const (n := n) b) = 1 := by
  simp [size]

@[simp] lemma size_literal (ℓ : Literal n) :
    size (literal (n := n) ℓ) = 1 := by
  simp [size]

lemma size_andGate (cs : List (AC0Circuit n)) :
    size (andGate (n := n) cs) = 1 + (cs.map size).sum := by
  simp [size]

lemma size_orGate (cs : List (AC0Circuit n)) :
    size (orGate (n := n) cs) = 1 + (cs.map size).sum := by
  simp [size]

/-- Глубина схемы: число слоёв вентилей.  Используем свёртку по списку, чтобы
    выделить максимум глубин среди потомков. -/
@[simp] def depth : AC0Circuit n → Nat
  | const _ => 0
  | literal _ => 0
  | andGate cs => Nat.succ (cs.foldl (fun acc C => Nat.max acc (depth C)) 0)
  | orGate cs  => Nat.succ (cs.foldl (fun acc C => Nat.max acc (depth C)) 0)

/-- Удобное обозначение для «максимальной глубины» в списке подформул. -/
@[simp] def depthList (cs : List (AC0Circuit n)) : Nat :=
  cs.foldl (fun acc C => Nat.max acc (depth (n := n) C)) 0

@[simp] lemma depth_andGate (cs : List (AC0Circuit n)) :
    depth (andGate (n := n) cs)
      = Nat.succ (depthList (n := n) cs) := by
  simp [depth, depthList]

@[simp] lemma depth_orGate (cs : List (AC0Circuit n)) :
    depth (orGate (n := n) cs)
      = Nat.succ (depthList (n := n) cs) := by
  simp [depth, depthList]

lemma size_pos (C : AC0Circuit n) : 0 < size (n := n) C := by
  cases C with
  | const _ => simp [size]
  | literal _ => simp [size]
  | andGate cs =>
      -- `size` равно `Nat.succ _`, поэтому используем `Nat.succ_pos`.
      simpa [size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        Nat.succ_eq_add_one] using Nat.succ_pos ((cs.map size).sum)
  | orGate cs =>
      -- Тот же аргумент для дизъюнктивного вентиля.
      simpa [size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        Nat.succ_eq_add_one] using Nat.succ_pos ((cs.map size).sum)

end AC0Circuit

end AC0
end Pnp3
