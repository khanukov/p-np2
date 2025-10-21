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

/-- Ширина клаузы — число литералов в списке.  Определяем её как длину
    списка, чтобы удобнее было доказывать оценочные свойства. -/
@[simp] def width (C : Clause n) : Nat :=
  C.lits.length

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

@[simp] def pendingWidth : RestrictResult n → Nat
  | .satisfied    => 0
  | .falsified    => 0
  | .pending lits => lits.length

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

/-- Ограничение не может увеличить ширину остаточной клаузы.  Технически мы
    формулируем утверждение для вспомогательной функции `restrictList`, после
    чего перенесём его на главную конструкцию `Clause.restrict`. -/
private lemma restrictList_pending_length_le (β : Subcube n) :
    ∀ {lits pending},
      restrictList (β := β) lits = RestrictResult.pending pending →
      pending.length ≤ lits.length := by
  intro lits
  induction lits with
  | nil =>
      intro pending h
      -- База невозможна: пустой список даёт `falsified`.
      simp [restrictList] at h
  | cons ℓ rest ih =>
      intro pending h
      classical
      dsimp [restrictList] at h
      cases hβ : β ℓ.idx with
      | some b =>
          by_cases hval : b = ℓ.val
          · -- Ветка `satisfied`: противоречит тому, что результат pending.
            simp [hβ, hval] at h
          · -- Отбрасываем литерал и применяем предположение индукции.
            have hRest : restrictList (β := β) rest = RestrictResult.pending pending := by
              simpa [hβ, hval] using h
            have ihBound := ih hRest
            have : pending.length ≤ rest.length := by simpa using ihBound
            exact Nat.le_trans this (Nat.le_succ (rest.length))
        | none =>
            cases hrest : restrictList (β := β) rest with
            | satisfied =>
                -- Когда хвост удовлетворён, результат не может быть `pending`.
                cases (by simpa [restrictList, hβ, hrest] using h : False)
            | falsified =>
                -- Из равенства получаем `pending = [ℓ]` и завершаем оценку.
                have hEq : [ℓ] = pending := by
                  simpa [restrictList, hβ, hrest] using h
                cases hEq
                simp [List.length_cons]
            | pending L =>
                -- Используем предположение индукции для остатка.
                have hEq : ℓ :: L = pending := by
                  simpa [restrictList, hβ, hrest] using h
                cases hEq
                have ihBound := ih hrest
                have : Nat.succ (List.length L) ≤ Nat.succ (List.length rest) :=
                  Nat.succ_le_succ ihBound
                simpa [List.length_cons] using this

/-- Интерпретация результата ограничения: для удовлетворённой/опровержённой
    клаузы возвращаем константы, в противном случае оцениваем остаток. -/
@[simp] def RestrictResult.eval (res : RestrictResult n) (x : Core.BitVec n) : Bool :=
  match res with
  | RestrictResult.satisfied => true
  | RestrictResult.falsified => false
  | RestrictResult.pending lits => Clause.evalList lits x

/-- Ограничение клаузы подкубом. -/
@[simp] def restrict (C : Clause n) (β : Subcube n) : RestrictResult n :=
  restrictList (β := β) C.lits

/-- Основное следствие: ширина остаточной клаузы не превосходит исходной. -/
lemma restrict_pending_width_le (C : Clause n) (β : Subcube n)
    {pending : List (Literal n)}
    (h : restrict (β := β) C = RestrictResult.pending pending) :
    pending.length ≤ C.width := by
  dsimp [Clause.restrict, Clause.width] at h ⊢
  exact restrictList_pending_length_le (β := β) h

/-- Ограничение одноэлементной клаузы, полностью фиксированной подкубом, даёт `satisfied`. -/
lemma restrict_singleton_satisfied (β : Subcube n) (i : Fin n) (b : Bool)
    (h : β i = some b) :
    restrict (β := β) ⟨[⟨i, b⟩]⟩ = RestrictResult.satisfied := by
  classical
  simp [Clause.restrict, restrictList, h]

end Clause

/-! ### Термы (конъюнкции литералов) -/

/-- Терм в ДНФ: конъюнкция литералов. -/
structure Term (n : Nat) where
  lits : List (Literal n)
  deriving DecidableEq, Repr

namespace Term

variable {n : Nat}

/-- Ширина терма — количество литералов в конъюнкции. -/
@[simp] def width (T : Term n) : Nat :=
  T.lits.length

/-- Значение терма на входе `x`: все литералы должны выполняться. -/
@[simp] def eval (T : Term n) (x : Core.BitVec n) : Bool :=
  T.lits.all (fun ℓ => Literal.holds ℓ x)

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

@[simp] def pendingWidth : RestrictResult n → Nat
  | .satisfied    => 0
  | .falsified    => 0
  | .pending lits => lits.length

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
        | RestrictResult.satisfied => RestrictResult.satisfied
        | RestrictResult.falsified => RestrictResult.falsified
        | RestrictResult.pending L => RestrictResult.pending (ℓ :: L)

  private lemma restrictList_pending_length_le (β : Subcube n) :
      ∀ {lits pending},
        restrictList (β := β) lits = RestrictResult.pending pending →
        pending.length ≤ lits.length := by
    intro lits
    induction lits with
    | nil =>
        intro pending h
        -- Пустой терм ограничивается в `satisfied`, так что рассматривать нечего.
        simp [restrictList] at h
    | cons ℓ rest ih =>
        intro pending h
        classical
        dsimp [restrictList] at h
        cases hβ : β ℓ.idx with
      | some b =>
          by_cases hval : b = ℓ.val
          · -- При совпадении значения переходим к хвосту и применяем И.П.
            have hRest : restrictList (β := β) rest = RestrictResult.pending pending := by
              simpa [hβ, hval] using h
            have ihBound := ih hRest
            have : pending.length ≤ rest.length := by simpa using ihBound
            exact Nat.le_trans this (Nat.le_succ (rest.length))
          · -- Противоречие: результат должен был стать `falsified`.
            cases (by simpa [restrictList, hβ, hval] using h : False)
          | none =>
              cases hrest : restrictList (β := β) rest with
            | satisfied =>
                have hEq : [ℓ] = pending := by
                  simpa [restrictList, hβ, hrest] using h
                cases hEq
                simp [List.length_cons]
            | falsified =>
                -- Этот случай невозможен: `restrictList` возвращает `falsified`
                -- только на пустом списке, что уже рассмотрено базой.
                cases (by simpa [restrictList, hβ, hrest] using h : False)
            | pending L =>
                have hEq : ℓ :: L = pending := by
                  simpa [restrictList, hβ, hrest] using h
                cases hEq
                have ihBound := ih hrest
                have : Nat.succ (List.length L) ≤ Nat.succ (List.length rest) :=
                  Nat.succ_le_succ ihBound
                simpa [List.length_cons] using this

@[simp] def RestrictResult.eval (res : RestrictResult n) (x : Core.BitVec n) : Bool :=
  match res with
  | RestrictResult.satisfied => true
  | RestrictResult.falsified => false
  | RestrictResult.pending lits => Term.eval ⟨lits⟩ x

@[simp] def restrict (T : Term n) (β : Subcube n) : RestrictResult n :=
  restrictList (β := β) T.lits

lemma restrict_pending_width_le (T : Term n) (β : Subcube n)
    {pending : List (Literal n)}
    (h : restrict (β := β) T = RestrictResult.pending pending) :
    pending.length ≤ T.width := by
  dsimp [Term.restrict, Term.width] at h ⊢
  exact restrictList_pending_length_le (β := β) h

/-- Ограничение одноэлементного терма, фиксированного подкубом, даёт `satisfied`. -/
lemma restrict_singleton_satisfied (β : Subcube n) (i : Fin n) (b : Bool)
    (h : β i = some b) :
    restrict (β := β) ⟨[⟨i, b⟩]⟩ = Term.RestrictResult.satisfied := by
  classical
  simp [Term.restrict, restrictList, h]

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

/-- Количество клауз в формуле.  Позже удобно брать максимум по ширине. -/
@[simp] def clauseCount (F : CNF n) : Nat :=
  F.clauses.length

@[simp] def eval (F : CNF n) (x : Core.BitVec n) : Bool :=
  F.clauses.all (fun C => Clause.eval C x)

/-- Результат ограничения КНФ: формула может стать тождественной истиной,
    тождественным ложью или остаться списком сокращённых клауз. -/
inductive RestrictResult (n : Nat)
| satisfied : RestrictResult n
| falsified : RestrictResult n
| pending   : List (Clause n) → RestrictResult n
  deriving Repr

namespace RestrictResult

variable {n : Nat}

@[simp] def eval : RestrictResult n → (Core.BitVec n → Bool)
  | RestrictResult.satisfied      => fun _ => true
  | RestrictResult.falsified      => fun _ => false
  | RestrictResult.pending clauses => fun x =>
      CNF.eval ⟨clauses⟩ x

end RestrictResult

private def restrictClauses (β : Subcube n) :
    List (Clause n) → RestrictResult n
  | [] => RestrictResult.satisfied
  | C :: rest =>
      match Clause.restrict (β := β) C,
            restrictClauses (β := β) rest with
      | Clause.RestrictResult.satisfied, tail => tail
      | Clause.RestrictResult.falsified, _ => RestrictResult.falsified
      | Clause.RestrictResult.pending lits, RestrictResult.satisfied =>
          RestrictResult.pending [⟨lits⟩]
      | Clause.RestrictResult.pending _lits, RestrictResult.falsified =>
          RestrictResult.falsified
      | Clause.RestrictResult.pending lits, RestrictResult.pending clauses =>
          RestrictResult.pending (⟨lits⟩ :: clauses)

@[simp] def restrict (F : CNF n) (β : Subcube n) : RestrictResult n :=
  restrictClauses (β := β) F.clauses


end CNF

namespace DNF

variable {n : Nat}

/-- Количество термов в формуле ДНФ. -/
@[simp] def termCount (F : DNF n) : Nat :=
  F.terms.length

@[simp] def eval (F : DNF n) (x : Core.BitVec n) : Bool :=
  F.terms.any (fun T => Term.eval T x)

/-- Аналог КНФ: формула после ограничения может стать постоянной или
    сократиться до меньшего списка термов. -/
inductive RestrictResult (n : Nat)
| satisfied : RestrictResult n
| falsified : RestrictResult n
| pending   : List (Term n) → RestrictResult n
  deriving Repr

namespace RestrictResult

variable {n : Nat}

@[simp] def eval : RestrictResult n → (Core.BitVec n → Bool)
  | RestrictResult.satisfied      => fun _ => true
  | RestrictResult.falsified      => fun _ => false
  | RestrictResult.pending terms  => fun x =>
      DNF.eval ⟨terms⟩ x

end RestrictResult

private def restrictTerms (β : Subcube n) :
    List (Term n) → RestrictResult n
  | [] => RestrictResult.falsified
  | T :: rest =>
      match Term.restrict (β := β) T,
            restrictTerms (β := β) rest with
      | Term.RestrictResult.satisfied, _ => RestrictResult.satisfied
      | Term.RestrictResult.falsified, tail => tail
      | Term.RestrictResult.pending lits, RestrictResult.satisfied =>
          RestrictResult.pending [⟨lits⟩]
      | Term.RestrictResult.pending lits, RestrictResult.falsified =>
          RestrictResult.pending [⟨lits⟩]
      | Term.RestrictResult.pending lits, RestrictResult.pending terms =>
          RestrictResult.pending (⟨lits⟩ :: terms)

@[simp] def restrict (F : DNF n) (β : Subcube n) : RestrictResult n :=
  restrictTerms (β := β) F.terms


end DNF

end AC0
end Pnp3
