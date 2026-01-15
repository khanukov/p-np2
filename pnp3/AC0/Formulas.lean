/-
  pnp3/AC0/Formulas.lean

  Формализация базовых булевых формул, появляющихся в классических
  switching-леммах: конъюнктивные и дизъюнктивные термы, а также их
  ограничение случайными подкубами.  Этот модуль служит подготовительным
  этапом к устранению внешней аксиомы `shrinkage_for_AC0` и к подстановке
  shrinkage-свидетеля для теоремы `shrinkage_for_localCircuit`: после определения
  синтаксиса формул можно строить непосредственные деревья решений и проводить
  оценку ошибок.

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

/-- Перевод AC0-литерала в Core-литерал (совпадают по полям). -/
@[simp] def toCore (ℓ : Literal n) : Core.Literal n :=
  ⟨ℓ.idx, ℓ.val⟩

/-! Истинность литерала на данном входе в булевой форме. -/
@[simp] def holds (ℓ : Literal n) (x : Core.BitVec n) : Bool :=
  decide (x ℓ.idx = ℓ.val)

@[simp] lemma toCore_idx (ℓ : Literal n) : (toCore ℓ).idx = ℓ.idx := by
  rfl

@[simp] lemma toCore_val (ℓ : Literal n) : (toCore ℓ).value = ℓ.val := by
  rfl

@[simp] lemma eval_toCore (ℓ : Literal n) (x : Core.BitVec n) :
    Core.Literal.eval (toCore ℓ) x = holds ℓ x := by
  -- В обеих версиях литерал истиннен тогда и только тогда,
  -- когда выполняется равенство `x idx = val`.
  by_cases h : x ℓ.idx = ℓ.val
  · simp [toCore, holds, Core.Literal.eval, h]
  · simp [toCore, holds, Core.Literal.eval, h]

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

end Clause

/-! ### Термы (конъюнкции литералов) -/

/-- Терм в ДНФ: конъюнкция литералов. -/
structure Term (n : Nat) where
  lits : List (Literal n)
  deriving DecidableEq, Repr

namespace Term

variable {n : Nat}

private lemma all_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    (l.map f).all p = l.all (fun a => p (f a)) := by
  induction l with
  | nil =>
      simp
  | cons a rest ih =>
      simp [List.all, ih]

@[simp] private lemma all_toCore_decide (lits : List (Literal n)) (x : Core.BitVec n) :
    lits.all ((fun ℓ => decide (x ℓ.idx = ℓ.value)) ∘ Literal.toCore) =
      lits.all (fun ℓ => decide (x ℓ.idx = ℓ.val)) := by
  induction lits with
  | nil =>
      simp
  | cons ℓ rest ih =>
      simp [List.all, Literal.toCore, Function.comp, ih]

/-- Ширина терма: число литералов. -/
@[simp] def width (T : Term n) : Nat := T.lits.length

/-- Значение терма на входе `x`: все литералы должны выполняться. -/
@[simp] def eval (T : Term n) (x : Core.BitVec n) : Bool :=
  T.lits.all (fun ℓ => Literal.holds ℓ x)

/--
Перевод терма в `Core.DnfTerm`.

Мы требуем `Nodup` по индексам, чтобы корректно сформировать
`Core.CnfClause`, который используется в Core-термах.
-/
@[simp] def toCoreDnfTerm (T : Term n)
    (hNodup : (T.lits.map (·.idx)).Nodup) : Core.DnfTerm n :=
  ⟨T.lits.map Literal.toCore, by
    -- Индексы сохраняются, поэтому `Nodup` переносится напрямую.
    simpa [Literal.toCore, List.map_map] using hNodup⟩

@[simp] lemma toCoreDnfTerm_width (T : Term n)
    (hNodup : (T.lits.map (·.idx)).Nodup) :
    (toCoreDnfTerm T hNodup).width = T.width := by
  -- `width` — это длина списка литералов; маппинг не меняет длину.
  simp [toCoreDnfTerm, width]

@[simp] lemma eval_toCoreDnfTerm (T : Term n)
    (hNodup : (T.lits.map (·.idx)).Nodup) (x : Core.BitVec n) :
    Core.DnfTerm.eval (toCoreDnfTerm T hNodup) x = eval T x := by
  -- Оценка терма сохраняется под поэлементным переводом литералов.
  cases T with
  | mk lits =>
      simp [toCoreDnfTerm, eval, Core.DnfTerm.eval, Literal.holds, all_toCore_decide]

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
        | RestrictResult.satisfied => RestrictResult.satisfied
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

end CNF

namespace DNF

variable {n : Nat}

@[simp] def eval (F : DNF n) (x : Core.BitVec n) : Bool :=
  F.terms.any (fun T => Term.eval T x)

end DNF

/-!
### Мост к `Core.DNF` (k-DNF) с явными ограничениями

Multi-switching в `Core` ожидает k-DNF, где термы имеют `Nodup` по индексам
и явный числовой bound на ширину. Следующие определения позволяют
переводить AC0-DNF в Core-DNF при наличии соответствующих предпосылок.
-/

namespace DNF

variable {n : Nat}

/-- Перевод AC0-DNF в `Core.DNF` ширины `w` при наличии ограничений. -/
@[simp] def toCoreDNF (F : DNF n) (w : Nat)
    (hwidth : ∀ T ∈ F.terms, Term.width T ≤ w)
    (hNodup : ∀ T ∈ F.terms, (T.lits.map (·.idx)).Nodup) : Core.DNF n w :=
  { terms :=
      (F.terms.attach).map
        (fun T => Term.toCoreDnfTerm T.1 (hNodup T.1 T.2))
    width_le := by
      intro T hT
      rcases List.mem_map.mp hT with ⟨T', hT', rfl⟩
      have hwidth' := hwidth T'.1 T'.2
      -- Переносим оценку ширины через `toCoreDnfTerm`.
      simpa [Term.toCoreDnfTerm_width] using hwidth' }

private lemma any_attach_map {α β : Type} (l : List α)
    (f : α → β) (p : β → Bool) :
    ((l.attach).map (fun a => f a.1)).any p = l.any (fun a => p (f a)) := by
  induction l with
  | nil =>
      simp
  | cons a rest ih =>
      -- В обоих списках голова даёт одинаковый вклад, дальше используем IH.
      simp [List.attach, List.any]
      rfl

@[simp] lemma eval_toCoreDNF (F : DNF n) (w : Nat)
    (hwidth : ∀ T ∈ F.terms, Term.width T ≤ w)
    (hNodup : ∀ T ∈ F.terms, (T.lits.map (·.idx)).Nodup)
    (x : Core.BitVec n) :
    Core.DNF.eval (toCoreDNF F w hwidth hNodup) x = eval F x := by
  -- Переходим к поэлементному переводу и используем лемму для термов.
  simp [toCoreDNF, Core.DNF.eval, eval]

end DNF

end AC0
end Pnp3
