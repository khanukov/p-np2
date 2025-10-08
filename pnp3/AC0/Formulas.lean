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

end AC0
end Pnp3
