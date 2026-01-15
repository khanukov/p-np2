import Core.BooleanBasics

/-!
  pnp3/AC0/MultiSwitching/Duality.lean

  Дуальность между k-DNF и k-CNF на уровне базовых типов Core.
  Этот файл даёт конструктивный мост:

  * литерал → отрицание литерала;
  * терм DNF → клауза CNF (по отрицанию литералов);
  * ¬(DNF) → CNF без изменения ширины.

  Все леммы здесь — вычислительные тождества над `Bool`, без аксиом.
-/

namespace Pnp3
namespace Core

/-! ### Отрицание литералов -/

namespace Literal

variable {n : Nat}

/-- Отрицание литерала: индекс тот же, значение инвертируется. -/
@[simp] def neg (ℓ : Literal n) : Literal n :=
  ⟨ℓ.idx, !ℓ.value⟩

@[simp] lemma neg_idx (ℓ : Literal n) : (neg ℓ).idx = ℓ.idx := by
  rfl

/-- Оценка отрицания совпадает с булевым отрицанием оценки. -/
@[simp] lemma eval_neg (ℓ : Literal n) (x : BitVec n) :
    Literal.eval (neg ℓ) x = ! Literal.eval ℓ x := by
  cases ℓ with
  | mk idx value =>
      -- Полный перебор по значению переменной и литерала.
      cases hx : x idx <;> cases value <;> simp [Literal.eval, neg]

end Literal

/-! ### От DNF-терма к CNF-клаузе -/

namespace DnfTerm

variable {n : Nat}

/-- Клауза, соответствующая отрицанию терма: ¬(ℓ₁ ∧ ... ∧ ℓ_k) = (¬ℓ₁) ∨ ... ∨ (¬ℓ_k). -/
@[simp] def negToClause (T : DnfTerm n) : CnfClause n :=
  ⟨T.literals.map Literal.neg, by
    -- Индексы литералов не меняются, поэтому `Nodup` сохраняется.
    simpa using (T.nodupIdx : (T.literals.map (·.idx)).Nodup)⟩

@[simp] lemma negToClause_width (T : DnfTerm n) :
    (negToClause T).width = T.width := by
  -- Ширина — длина списка литералов; `map` длину не меняет.
  simp [negToClause, CnfClause.width]

private lemma any_neg_eq_not_all (l : List (Literal n)) (x : BitVec n) :
    l.any (fun ℓ => Literal.eval (Literal.neg ℓ) x) =
      ! l.all (fun ℓ => Literal.eval ℓ x) := by
  induction l with
  | nil =>
      simp
  | cons ℓ rest ih =>
      -- Разбираем значения переменной и литерала.
      have ih' := ih
      simp [Literal.eval] at ih'
      cases hx : x ℓ.idx <;>
      cases hv : ℓ.value <;>
      simp [List.any, List.all, Literal.eval, Literal.neg, hx, hv, ih']

/-- Версия `any_neg_eq_not_all` после разворачивания `Literal.eval`. -/
@[simp] lemma any_neg_eq_not_all_decide (l : List (Literal n)) (x : BitVec n) :
    l.any ((fun ℓ => decide (x ℓ.idx = ℓ.value)) ∘ Literal.neg) =
      ! l.all (fun ℓ => decide (x ℓ.idx = ℓ.value)) := by
  -- Достаточно раскрыть `Literal.eval` и применить базовую лемму.
  simpa [Literal.eval] using (any_neg_eq_not_all (l := l) (x := x))

private lemma eval_negToClause_decide (T : DnfTerm n) (x : BitVec n) :
    (DnfTerm.negToClause T).literals.any (fun ℓ => decide (x ℓ.idx = ℓ.value)) =
      ! T.literals.all (fun ℓ => decide (x ℓ.idx = ℓ.value)) := by
  -- Используем уже полученную версию через `decide`.
  -- Здесь `simp` раскрывает `negToClause` и сводит к `any_neg_eq_not_all_decide`.
  simp [DnfTerm.negToClause]

/-- Оценка клаузы отрицания совпадает с отрицанием оценки терма. -/
@[simp] lemma eval_negToClause (T : DnfTerm n) (x : BitVec n) :
    CnfClause.eval (negToClause T) x = ! DnfTerm.eval T x := by
  simp [DnfTerm.eval, CnfClause.eval, negToClause, any_neg_eq_not_all_decide]

end DnfTerm

/-! ### Отрицание DNF как CNF -/

namespace DNF

variable {n w : Nat}

private lemma all_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    (l.map f).all p = l.all (fun a => p (f a)) := by
  induction l with
  | nil =>
      simp
  | cons a rest ih =>
      simp [List.all, ih]

private lemma any_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    (l.map f).any p = l.any (fun a => p (f a)) := by
  induction l with
  | nil =>
      simp
  | cons a rest ih =>
      simp [List.any, ih]

/-- CNF-формула, эквивалентная отрицанию DNF. -/
@[simp] def negToCNF (F : DNF n w) : CNF n w :=
  { clauses := F.terms.map DnfTerm.negToClause
    width_le := by
      intro C hC
      rcases List.mem_map.mp hC with ⟨T, hT, rfl⟩
      simpa [DnfTerm.negToClause_width] using F.width_le T hT }

private lemma all_neg_eq_not_any (l : List (DnfTerm n)) (x : BitVec n) :
    l.all (fun T => ! DnfTerm.eval T x) =
      ! l.any (fun T => DnfTerm.eval T x) := by
  induction l with
  | nil =>
      simp
  | cons T rest ih =>
      have ih' := ih
      simp [DnfTerm.eval] at ih'
      cases hT : T.literals.all (fun ℓ => Literal.eval ℓ x) <;>
      cases hrest : rest.any (fun T => DnfTerm.eval T x) <;>
      -- `hT` и `hrest` не нужны после раскрытия `DnfTerm.eval`.
      simp [List.any, List.all, DnfTerm.eval, ih']

private lemma all_neg_eq_not_any_decide (l : List (DnfTerm n)) (x : BitVec n) :
    l.all (fun T => !T.literals.all (fun ℓ => decide (x ℓ.idx = ℓ.value))) =
      ! l.any (fun T => T.literals.all (fun ℓ => decide (x ℓ.idx = ℓ.value))) := by
  simpa [DnfTerm.eval, Literal.eval] using (all_neg_eq_not_any (l := l) (x := x))

/-- Значение `negToCNF` — точное отрицание значения исходной DNF. -/
@[simp] lemma eval_negToCNF (F : DNF n w) (x : BitVec n) :
    CNF.eval (negToCNF F) x = ! DNF.eval F x := by
  cases F with
  | mk terms width_le =>
      -- После раскрытия определений ширина не влияет на оценку.
      simp [CNF.eval, DNF.eval, negToCNF]
      induction terms with
      | nil =>
          simp
      | cons T rest ih =>
          have width_le_rest : ∀ T ∈ rest, CnfClause.width T ≤ w := by
            intro T hT
            exact width_le T (by simp [hT])
          have ih' := ih width_le_rest
          -- После разворачивания `negToClause` и `any_neg_eq_not_all_decide`
          -- остаётся стандартное `simp` на хвосте.
          simp [DnfTerm.negToClause, DnfTerm.any_neg_eq_not_all_decide,
            List.any, List.all, Function.comp, ih']

end DNF

/-! ### Эквивалентность с двойным отрицанием -/

namespace DNF

variable {n w : Nat}

/-- Двойное отрицание DNF восстанавливает исходную формулу по значениям. -/
@[simp] lemma eval_negToCNF_neg (F : DNF n w) (x : BitVec n) :
    ! CNF.eval (negToCNF F) x = DNF.eval F x := by
  -- Переводим `eval_negToCNF` к форме с `terms`, затем снимаем отрицание.
  have h := eval_negToCNF (F := F) (x := x)
  simp [CNF.eval, DNF.eval, negToCNF] at h
  simp [h]

end DNF

end Core
end Pnp3
