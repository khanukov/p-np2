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
  rfl

private lemma any_neg_eq_not_all (l : List (Literal n)) (x : BitVec n) :
    l.any (fun ℓ => Literal.eval (Literal.neg ℓ) x) =
      ! l.all (fun ℓ => Literal.eval ℓ x) := by
  induction l with
  | nil =>
      simp
  | cons ℓ rest ih =>
      cases hℓ : Literal.eval ℓ x <;>
        cases hrest : rest.all (fun ℓ => Literal.eval ℓ x) <;>
        simp [List.any, List.all, Literal.eval_neg, hℓ, hrest, ih]

/-- Оценка клаузы отрицания совпадает с отрицанием оценки терма. -/
@[simp] lemma eval_negToClause (T : DnfTerm n) (x : BitVec n) :
    CnfClause.eval (negToClause T) x = ! DnfTerm.eval T x := by
  simp [DnfTerm.eval, CnfClause.eval, negToClause, any_neg_eq_not_all]

end DnfTerm

/-! ### Отрицание DNF как CNF -/

namespace DNF

variable {n w : Nat}

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
      cases hT : DnfTerm.eval T x <;>
        cases hrest : rest.any (fun T => DnfTerm.eval T x) <;>
        simp [List.any, List.all, hT, hrest, ih]

/-- Значение `negToCNF` — точное отрицание значения исходной DNF. -/
@[simp] lemma eval_negToCNF (F : DNF n w) (x : BitVec n) :
    CNF.eval (negToCNF F) x = ! DNF.eval F x := by
  simp [CNF.eval, DNF.eval, negToCNF, all_neg_eq_not_any]

end DNF

end Core
end Pnp3
