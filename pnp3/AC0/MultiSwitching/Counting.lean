import AC0.MultiSwitching.Restrictions

/-!
  pnp3/AC0/MultiSwitching/Counting.lean

  Базовые комбинаторные леммы для модели `R_s` (равномерное распределение
  по рестрикциям с фиксированным числом свободных координат).

  Эти результаты нужны для шага "вероятность → существование": если множество
  "плохих" рестрикций имеет строго меньший кардинал, чем всё `R_s`, то
  существует "хорошая" рестрикция. Леммы здесь не зависят от конкретного
  определения "плохих" рестрикций и потому пригодны для будущей реализации
  multi‑switching (encoding/injection).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n : Nat}

/--
Множество "плохих" рестрикций внутри `R_s`: это просто фильтр по предикату
`bad`. По умолчанию используется `DecidablePred bad`, чтобы лемма была
применима к любому вычислимому условию.
-/
@[simp] def badRestrictions (s : Nat) (bad : Restriction n → Prop)
    [DecidablePred bad] : Finset (Restriction n) :=
  (R_s (n := n) s).filter bad

/-!
  Простейшие свойства `badRestrictions`.

  Эти леммы почти тривиальны, но они избавляют от повторения
  однотипных аргументов `simp`/`filter` в будущих модулях
  (Encoding/Counting), где будем оценивать кардиналы.
-/

/-- Подмножество: `badRestrictions` лежит внутри `R_s`. -/
lemma badRestrictions_subset {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad] :
    badRestrictions (n := n) s bad
      ⊆ R_s (n := n) s := by
  intro ρ hmem
  have hmem' : ρ ∈ R_s (n := n) s ∧ bad ρ := by
    simpa [badRestrictions] using hmem
  exact hmem'.1

/--
Кардинал `badRestrictions` никогда не превосходит кардинал `R_s`.

Это базовая оценка, которая в паре с *строгим* неравенством
даёт существование "хорошей" рестрикции.
-/
lemma badRestrictions_card_le {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad] :
    (badRestrictions (n := n) s bad).card
      ≤ (R_s (n := n) s).card := by
  classical
  -- `filter` всегда уменьшает кардинал.
  simpa [badRestrictions] using
    (Finset.card_filter_le (s := R_s (n := n) s)
      (p := bad))

@[simp] lemma mem_badRestrictions {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad] {ρ : Restriction n} :
    ρ ∈ badRestrictions (n := n) s bad
      ↔ ρ ∈ R_s (n := n) s ∧ bad ρ := by
  classical
  simp [badRestrictions]

/--
Если "плохих" рестрикций строго меньше, чем всего `R_s`,
то существует "хорошая" рестрикция в `R_s`.

Это целевой комбинаторный шаг, который в дальнейшем будет
применяться после доказательства оценки на `card (badRestrictions ...)`.
-/
lemma exists_good_of_card_lt {s : Nat} {bad : Restriction n → Prop}
    [DecidablePred bad]
    (hcard :
      (badRestrictions (n := n) s bad).card
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ bad ρ := by
  classical
  have hsubset :
      badRestrictions (n := n) s bad
        ⊆ R_s (n := n) s := by
    exact badRestrictions_subset (n := n) (s := s) (bad := bad)
  rcases Restriction.exists_not_mem_of_subset_card_lt
      (s := badRestrictions (n := n) s bad)
      (t := R_s (n := n) s)
      hsubset hcard with ⟨ρ, hρt, hρs⟩
  refine ⟨ρ, hρt, ?_⟩
  intro hbad
  have : ρ ∈ badRestrictions (n := n) s bad := by
    exact (mem_badRestrictions (n := n) (s := s) (bad := bad)).2 ⟨hρt, hbad⟩
  exact hρs this

end MultiSwitching
end AC0
end Pnp3
