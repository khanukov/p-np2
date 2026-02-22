import Core.BooleanBasics
import Mathlib.Data.Nat.Choose.Bounds

/-!
  pnp3/AC0/MultiSwitching/Restrictions.lean

  Минимальный набор лемм про модель `R_s` — рестрикции с фиксированным числом
  свободных координат.  Эти факты используются как «контракт» в модулях
  multi-switching, чтобы не вытягивать детали из `Core.BooleanBasics`.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n : Nat}

/-!
### Модель `R_s`

Мы работаем с равномерным распределением по рестрикциям, у которых ровно `s`
свободных координат.  Это стандартная комбинаторная замена вероятностного
подхода в switching-леммах.
-/

/-- `R_s` — финитное множество рестрикций с ровно `s` свободными битами. -/
@[simp] abbrev R_s (n s : Nat) : Finset (Restriction n) :=
  Restriction.restrictionsWithFreeCount (n := n) s

/--
`R_le n s` — срез рестрикций с не более чем `s` свободными координатами.
Нужен для block-wise шагов, где за один шаг может убираться >1 звезды.
-/
@[simp] def R_le (n s : Nat) : Finset (Restriction n) :=
  (Finset.univ : Finset (Restriction n)).filter (fun ρ => ρ.freeCount ≤ s)

/--
`R_exact n L` — точный комбинаторный срез: рестрикции с ровно `L` звёздами
(`freeCount = L`). Это синоним `R_s`, выделенный для теорем существования.
-/
@[simp] abbrev R_exact (n L : Nat) : Finset (Restriction n) := R_s (n := n) L

/-- Характеризация принадлежности `R_s`. -/
@[simp] lemma mem_R_s {ρ : Restriction n} {s : Nat} :
    ρ ∈ R_s (n := n) s ↔ ρ.freeCount = s := by
  simp [R_s]

@[simp] lemma mem_R_le {ρ : Restriction n} {s : Nat} :
    ρ ∈ R_le (n := n) s ↔ ρ.freeCount ≤ s := by
  simp [R_le]

lemma R_s_subset_R_le {s : Nat} :
    R_s (n := n) s ⊆ R_le (n := n) s := by
  intro ρ hρ
  have hEq : ρ.freeCount = s :=
    (mem_R_s (n := n) (ρ := ρ) (s := s)).1 hρ
  exact (mem_R_le (n := n) (ρ := ρ) (s := s)).2
    (le_of_eq hEq)

lemma card_R_s_le_card_R_le (s : Nat) :
    (R_s (n := n) s).card ≤ (R_le (n := n) s).card := by
  exact Finset.card_le_card (R_s_subset_R_le (n := n) (s := s))

/--
В строгом срезе `R_s` число свободных координат фиксировано,
поэтому любые верхние оценки на `s` автоматически переносятся на `ρ.freeCount`.
-/
lemma freeCount_le_of_mem_R_s {ρ : Restriction n} {s b : Nat}
    (hρ : ρ ∈ R_s (n := n) s) (hsb : s ≤ b) :
    ρ.freeCount ≤ b := by
  have hcount : ρ.freeCount = s := (mem_R_s (n := n) (ρ := ρ) (s := s)).1 hρ
  have hcount' : ρ.freeIndicesList.length = s := by
    simpa [Restriction.freeCount] using hcount
  simpa [Restriction.freeCount, hcount'] using hsb

/--
Специализация для I-4: если работаем в срезе `R_s` с `s ≤ n/4`,
то требование `freeCount ≤ n/4` выполняется по построению.
-/
lemma freeCount_le_quarter_of_mem_R_s {ρ : Restriction n} {s : Nat}
    (hρ : ρ ∈ R_s (n := n) s) (hs : s ≤ n / 4) :
    ρ.freeCount ≤ n / 4 :=
  freeCount_le_of_mem_R_s (n := n) hρ hs

lemma freeCount_le_of_mem_R_le {ρ : Restriction n} {s : Nat}
    (hρ : ρ ∈ R_le (n := n) s) :
    ρ.freeCount ≤ s :=
  (mem_R_le (n := n) (ρ := ρ) (s := s)).1 hρ

lemma freeCount_le_quarter_of_mem_R_le {ρ : Restriction n} {s : Nat}
    (hρ : ρ ∈ R_le (n := n) s) (hs : s ≤ n / 4) :
    ρ.freeCount ≤ n / 4 :=
  le_trans (freeCount_le_of_mem_R_le (n := n) hρ) hs

/-!
### Кардинальные оценки

Явная формула `|R_s| = C(n,s) * 2^(n-s)` нужна для подсчёта "плохих"
рестрикций и последующего извлечения "хорошей" через `exists_not_mem_of_subset_card_lt`.
-/

/-- Явная формула для кардинала `R_s`. -/
lemma card_R_s (n s : Nat) :
    (R_s (n := n) s).card = Nat.choose n s * 2 ^ (n - s) := by
  simpa [R_s] using
    (Restriction.restrictionsWithFreeCount_card (n := n) (s := s))

@[simp] lemma card_R_exact (n L : Nat) :
    (R_exact n L).card = Nat.choose n L * 2 ^ (n - L) := by
  simpa [R_exact] using card_R_s (n := n) (s := L)

/-- Кардинал `R_s` положителен при `s ≤ n`. -/
lemma card_R_s_pos {s : Nat} (hs : s ≤ n) :
    0 < (R_s (n := n) s).card := by
  simpa [R_s] using
    (Restriction.restrictionsWithFreeCount_card_pos (n := n) (s := s) hs)

/-- Непустота `R_s` при `s ≤ n`. -/
lemma R_s_nonempty {s : Nat} (hs : s ≤ n) :
    (R_s (n := n) s).Nonempty := by
  simpa [R_s] using
    (Restriction.restrictionsWithFreeCount_nonempty (n := n) (s := s) hs)

/-!
### Грубые оценки сверху

Эти оценки полезны для "первого прохода", когда нужно быстро получить
полиномиальную (или экспоненциальную) верхнюю границу без точной формулы.
-/

/-- Грубая оценка: `|R_s| ≤ n^s * 2^(n-s)`. -/
lemma card_R_s_le_pow (n s : Nat) :
    (R_s (n := n) s).card ≤ n ^ s * 2 ^ (n - s) := by
  -- Подставляем формулу и ограничиваем биномиальный коэффициент.
  have hchoose : Nat.choose n s ≤ n ^ s := Nat.choose_le_pow n s
  calc
    (R_s (n := n) s).card
        = Nat.choose n s * 2 ^ (n - s) := card_R_s (n := n) (s := s)
    _ ≤ n ^ s * 2 ^ (n - s) := by
          exact Nat.mul_le_mul_right (2 ^ (n - s)) hchoose

/-- Грубая оценка отношения `|R_{s-t}| / |R_s|` без тонких биномиальных фактов. -/
lemma card_R_s_ratio_le_coarse {n s t : Nat} (hs : s ≤ n) :
    (R_s (n := n) (s - t)).card ≤
      (R_s (n := n) s).card * (2 ^ (n + t) * n ^ (s - t)) := by
  -- Числитель: грубая оценка через `card_R_s_le_pow`.
  have hnum :
      (R_s (n := n) (s - t)).card
        ≤ n ^ (s - t) * 2 ^ (n - (s - t)) :=
    card_R_s_le_pow (n := n) (s := s - t)
  -- Ослабляем степень `2^(n-(s-t))` до `2^(n+t)`.
  have hpow :
      2 ^ (n - (s - t)) ≤ 2 ^ (n + t) := by
    have hle : n - (s - t) ≤ n + t := by
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hle
  -- Получаем "сырой" верхний предел на числитель.
  have hnum' :
      (R_s (n := n) (s - t)).card
        ≤ n ^ (s - t) * 2 ^ (n + t) := by
    exact Nat.le_trans hnum (Nat.mul_le_mul (Nat.le_refl _) hpow)
  -- Нижняя граница для знаменателя: `|R_s| ≥ 1`.
  have hden_pos : 0 < (R_s (n := n) s).card :=
    card_R_s_pos (n := n) (s := s) hs
  have hden : 1 ≤ (R_s (n := n) s).card := Nat.succ_le_iff.mpr hden_pos
  -- Конечный шаг: домножаем грубую оценку на `|R_s|`.
  have hmul :
      n ^ (s - t) * 2 ^ (n + t)
        ≤ (R_s (n := n) s).card * (2 ^ (n + t) * n ^ (s - t)) := by
    -- Используем `1 ≤ |R_s|`.
    have : n ^ (s - t) * 2 ^ (n + t)
        ≤ (n ^ (s - t) * 2 ^ (n + t)) * (R_s (n := n) s).card := by
      exact Nat.le_mul_of_pos_right _ hden_pos
    -- Переставляем множители в правой части.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  exact Nat.le_trans hnum' hmul

end MultiSwitching
end AC0
end Pnp3
