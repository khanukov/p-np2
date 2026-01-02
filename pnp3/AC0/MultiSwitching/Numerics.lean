import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import AC0.MultiSwitching.Restrictions

/-!
  pnp3/AC0/MultiSwitching/Numerics.lean

  Числовые оценки для шага 3.2 (strict bound `|Bad| < |R_s|`).

  Мы работаем в модели `R_s` с `freeCount = s` и используем
  **малый алфавит** трасс `2*(w+1)` (без `n` в степени).

  Ключевой технический факт: биномиальное отношение оценивается без
  лишней экспоненты по `n`, через индукцию по `t` и тождество
  `choose_succ_right_eq`.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-!
## Биномиальная оценка без делений

Мы доказываем натуральное неравенство

`choose n (s - t) * (n - s + 1)^t ≤ choose n s * s^t`,

которое эквивалентно стандартной дробной оценке
`choose(n, s - t) / choose(n, s) ≤ (s / (n - s + 1))^t`,
но не требует делений и работает в `Nat`.
-/

lemma choose_step_le
    (n s k : Nat) (hs : s ≤ n) (hk : k < s) :
    Nat.choose n k * (n - s + 1) ≤ Nat.choose n (k + 1) * s := by
  -- Тождество: C(n,k+1) * (k+1) = C(n,k) * (n-k).
  have hchoose := Nat.choose_succ_right_eq n k
  -- Оценка `n - s + 1 ≤ n - k`.
  have hnk : n - s + 1 ≤ n - k := by
    omega
  -- Оценка `k+1 ≤ s`.
  have hk1 : k + 1 ≤ s := Nat.succ_le_of_lt hk
  calc
    Nat.choose n k * (n - s + 1)
        ≤ Nat.choose n k * (n - k) := by
              exact Nat.mul_le_mul_left _ hnk
    _ = Nat.choose n (k + 1) * (k + 1) := by
          -- Переставляем множители по тождеству.
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hchoose.symm
    _ ≤ Nat.choose n (k + 1) * s := by
          exact Nat.mul_le_mul_left _ hk1

lemma choose_mul_pow_le
    (n s t : Nat) (hs : s ≤ n) (ht : t ≤ s) :
    Nat.choose n (s - t) * (n - s + 1) ^ t ≤ Nat.choose n s * s ^ t := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have ht' : Nat.succ t ≤ s := ht
      have ht_le : t ≤ s := Nat.le_of_succ_le ht'
      -- Шаговая оценка для `k = s - (t+1)`.
      have hk : s - Nat.succ t < s := by
        omega
      have hstep :
          Nat.choose n (s - Nat.succ t) * (n - s + 1)
            ≤ Nat.choose n (s - t) * s := by
        have h := choose_step_le (n := n) (s := s) (k := s - Nat.succ t) hs hk
        -- В тождестве `k+1` соответствует `s - t`.
        have hk1 : s - Nat.succ t + 1 = s - t := by
          omega
        simpa [hk1] using h
      -- Домножаем на `(n - s + 1)^t` и объединяем с IH.
      have hstep' :
          Nat.choose n (s - Nat.succ t) * (n - s + 1) ^ Nat.succ t
            ≤ Nat.choose n (s - t) * s * (n - s + 1) ^ t := by
        -- Переписываем степень и группируем множители.
        have := Nat.mul_le_mul_right ((n - s + 1) ^ t) hstep
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      have ih' :
          Nat.choose n (s - t) * s * (n - s + 1) ^ t
            ≤ Nat.choose n s * s ^ t * s := by
        have := Nat.mul_le_mul_right s (ih ht_le)
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      calc
        Nat.choose n (s - Nat.succ t) * (n - s + 1) ^ Nat.succ t
            ≤ Nat.choose n (s - t) * s * (n - s + 1) ^ t := hstep'
        _ ≤ Nat.choose n s * s ^ t * s := ih'
        _ = Nat.choose n s * s ^ Nat.succ t := by
              simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-!
## Ratio-оценка в `ℚ`

Удобная обёртка для последующего умножения на `(2*(w+1))^t`.
-/

lemma choose_ratio_le_pow
    (n s t : Nat) (hs : s ≤ n) (ht : t ≤ s) :
    ((Nat.choose n (s - t) : ℚ) / (Nat.choose n s : ℚ))
      ≤ ((s : ℚ) / (n - s + 1 : ℚ)) ^ t := by
  have hpos : 0 < (Nat.choose n s : ℚ) := by
    exact_mod_cast (Nat.choose_pos hs)
  have hpos' : 0 < (n - s + 1 : ℚ) := by
    exact_mod_cast (Nat.succ_pos _)
  -- Переносим натуральное неравенство в `ℚ`.
  have hnat :
      (Nat.choose n (s - t) : ℚ) * (n - s + 1 : ℚ) ^ t
        ≤ (Nat.choose n s : ℚ) * (s : ℚ) ^ t := by
    exact_mod_cast (choose_mul_pow_le (n := n) (s := s) (t := t) hs ht)
  -- Делим на положительные знаменатели.
  have hratio :
      (Nat.choose n (s - t) : ℚ) / (Nat.choose n s : ℚ)
        ≤ (s : ℚ) ^ t / (n - s + 1 : ℚ) ^ t := by
    have hpos_pow : 0 < (n - s + 1 : ℚ) ^ t := by
      exact pow_pos hpos' _
    have hpos_choose : 0 < (Nat.choose n s : ℚ) := hpos
    refine (div_le_div_iff₀ hpos_choose hpos_pow).2 ?_
    -- Приводим к форме `a*d ≤ c*b`.
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnat
  -- Финальный шаг: превращаем `a^t / b^t` в `(a/b)^t`.
  -- В ℚ это тождественно.
  have hpow :
      (s : ℚ) ^ t / (n - s + 1 : ℚ) ^ t
        = ((s : ℚ) / (n - s + 1 : ℚ)) ^ t := by
    simpa [div_pow] using
      (div_pow (s : ℚ) (n - s + 1 : ℚ) t).symm
  simpa [hpow] using hratio

/-!
## Специализация для шага 3.2

Определения параметров оставлены как «контракт» для downstream‑кода.
Числовые оценки здесь будут восстановлены в будущих версиях.
-/

def sParam (n w : Nat) : Nat := n / (48 * (w + 1))
def tParam (Flen n : Nat) : Nat := Nat.log2 (Flen * (n + 2)) + 1

end MultiSwitching
end AC0
end Pnp3
