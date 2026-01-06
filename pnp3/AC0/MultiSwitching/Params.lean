import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
  pnp3/AC0/MultiSwitching/Params.lean

  Явные параметры для шага 3.2 (строгая оценка `|Bad| < |R_s|`).
  Здесь мы фиксируем конкретные константы (49, база 12 и т.д.),
  а также минимальные арифметические леммы, необходимые downstream‑коду.

  Важно: эти определения **не** являются частью доказательства
  multi‑switching.  Это "контрактный" слой, который стабилизирует
  числовые параметры и позволяет закрывать Step 3.2 без ручной
  настройки на каждом использовании.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

/-!
## Параметры для шага 3.2

* `sParam` фиксирует число свободных координат (exact‑p модель).
* `BParam` фиксирует базу алфавита кодов на один шаг.
* `tParam` — "безопасный" вариант `⌈log₂((m+1)(n+2))⌉ + 2`,
  удобный для перевода в оценку вида `2^t ≥ (m+1)(n+2)`.
-/

def sParam (n w : Nat) : Nat :=
  n / (49 * (w + 1))

def BParam (w : Nat) : Nat :=
  2 * (w + 1)

/-!
## Параметр глубины ствола

`ℓParam M` — Lean‑дружественная версия `⌈log₂(2M)⌉` с небольшим запасом.
Эта величина используется в глубинной индукции multi‑switching,
но для шага 3.2 она не требуется.
-/

def ℓParam (M : Nat) : Nat :=
  Nat.log2 (2 * M + 1) + 1

def tParam (m n : Nat) : Nat :=
  Nat.log2 ((m + 1) * (n + 2)) + 2

/-!
## Простые леммы о `sParam`

Эти факты используются для разбиения на случаи:
если `n` мало, то `sParam = 0`; если `n` достаточно велико,
то `sParam` положительно.
-/

lemma sParam_eq_zero_of_lt (n w : Nat)
    (h : n < 49 * (w + 1)) :
    sParam n w = 0 := by
  -- `sParam = n / k`, а при `n < k` частное равно нулю.
  have : n / (49 * (w + 1)) = 0 := by
    exact Nat.div_eq_of_lt h
  simpa [sParam] using this

lemma sParam_pos_of_le (n w : Nat)
    (h : 49 * (w + 1) ≤ n) :
    0 < sParam n w := by
  -- `n / k ≥ 1`, если `k ≤ n`.
  have hkpos : 0 < 49 * (w + 1) := by
    have : 0 < w + 1 := Nat.succ_pos _
    exact Nat.mul_pos (by decide : 0 < (49 : Nat)) this
  have hmul : 1 * (49 * (w + 1)) ≤ n := by
    simpa using h
  have hdiv : 1 ≤ n / (49 * (w + 1)) :=
    (Nat.le_div_iff_mul_le hkpos).2 hmul
  exact Nat.succ_le_iff.mp hdiv

/-!
## Полезные вспомогательные оценки

Эти леммы позволяют быстро получать грубые верхние оценки на множители
`(m+1)` через степени `2^t` и `12^t`.  Они будут использоваться
при закрытии строгих числовых неравенств в `Numerics.lean`.
-/

lemma pow_two_le_pow_twelve (t : Nat) :
    2 ^ t ≤ 12 ^ t := by
  -- `12 = 2 * 6`, затем применяем `(a*b)^t = a^t * b^t`.
  have hmul : 12 ^ t = 2 ^ t * 6 ^ t := by
    -- Переписываем через `Nat.mul_pow` и упрощаем.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_pow 2 6 t)
  have hpos : 0 < 6 ^ t := by
    exact Nat.pow_pos (by decide : 0 < (6 : Nat))
  have hle : 2 ^ t ≤ 2 ^ t * 6 ^ t := by
    exact Nat.le_mul_of_pos_right _ hpos
  -- Подставляем разложение `12^t`.
  simpa [hmul] using hle

/-!
## Минимальные факты о `ℓParam`

Эта лемма нужна для перевода `log2`‑определения в форму `2^ℓ ≥ 2M`.
-/

lemma pow_two_le_ℓParam (M : Nat) :
    2 ^ (ℓParam M) ≥ 2 * M := by
  -- Ключевой факт: `x < 2^(log2 x + 1)` для любого `x`.
  have hlt : 2 * M + 1 < 2 ^ (Nat.log2 (2 * M + 1) + 1) := by
    have hlog :
        2 * M + 1 <
          2 ^ (Nat.log 2 (2 * M + 1)).succ := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * M + 1)
    simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using hlog
  -- Ослабляем строгую оценку и убираем `+1`.
  have hle : 2 * M ≤ 2 ^ (Nat.log2 (2 * M + 1) + 1) := by
    exact Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self (2 * M)) hlt)
  simpa [ℓParam] using hle

/-!
## Минимальные факты о `tParam`

Эти леммы дают "грубую" оценку `2^t ≥ (m+1)(n+2)`, которая позже
используется для сравнения с `12^t` и для подавления множителя `|F|`.
-/

lemma pow_two_le_tParam (m n : Nat) :
    2 ^ (tParam m n) ≥ (m + 1) * (n + 2) := by
  -- Ключевой факт: `x < 2^(log2 x + 1)` для любого `x`.
  have hlt :
      (m + 1) * (n + 2) < 2 ^ (Nat.log2 ((m + 1) * (n + 2)) + 1) := by
    have hlog :
        (m + 1) * (n + 2) <
          2 ^ (Nat.log 2 ((m + 1) * (n + 2))).succ := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two ((m + 1) * (n + 2))
    simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using hlog
  have hle :
      (m + 1) * (n + 2) ≤ 2 ^ (Nat.log2 ((m + 1) * (n + 2)) + 1) := by
    exact Nat.le_of_lt hlt
  -- Усиливаем оценку: `tParam` на единицу больше, чем `log2 + 1`.
  have hmono :
      2 ^ (Nat.log2 ((m + 1) * (n + 2)) + 1)
        ≤ 2 ^ (tParam m n) := by
    -- Монотонность `pow` по показателю.
    have hle' :
        Nat.log2 ((m + 1) * (n + 2)) + 1 ≤ tParam m n := by
      -- `tParam = log2(...) + 2`.
      simpa [tParam, Nat.succ_eq_add_one, Nat.add_assoc] using
        (Nat.le_succ (Nat.log2 ((m + 1) * (n + 2)) + 1))
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) hle'
  exact hle.trans hmono

lemma m_plus_one_le_pow_two_tParam (m n : Nat) :
    m + 1 ≤ 2 ^ (tParam m n) := by
  -- `(m+1) ≤ (m+1)*(n+2) ≤ 2^t`.
  have hpos : 0 < n + 2 := by
    exact Nat.succ_pos _
  have hmul : m + 1 ≤ (m + 1) * (n + 2) := by
    exact Nat.le_mul_of_pos_right _ hpos
  exact hmul.trans (pow_two_le_tParam m n)

lemma m_plus_one_le_pow_twelve_tParam (m n : Nat) :
    m + 1 ≤ 12 ^ (tParam m n) := by
  exact (m_plus_one_le_pow_two_tParam m n).trans
    (pow_two_le_pow_twelve (tParam m n))

end MultiSwitching
end AC0
end Pnp3
