import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import AC0.MultiSwitching.Restrictions
import AC0.MultiSwitching.Params

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

Определения параметров вынесены в `AC0.MultiSwitching.Params`.
Здесь остаются только числовые оценки, опирающиеся на эти параметры.
-/

/-!
## Кардинальная оценка для `R_s`

Следующая лемма — удобный мост к строгостью вида
`|Bad| < |R_s|`: она выражает отношение кардиналов через
биномиальные коэффициенты и степень `(2 * s)^t`.
Это полностью натуральное неравенство, не требующее делений.
-/

lemma card_R_s_mul_pow_le
    (n s t : Nat) (hs : s ≤ n) (ht : t ≤ s) :
    (R_s (n := n) (s - t)).card * (n - s + 1) ^ t
      ≤ (R_s (n := n) s).card * (2 * s) ^ t := by
  -- Основная оценка для биномиальных коэффициентов.
  have hchoose :=
    choose_mul_pow_le (n := n) (s := s) (t := t) hs ht
  -- Уточняем показатель степени `2` в кардинале `R_{s-t}`.
  have hpow : n - (s - t) = n - s + t := by
    omega
  -- Преобразуем через явную формулу для `|R_s|`.
  calc
    (R_s (n := n) (s - t)).card * (n - s + 1) ^ t
        = (Nat.choose n (s - t) * 2 ^ (n - (s - t))) * (n - s + 1) ^ t := by
            simp [card_R_s]
    _ = (Nat.choose n (s - t) * (n - s + 1) ^ t) * 2 ^ (n - (s - t)) := by
          ac_rfl
    _ = (Nat.choose n (s - t) * (n - s + 1) ^ t) * 2 ^ (n - s + t) := by
          simp [hpow]
    _ ≤ (Nat.choose n s * s ^ t) * 2 ^ (n - s + t) := by
          exact Nat.mul_le_mul_right _ hchoose
    _ = (Nat.choose n s * 2 ^ (n - s)) * (2 * s) ^ t := by
          have hpow_add : 2 ^ (n - s + t) = 2 ^ (n - s) * 2 ^ t := by
            simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          have hmul_pow : (2 * s) ^ t = 2 ^ t * s ^ t := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              (Nat.mul_pow 2 s t)
          calc
            (Nat.choose n s * s ^ t) * 2 ^ (n - s + t)
                = (Nat.choose n s * s ^ t) * (2 ^ (n - s) * 2 ^ t) := by
                    simp [hpow_add]
            _ = (Nat.choose n s * 2 ^ (n - s)) * (2 ^ t * s ^ t) := by
                    ac_rfl
            _ = (Nat.choose n s * 2 ^ (n - s)) * (2 * s) ^ t := by
                    simp [hmul_pow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ = (R_s (n := n) s).card * (2 * s) ^ t := by
          simp [card_R_s, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-!
## Усиленная форма: добавляем базу `B` в степенной множитель

Эта лемма комбинирует "ratio"-оценку для `R_s` с дополнительной
границей на базу `B`.  Она полезна как промежуточный шаг для
доказательств вида `|R_{s-t}| * B^t < |R_s|`, когда удаётся показать,
что `(2*s*B)^t` доминируется `(n - s + 1)^t`.
-/

lemma card_R_s_mul_pow_le_with_base
    (n s t B : Nat) (hs : s ≤ n) (ht : t ≤ s)
    (hbase : 2 * s * B ≤ n - s + 1) :
    (R_s (n := n) (s - t)).card * (n - s + 1) ^ t * B ^ t
      ≤ (R_s (n := n) s).card * (n - s + 1) ^ t := by
  -- Первая часть: ratio-оценка из `card_R_s_mul_pow_le`.
  have hratio := card_R_s_mul_pow_le (n := n) (s := s) (t := t) hs ht
  -- Вторая часть: `B` поглощается, если `2*s*B ≤ n - s + 1`.
  have hpow_base : (2 * s) ^ t * B ^ t ≤ (n - s + 1) ^ t := by
    have hpow' : (2 * s * B) ^ t ≤ (n - s + 1) ^ t := by
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hbase
    have hmul_pow :
        (2 * s) ^ t * B ^ t = (2 * s * B) ^ t := by
      -- `(a*b)^t = a^t * b^t` для натуральных.
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.mul_pow (2 * s) B t)
    simpa [hmul_pow] using hpow'
  calc
    (R_s (n := n) (s - t)).card * (n - s + 1) ^ t * B ^ t
        ≤ (R_s (n := n) s).card * (2 * s) ^ t * B ^ t := by
            -- Домножаем ratio-оценку на `B^t`.
            exact Nat.mul_le_mul_right _ hratio
    _ ≤ (R_s (n := n) s).card * (n - s + 1) ^ t := by
          -- Используем поглощение базы `B`.
          have hmul := Nat.mul_le_mul_left (R_s (n := n) s).card hpow_base
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-!
## Шаблон для строгой оценки с множителем `m+1`

Эта лемма не закрывает Step 3.2 полностью, но изолирует два
ключевых "числовых" условия:

1. `2 * s * B ≤ n - s + 1` — база поглощается размером пространства.
2. `(m+1) * B^t < (n - s + 1)^t` — множитель `m+1` убивается степенью.

При их выполнении получаем строгую оценку, совместимую с
`Counting.lean` (в виде `|R_{s-t}| * (m+1) * B^t < ...`).
-/

lemma card_R_s_mul_pow_lt_with_multiplier
    (n s t B m : Nat) (hs : s ≤ n) (ht : t ≤ s)
    (hbase : 2 * s * B ≤ n - s + 1)
    (hsize : (m + 1) * B ^ t < (n - s + 1) ^ t) :
    (R_s (n := n) (s - t)).card * (m + 1) * B ^ t
      < (R_s (n := n) s).card * (n - s + 1) ^ t := by
  -- Сначала поднимаем множитель `m+1` до `(n-s+1)^t`.
  have hmul :
      (R_s (n := n) (s - t)).card * (m + 1) * B ^ t
        < (R_s (n := n) (s - t)).card * (n - s + 1) ^ t * B ^ t := by
    -- Домножаем строгую оценку `hsize` на `|R_{s-t}|`.
    have hsize' :
        (R_s (n := n) (s - t)).card * ((m + 1) * B ^ t)
          < (R_s (n := n) (s - t)).card * (n - s + 1) ^ t := by
      exact Nat.mul_lt_mul_left _ hsize
    -- Переставляем множители в нужный вид.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsize'
  -- Затем применяем основную base‑лемму.
  have hbase' :=
    card_R_s_mul_pow_le_with_base (n := n) (s := s) (t := t) (B := B) hs ht hbase
  exact lt_of_lt_of_le hmul hbase'

/-!
## Специализация базовой оценки для `sParam` и `BParam`

Следующая лемма фиксирует, что при выбранных параметрах
`sParam` и `BParam` базовый множитель действительно "поглощается"
размером пространства `R_s`.  Это ровно тот числовой шаг,
который затем подставляется в шаблон строгой оценки.
-/

lemma base_absorbs_sParam (n w : Nat) :
    2 * sParam n w * BParam w ≤ n - sParam n w + 1 := by
  -- Обозначаем знаменатель `k = 49*(w+1)` и используем разложение `n`.
  set k : Nat := 49 * (w + 1)
  have hs : sParam n w = n / k := by
    simp [sParam, k]
  have hdecomp : n = k * (n / k) + n % k := by
    -- `n = k*(n/k) + n%k` — стандартное разложение по модулю.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mod_add_div n k).symm
  -- Показываем, что коэффициент перед `sParam` достаточно мал.
  have hcoeff : 2 * BParam w ≤ k - 1 := by
    -- `2*BParam = 4*(w+1)` и это существенно меньше `49*(w+1) - 1`.
    simp [BParam, k]
    omega
  -- Переходим к оценке с учётом множителя `sParam`.
  have hbase : 2 * sParam n w * BParam w ≤ (k - 1) * (n / k) := by
    -- Используем `hcoeff` и монотонность умножения.
    have hmul := Nat.mul_le_mul_right (n / k) hcoeff
    -- Упорядочиваем множители.
    simpa [hs, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  -- Остаётся показать `(k-1)*s ≤ n - s + 1`.
  -- Из разложения `n = k*s + r` следует
  -- `n - s + 1 = (k-1)*s + r + 1 ≥ (k-1)*s`.
  have hrest :
      (k - 1) * (n / k) ≤ n - (n / k) + 1 := by
    -- Подставляем разложение и используем монотонность сложения.
    -- Это чистая арифметика на `Nat` (без делений).
    have hkpos : 0 < k := by
      have : 0 < w + 1 := Nat.succ_pos _
      exact Nat.mul_pos (by decide : 0 < (49 : Nat)) this
    have hk : k = (k - 1) + 1 := by
      -- `k` положителен, значит `k = (k-1)+1`.
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hkpos).symm
    have hk_mul : k * (n / k) = (k - 1) * (n / k) + (n / k) := by
      calc
        k * (n / k) = ((k - 1) + 1) * (n / k) := by simpa [hk]
        _ = (k - 1) * (n / k) + 1 * (n / k) := by
              simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (k - 1) * (n / k) + (n / k) := by simp
    have hsub : k * (n / k) - (n / k) = (k - 1) * (n / k) := by
      -- `(k-1)*s + s - s = (k-1)*s`.
      calc
        k * (n / k) - (n / k)
            = ((k - 1) * (n / k) + (n / k)) - (n / k) := by
                simpa [hk_mul]
        _ = (k - 1) * (n / k) := by
              simpa [Nat.add_sub_cancel]
    -- Теперь раскрываем `n` через `k*s + r`.
    calc
      (k - 1) * (n / k)
          = k * (n / k) - (n / k) := by simpa [hsub]
      _ ≤ (k * (n / k) + n % k) - (n / k) := by
            -- добавляем `n%k` справа
            exact Nat.sub_le_sub_left (Nat.le_add_right _ _) _
      _ = n - (n / k) := by
            -- подставляем разложение `n = k*s + r`
            simpa [hdecomp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ ≤ n - (n / k) + 1 := by
            exact Nat.le_add_right _ _
  exact hbase.trans hrest

/-!
## Строгая версия поглощения базы для `sParam`

Если `n` как минимум `49*(w+1)`, то величина `n - sParam n w + 1`
строго больше `12 * BParam w`.  Это точный "жёсткий" вариант,
который нужен для Step 3.2.
-/

lemma base_absorbs_sParam_strict (n w : Nat)
    (hN : 49 * (w + 1) ≤ n) :
    12 * BParam w < n - sParam n w + 1 := by
  -- Вводим обозначения `k` и `q = n / k`.
  set k : Nat := 49 * (w + 1)
  set q : Nat := n / k
  have hkpos : 0 < k := by
    have : 0 < w + 1 := Nat.succ_pos _
    exact Nat.mul_pos (by decide : 0 < (49 : Nat)) this
  have hqpos : 1 ≤ q := by
    -- `q = n/k`, а `n ≥ k`.
    have : 1 * k ≤ n := by simpa [k] using hN
    exact (Nat.le_div_iff_mul_le hkpos).2 this
  have hdecomp : n = k * q + n % k := by
    simpa [q, k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mod_add_div n k).symm
  -- Оценка `(k-1)*q ≤ n - q + 1` (как в `base_absorbs_sParam`).
  have hrest : (k - 1) * q ≤ n - q + 1 := by
    have hk : k = (k - 1) + 1 := by
      -- `k` положителен, значит `k = (k-1)+1`.
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hkpos).symm
    have hk_mul : k * q = (k - 1) * q + q := by
      calc
        k * q = ((k - 1) + 1) * q := by simpa [hk]
        _ = (k - 1) * q + 1 * q := by
              simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (k - 1) * q + q := by simp
    have hsub : k * q - q = (k - 1) * q := by
      calc
        k * q - q
            = ((k - 1) * q + q) - q := by simpa [hk_mul]
        _ = (k - 1) * q := by simpa [Nat.add_sub_cancel]
    calc
      (k - 1) * q
          = k * q - q := by simpa [hsub]
      _ ≤ (k * q + n % k) - q := by
            exact Nat.sub_le_sub_left (Nat.le_add_right _ _) _
      _ = n - q := by
            simpa [hdecomp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ ≤ n - q + 1 := by
            exact Nat.le_add_right _ _
  -- Из `q ≥ 1` получаем `(k-1) ≤ (k-1)*q`.
  have hmul : k - 1 ≤ (k - 1) * q := by
    have hqpos' : 0 < q := Nat.succ_le_iff.mp hqpos
    exact Nat.le_mul_of_pos_right _ hqpos'
  have hge : k - 1 ≤ n - q + 1 := by
    exact hmul.trans hrest
  -- Сравнение коэффициентов: `12*BParam = 24*(w+1) < k-1`.
  have hcoeff : 12 * BParam w < k - 1 := by
    -- `k = 49*(w+1)`, поэтому разница строго положительна.
    simp [BParam, k]
    omega
  -- Собираем итоговую строгую оценку.
  have hge' : k - 1 < n - q + 1 := lt_of_lt_of_le hcoeff hge
  simpa [sParam, q] using hge'

/-!
## Усиленная оценка базы с фактором `2*s`

Для финальной формы Step 3.2 нам нужно подавить множитель
`(2 * s)^t` вместе с кодовой базой `B`.  При новых числовых
параметрах `sParam` это достигается через более сильную оценку
`12 * (2*s*B) < n - s + 1`.
-/

lemma base_absorbs_sParam_strict_scaled (n w : Nat)
    (hN : 49 * (w + 1) ≤ n) :
    12 * (2 * sParam n w * BParam w) < n - sParam n w + 1 := by
  set k : Nat := 49 * (w + 1)
  set q : Nat := n / k
  have hkpos : 0 < k := by
    have : 0 < w + 1 := Nat.succ_pos _
    exact Nat.mul_pos (by decide : 0 < (49 : Nat)) this
  have hqpos : 1 ≤ q := by
    -- `q = n/k`, а `n ≥ k`.
    have : 1 * k ≤ n := by simpa [k] using hN
    exact (Nat.le_div_iff_mul_le hkpos).2 this
  have hdecomp : n = k * q + n % k := by
    simpa [q, k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mod_add_div n k).symm
  -- Оценка `(k-1)*q ≤ n - q + 1` (как в `base_absorbs_sParam_strict`).
  have hrest : (k - 1) * q ≤ n - q + 1 := by
    have hk : k = (k - 1) + 1 := by
      -- `k` положителен, значит `k = (k-1)+1`.
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hkpos).symm
    have hk_mul : k * q = (k - 1) * q + q := by
      calc
        k * q = ((k - 1) + 1) * q := by simpa [hk]
        _ = (k - 1) * q + 1 * q := by
              simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (k - 1) * q + q := by simp
    have hsub : k * q - q = (k - 1) * q := by
      calc
        k * q - q
            = ((k - 1) * q + q) - q := by simpa [hk_mul]
        _ = (k - 1) * q := by simpa [Nat.add_sub_cancel]
    calc
      (k - 1) * q
          = k * q - q := by simpa [hsub]
      _ ≤ (k * q + n % k) - q := by
            exact Nat.sub_le_sub_left (Nat.le_add_right _ _) _
      _ = n - q := by
            simpa [hdecomp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ ≤ n - q + 1 := by
            exact Nat.le_add_right _ _
  -- Сравнение коэффициентов: `12 * (2*BParam) = 48*(w+1) < k-1`.
  have hcoeff : 12 * (2 * BParam w) < k - 1 := by
    simp [BParam, k]
    omega
  have hmul :
      12 * (2 * BParam w) * q < (k - 1) * q := by
    have hqpos' : 0 < q := Nat.succ_le_iff.mp hqpos
    exact Nat.mul_lt_mul_of_pos_right hcoeff hqpos'
  -- Переходим к `sParam` и собираем итоговую оценку.
  have hbase :
      12 * (2 * sParam n w * BParam w) < (k - 1) * q := by
    -- `sParam n w = q` и раскрытие скобок.
    simpa [sParam, q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact lt_of_lt_of_le hbase hrest

/-!
## Подавление множителя `(m+1)` через `tParam`

Этот шаг формализует стандартный трюк:

* `m+1 ≤ 12^t` (из определения `tParam`),
* `(12 * B)^t < (n - s + 1)^t` при строгой оценке базы,

что вместе даёт строгую оценку
`(m+1) * B^t < (n - s + 1)^t`.

Лемма оставляет параметры абстрактными, чтобы её можно было
использовать в разных ветках (CNF/DNF).
-/

lemma multiplier_suppressed_of_bounds
    (n s t B m : Nat)
    (hpos : 0 < t)
    (hbase : 12 * B < n - s + 1)
    (hm : m + 1 ≤ 12 ^ t) :
    (m + 1) * B ^ t < (n - s + 1) ^ t := by
  -- Поднимаем `(m+1)` до `12^t`.
  have hmul :
      (m + 1) * B ^ t ≤ 12 ^ t * B ^ t := by
    exact Nat.mul_le_mul_right _ hm
  -- Сливаем множители в `(12*B)^t`.
  have hmul_pow : 12 ^ t * B ^ t = (12 * B) ^ t := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_pow 12 B t).symm
  have hpow : (12 * B) ^ t < (n - s + 1) ^ t := by
    -- Строгость сохраняется при возведении в степень.
    exact Nat.pow_lt_pow_of_lt_left hbase hpos
  -- Итоговая строгая оценка.
  calc
    (m + 1) * B ^ t ≤ 12 ^ t * B ^ t := hmul
    _ = (12 * B) ^ t := hmul_pow
    _ < (n - s + 1) ^ t := hpow

/-!
## Закрывающая числовая лемма Step 3.2

`numerical_inequality_3_2` объединяет:

* строгую базовую оценку `12 * BParam < n - sParam + 1`;
* рост `tParam`, дающий `m+1 ≤ 12^t`;
* шаблон строгой оценки для `|R_s|`.

Это готовая подстановка для `Counting.lean`.
-/

lemma numerical_inequality_3_2 (n w m : Nat)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam m n ≤ sParam n w) :
    (R_s (n := n) (sParam n w - tParam m n)).card * (m + 1)
        * (BParam w) ^ (tParam m n)
      < (R_s (n := n) (sParam n w)).card
        * (n - sParam n w + 1) ^ (tParam m n) := by
  -- Сначала докажем строгую оценку `(m+1) * B^t < (n - s + 1)^t`.
  have htpos : 0 < tParam m n := by
    -- `tParam = log2(...) + 1`.
    simpa [tParam] using
      (Nat.succ_pos (Nat.log2 ((m + 1) * (n + 2))))
  have hbase : 12 * BParam w < n - sParam n w + 1 :=
    base_absorbs_sParam_strict (n := n) (w := w) hN
  have hm : m + 1 ≤ 12 ^ (tParam m n) :=
    m_plus_one_le_pow_twelve_tParam m n
  have hsize :
      (m + 1) * (BParam w) ^ (tParam m n)
        < (n - sParam n w + 1) ^ (tParam m n) := by
    exact multiplier_suppressed_of_bounds
      (n := n) (s := sParam n w) (t := tParam m n)
      (B := BParam w) (m := m) htpos hbase hm
  -- Теперь применяем общий шаблон с `sParam`/`BParam`.
  have hs : sParam n w ≤ n := by
    simpa [sParam] using Nat.div_le_self n (49 * (w + 1))
  have hbase' : 2 * sParam n w * BParam w ≤ n - sParam n w + 1 := by
    exact base_absorbs_sParam (n := n) (w := w)
  exact card_R_s_mul_pow_lt_with_multiplier
    (n := n) (s := sParam n w) (t := tParam m n)
    (B := BParam w) (m := m) hs ht hbase' hsize

/-!
## Финальная форма числовой оценки Step 3.2

Эта лемма убирает дополнительный множитель `(n - s + 1)^t` справа,
что позволяет напрямую применить `exists_good_of_card_lt`.
Мы используем более сильную оценку базы `12 * (2*s*B) < n - s + 1`
и затем сокращаем множитель `(2*s)^t`.
-/

lemma numerical_inequality_3_2_final (n w m : Nat)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam m n ≤ sParam n w) :
    (R_s (n := n) (sParam n w - tParam m n)).card * (m + 1)
        * (BParam w) ^ (tParam m n)
      < (R_s (n := n) (sParam n w)).card := by
  set s : Nat := sParam n w
  set t : Nat := tParam m n
  set B : Nat := BParam w
  have htpos : 0 < t := by
    -- `tParam = log2(...) + 1`.
    simpa [t, tParam] using
      (Nat.succ_pos (Nat.log2 ((m + 1) * (n + 2))))
  have hspos : 0 < s := by
    -- `sParam` положителен при `n ≥ 49*(w+1)`.
    simpa [s] using (sParam_pos_of_le (n := n) (w := w) hN)
  have hbase :
      12 * (2 * s * B) < n - s + 1 := by
    simpa [s, B] using
      (base_absorbs_sParam_strict_scaled (n := n) (w := w) hN)
  have hm : m + 1 ≤ 12 ^ t := by
    simpa [t] using m_plus_one_le_pow_twelve_tParam m n
  have hsize :
      (m + 1) * (2 * s * B) ^ t < (n - s + 1) ^ t := by
    exact multiplier_suppressed_of_bounds
      (n := n) (s := s) (t := t) (B := 2 * s * B) (m := m)
      htpos hbase hm
  have hs : s ≤ n := by
    simpa [s, sParam] using Nat.div_le_self n (49 * (w + 1))
  have hcard :
      (R_s (n := n) (s - t)).card * (n - s + 1) ^ t
        ≤ (R_s (n := n) s).card * (2 * s) ^ t := by
    simpa [s, t] using (card_R_s_mul_pow_le (n := n) (s := s) (t := t) hs ht)
  have hlt :
      (R_s (n := n) (s - t)).card * (m + 1) * (2 * s * B) ^ t
        < (R_s (n := n) s).card * (2 * s) ^ t := by
    have hsize' :
        (R_s (n := n) (s - t)).card
            * ((m + 1) * (2 * s * B) ^ t)
          < (R_s (n := n) (s - t)).card * (n - s + 1) ^ t := by
      exact Nat.mul_lt_mul_left _ hsize
    -- Сравниваем с `|R_s| * (2*s)^t`.
    exact lt_of_lt_of_le
      (by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsize')
      hcard
  -- Переписываем `(2*s*B)^t` и сокращаем `(2*s)^t`.
  have hmul_pow : (2 * s * B) ^ t = (2 * s) ^ t * B ^ t := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_pow (2 * s) B t)
  have hpos : 0 < (2 * s) ^ t := by
    have hpos' : 0 < 2 * s := Nat.mul_pos (by decide : 0 < (2 : Nat)) hspos
    exact Nat.pow_pos hpos' _
  have hlt' :
      (R_s (n := n) (s - t)).card * (m + 1) * B ^ t * (2 * s) ^ t
        < (R_s (n := n) s).card * (2 * s) ^ t := by
    simpa [hmul_pow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
  -- Сокращаем общий множитель `(2*s)^t`.
  exact (Nat.lt_of_mul_lt_mul_right hlt' hpos)

/-!
## Расширенная база: `(2*n) * BParam`

Для «широкого» кодирования (когда мы явно записываем выбранную переменную)
нужна оценка с базой `2*n * BParam`.  В отличие от компактного случая,
получить её **без дополнительных гипотез** нельзя, поэтому мы оставляем
в лемме явное условие `hsize` на подавление множителя.

Эта форма согласуется с counting‑веткой, где база равна
`(2*n)^t * (2*(w+1))^t = (2*n*BParam w)^t`.
-/

lemma numerical_inequality_3_2_final_expanded
    (n w m : Nat)
    (hN : 49 * (w + 1) ≤ n)
    (ht : tParam m n ≤ sParam n w)
    (hsize :
      (m + 1) * (2 * n * BParam w) ^ (tParam m n)
        < (n - sParam n w + 1) ^ (tParam m n)) :
    (R_s (n := n) (sParam n w - tParam m n)).card * (m + 1)
        * (2 * n * BParam w) ^ (tParam m n)
      < (R_s (n := n) (sParam n w)).card := by
  set s : Nat := sParam n w
  set t : Nat := tParam m n
  have htpos : 0 < t := by
    simpa [t, tParam] using
      (Nat.succ_pos (Nat.log2 ((m + 1) * (n + 2))))
  have hspos : 0 < s := by
    simpa [s] using (sParam_pos_of_le (n := n) (w := w) hN)
  have hs : s ≤ n := by
    simpa [s, sParam] using Nat.div_le_self n (49 * (w + 1))
  have hcard :
      (R_s (n := n) (s - t)).card * (n - s + 1) ^ t
        ≤ (R_s (n := n) s).card * (2 * s) ^ t := by
    simpa [s, t] using (card_R_s_mul_pow_le (n := n) (s := s) (t := t) hs ht)
  have hlt :
      (R_s (n := n) (s - t)).card * (m + 1) * (2 * n * BParam w) ^ t
        < (R_s (n := n) s).card * (2 * s) ^ t := by
    have hsize' :
        (R_s (n := n) (s - t)).card
            * ((m + 1) * (2 * n * BParam w) ^ t)
          < (R_s (n := n) (s - t)).card * (n - s + 1) ^ t := by
      exact Nat.mul_lt_mul_left _ hsize
    exact lt_of_lt_of_le
      (by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsize')
      hcard
  have hpos : 0 < (2 * s) ^ t := by
    have hpos' : 0 < 2 * s := Nat.mul_pos (by decide : 0 < (2 : Nat)) hspos
    exact Nat.pow_pos hpos' _
  -- Сокращаем общий множитель `(2*s)^t`.
  exact (Nat.lt_of_mul_lt_mul_right
    (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt) hpos)

end MultiSwitching
end AC0
end Pnp3
