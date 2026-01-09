import Counting.BinomialBounds

/-!
  pnp3/Counting/CapacityGap.lean

  В этом файле мы собираем «итоговый разрыв» для ёмкости:
  объединяем грубую оценку `unionBound` и строгую оценку на
  хаммингов шар при `ε = 1/(n+2)`.

  Это позволяет в шагах C/D напрямую получить строгий разрыв
  `capacityBound < 2^(2^n)` (после подстановки численных
  ограничений на словарь).
-/

namespace Pnp3
namespace Counting

/--
  Если заранее известно, что словарная часть `unionBound` не превосходит
  `2^(N/(n+2))` при `N = 2^n`, то ёмкость уже строго меньше `2^N`.

  Важный момент: мы используем **строгое** неравенство на объём хаммингового
  шара и отдельно контролируем «запас» `t = N/(n+2)`; в итоге разрыв
  складывается в точное `2^N`.
-/
lemma capacityBound_twoPow_lt_twoPowPow
    (n D k : Nat) (hn : 8 ≤ n)
    (hε0 : (0 : Rat) ≤ (1 : Rat) / (n + 2))
    (hε1 : (1 : Rat) / (n + 2) ≤ (1 : Rat) / 2)
    (hU :
      unionBound D k ≤ Nat.pow 2 (Nat.pow 2 n / (n + 2))) :
    capacityBound D k (Nat.pow 2 n) ((1 : Rat) / (n + 2)) hε0 hε1
      < Nat.pow 2 (Nat.pow 2 n) := by
  classical
  -- Обозначения: `N = 2^n` и `t = N/(n+2)`.
  set N := Nat.pow 2 n
  set t := N / (n + 2)
  -- Явная верхняя оценка на хаммингов шар.
  have hball_bound :
      hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1
        ≤ (t + 2) * N ^ (t + 1) := by
    dsimp [N, t]
    exact hammingBallBound_twoPow_le_mul_pow_div_add_one n hε0 hε1
  -- Положительность `N`.
  have hNpos : 0 < N := by
    have htwo : 0 < (2 : Nat) := by decide
    dsimp [N]
    exact Nat.pow_pos htwo
  -- Условие `t ≥ 2n`, необходимое для оценки показателей.
  have ht_ge : 2 * n ≤ t := by
    have hmul : 2 * n * (n + 2) ≤ N := by
      -- Прямо подставляем `N = 2^n`.
      simpa [N] using (twoPow_ge_twoMul_mul n hn)
    have hpos : 0 < n + 2 := by
      exact Nat.succ_pos (n + 1)
    have hdiv :
        2 * n ≤ N / (n + 2) :=
      (Nat.le_div_iff_mul_le hpos).2 hmul
    simpa [t] using hdiv
  -- Переходим от оценки шара к степени `N^(t+2)`.
  have hmul_pow :
      (t + 2) * N ^ (t + 1) < N ^ (t + 2) := by
    -- Достаточно показать `t + 2 < N`.
    have ht_lt : t + 2 < N := by
      -- Из `n*(t+2) < N` следует `t+2 < N`, так как `n ≥ 1`.
      have hn_pos : 0 < n := by
        exact Nat.succ_le_iff.mp (le_trans (by decide : 1 ≤ 8) hn)
      -- Оцениваем `n*(t+2)` через `2^n` (как в основной лемме).
      have hExp : n * (t + 2) < N := by
        -- Используем уже доказанную оценку `n*(n+2) < 2^n` и монотонность `t`.
        have ht_ge_n : n ≤ t := by
          -- Из `n*(n+2) ≤ N` получаем `n ≤ t`.
          have hmul_n : n * (n + 2) ≤ N := le_of_lt (twoPow_gt_mul n hn)
          have hpos : 0 < n + 2 := by
            exact Nat.succ_pos (n + 1)
          have hdiv : n ≤ N / (n + 2) :=
            (Nat.le_div_iff_mul_le hpos).2 hmul_n
          simpa [t] using hdiv
        by_cases ht : t = n
        · simpa [t, ht, N] using twoPow_gt_mul n hn
        · have hlt : n < t := lt_of_le_of_ne ht_ge_n (Ne.symm ht)
          have h2lt : 2 * n < 2 * t := by
            exact Nat.mul_lt_mul_of_pos_left hlt (by decide : 0 < (2 : Nat))
          have hlt_mul : n * t + 2 * n < n * t + 2 * t := by
            exact Nat.add_lt_add_left h2lt (n * t)
          have hlt_mul' : n * (t + 2) < (n + 2) * t := by
            simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.mul_comm,
              Nat.mul_left_comm, Nat.mul_assoc] using hlt_mul
          -- `(n+2)*t ≤ N` по определению `t`.
          have hmul_le : (n + 2) * t ≤ N := by
            have h := Nat.mul_div_le N (n + 2)
            simpa [t, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
          exact lt_of_lt_of_le hlt_mul' hmul_le
      have hle : t + 2 ≤ n * (t + 2) :=
        Nat.le_mul_of_pos_left _ hn_pos
      exact lt_of_le_of_lt hle hExp
    have hpowpos : 0 < N ^ (t + 1) := by
      exact Nat.pow_pos hNpos
    have hmul_lt := Nat.mul_lt_mul_of_pos_right ht_lt hpowpos
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul_lt
  have hball_lt :
      hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1
        < N ^ (t + 2) := by
    exact lt_of_le_of_lt hball_bound hmul_pow
  -- Теперь связываем показатели: `2^t * N^(t+2) ≤ 2^N`.
  have hsum_le : t + n * (t + 2) ≤ N := by
    have hmul_le : (n + 2) * t ≤ N := by
      have h := Nat.mul_div_le N (n + 2)
      simpa [t, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    -- `(n+1)*t + 2n ≤ (n+2)*t`, так как `2n ≤ t`.
    have hstep : (n + 1) * t + 2 * n ≤ (n + 2) * t := by
      nlinarith [ht_ge]
    have hsum :
        t + n * (t + 2) = (n + 1) * t + 2 * n := by
      nlinarith
    exact (hsum ▸ hstep.trans hmul_le)
  have hpow_le :
      (Nat.pow 2 t) * (N ^ (t + 2)) ≤ Nat.pow 2 N := by
    -- Переводим `N^(t+2)` в `2^(n*(t+2))` и собираем степени.
    have hrewrite :
        (Nat.pow 2 t) * (N ^ (t + 2)) =
          Nat.pow 2 (t + n * (t + 2)) := by
      simp [N, Nat.pow_mul, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm]
    have hpow :
        Nat.pow 2 (t + n * (t + 2)) ≤ Nat.pow 2 N :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hsum_le
    exact hrewrite.symm ▸ hpow
  -- Собираем итоговую цепочку для `capacityBound`.
  have hmul_le :
      unionBound D k *
        hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1
        < Nat.pow 2 t * N ^ (t + 2) := by
    have hstep := Nat.mul_le_mul_right
      (hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1) hU
    have hstep' :
        Nat.pow 2 t *
          hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1
          < Nat.pow 2 t * N ^ (t + 2) := by
      have hpos : 0 < Nat.pow 2 t :=
        Nat.pow_pos (n := t) (by decide : 0 < (2 : Nat))
      exact Nat.mul_lt_mul_of_pos_left hball_lt hpos
    exact lt_of_le_of_lt hstep hstep'
  -- Завершаем: `capacityBound = unionBound * hammingBallBound`.
  have hcap_lt :
      unionBound D k *
        hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1
        < Nat.pow 2 N := by
    exact lt_of_lt_of_le hmul_le hpow_le
  simpa [capacityBound, N] using hcap_lt

end Counting
end Pnp3
