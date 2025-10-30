import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Init

/-!
  pnp3/Counting/BinomialBounds.lean

  В этом файле собраны стандартные комбинаторные оценки для шага B.  Теперь
  все необходимые неравенства выводятся строго внутри Lean, поэтому атласные
  ёмкости, используемые в anti-checker, опираются на проверенные подсчёты.

  Основные блоки:

  * биномиальные суммы `∑_{i=0}^k C(D,i)` и их грубая оценка `(k+1)·(max 1 D)^k`;
  * верхняя граница на мощность хаммингового шара через инъекцию в множество
    подмножеств пространства входов;
  * леммы монотонности по размеру словаря и по бюджету ошибок ε, полезные как
    для поиска контрпримеров, так и для аккуратного переноса параметров.

  На основе этих результатов определяется функция `capacityBound` и получаются
  численные ограничения, задействованные в теореме `Counting.covering_power_bound`.
-/

open scoped BigOperators ENNReal

namespace Pnp3
namespace Counting

/--
  Бинарная энтропия `H(ε)` из аналитической оценки объёма хаммингового
  шара.  Пока мы используем её как чистый символ (возвращаем просто `ε`),
  важен лишь факт, что она присутствует в формуле.  Когда будет подключена
  строгая аналитика, определение можно заменить на настоящее выражение
  через логарифмы.
-/
@[reducible] def Hbin (ε : Rat) : Rat := ε

/--
  Суммарная верхняя оценка на число подмножеств словаря размера `D`,
  состоящих не более чем из `k` элементов.  Мы работаем с грубой, но
  полностью формальной границей: суммарная биномиальная сумма не превосходит
  полного числа подмножеств `2^D`.  Более точные оценки (например,
  `(k+1) * (eD/k)^k`) можно будет добавить позже, но уже эта версия
  позволяет заменить прежнюю аксиому на честное доказательство.
-/
lemma sum_choose_le_pow (D k : Nat) :
    (∑ i ∈ Finset.range (k.succ), Nat.choose D i) ≤ 2 ^ D :=
  by
    classical
    by_cases h : k ≤ D
    · -- В случае `k ≤ D` ограничиваем сумму более длинной суммой `0 ≤ i ≤ D`.
      have hsubset : Finset.range (k.succ) ⊆ Finset.range (D.succ) := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact Finset.mem_range.mpr <| lt_of_lt_of_le hi' (Nat.succ_le_succ h)
      have hmono :
          (∑ i ∈ Finset.range (k.succ), Nat.choose D i)
              ≤ (∑ i ∈ Finset.range (D.succ), Nat.choose D i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro i _hi _; exact Nat.zero_le _)
      have hsum_eq : (∑ i ∈ Finset.range (D.succ), Nat.choose D i) = 2 ^ D :=
        Nat.sum_range_choose (n := D)
      exact hmono.trans hsum_eq.le
    · -- Если `k > D`, то хвост суммы обнуляется, и мы получаем точное равенство.
      push_neg at h
      have hx :
          ∀ i ∈ Finset.Ico (D.succ) (k.succ), Nat.choose D i = 0 :=
        by
          intro i hi
          rcases Finset.mem_Ico.mp hi with ⟨hi₁, _⟩
          have hx : D < i := lt_of_lt_of_le (Nat.lt_succ_self _) hi₁
          simp [Nat.choose_eq_zero_of_lt hx]
      have htail :
          (∑ i ∈ Finset.Ico (D.succ) (k.succ), Nat.choose D i) = 0 :=
        Finset.sum_eq_zero hx
      have hsplit :=
        Finset.sum_range_add_sum_Ico (f := fun i ↦ Nat.choose D i)
          (m := D.succ) (n := k.succ) (Nat.succ_le_succ h.le)
      have heq : (∑ i ∈ Finset.range (k.succ), Nat.choose D i)
          = (∑ i ∈ Finset.range (D.succ), Nat.choose D i) := by
        calc
          (∑ i ∈ Finset.range (k.succ), Nat.choose D i)
              = (∑ i ∈ Finset.range (D.succ), Nat.choose D i)
                  + (∑ i ∈ Finset.Ico (D.succ) (k.succ), Nat.choose D i) :=
                by
                  simp [hsplit]
          _ = (∑ i ∈ Finset.range (D.succ), Nat.choose D i) + 0 := by
                rw [htail]
          _ = (∑ i ∈ Finset.range (D.succ), Nat.choose D i) := by
                simp
      have hsum_eq : (∑ i ∈ Finset.range (D.succ), Nat.choose D i) = 2 ^ D :=
        Nat.sum_range_choose (n := D)
      have hsum_le : (∑ i ∈ Finset.range (k.succ), Nat.choose D i) ≤ 2 ^ D := by
        have htarget : (∑ i ∈ Finset.range (D.succ), Nat.choose D i) ≤ 2 ^ D :=
          hsum_eq.le
        exact heq ▸ htarget
      exact hsum_le

/--
  Более точная оценка для биномиальной суммы.  Мы отделяем зависимость от
  конкретного размера словаря, оценивая его через `max 1 D`, что автоматически
  обеспечивает положительность базы степени.  Такая форма удобна для дальнейших
  аналитических преобразований, поскольку она не приводит к нулевым степеням
  при `D = 0`.
-/
lemma choose_le_pow_max (D i : Nat) :
    Nat.choose D i ≤ (Nat.max 1 D) ^ i :=
  by
    have hmono : D ≤ Nat.max 1 D := by
      exact le_max_of_le_right (le_rfl)
    exact (Nat.choose_le_pow D i).trans (Nat.pow_le_pow_left hmono i)

/--
  Удобное обозначение для счётной части словаря: мы просто рассматриваем
  суммарное количество объединений не более чем `k` подкубов из набора длины
  `D`.  Эта величина играет роль верхней оценки для «словаря» в сценариях SAL.
-/
noncomputable def unionBound (D k : Nat) : Nat :=
  ∑ i ∈ Finset.range (k.succ), Nat.choose D i

/-- Свойство, сопровождающее `unionBound`: извлечённая сумма ограничена числом `2^D`. -/
theorem unionBound_le_pow (D k : Nat) : unionBound D k ≤ 2 ^ D :=
  sum_choose_le_pow D k

/--
  Если перебрать все подмножества размером ≤ `k`, то их количество ограничено
  грубой, но полностью конструктивной границей `(k+1) * (max 1 D)^k`.  Эта оценка
  усиливает предыдущую тривиальную границу `2^D` и важна при поиске реальных
  контрпримеров: мы можем быстро проверять, что словарь недостаточно велик,
  используя лишь арифметику по натуральным числам.
-/
lemma unionBound_le_pow_mul (D k : Nat) :
    unionBound D k ≤ (k.succ) * (Nat.max 1 D) ^ k :=
  by
    classical
    -- Удобное обозначение для положительной базы степени.
    set M := Nat.max 1 D with hMdef
    have hM_pos : 0 < M := by
      -- Из `1 ≤ M` следует положительность.
      have hM_ge_aux : 1 ≤ Nat.max 1 D := le_max_left (1 : Nat) D
      have hM_ge : 1 ≤ M := hMdef.symm ▸ hM_ge_aux
      have : 0 < (1 : Nat) := by decide
      exact lt_of_lt_of_le this hM_ge
    -- Каждая отдельная биномиальная компонента ограничена сверху `M^k`.
    have hterm :
        ∀ i ∈ Finset.range (k.succ), Nat.choose D i ≤ M ^ k :=
      by
        intro i hi
        -- Из принадлежности диапазону получаем `i ≤ k`.
        have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        -- Сначала применяем оценку `choose ≤ M^i`.
        have hchoose_aux := choose_le_pow_max D i
        have hpow : (Nat.max 1 D) ^ i = M ^ i := by
          simp [hMdef]
        have hchoose : Nat.choose D i ≤ M ^ i := hpow ▸ hchoose_aux
        -- Затем используем монотонность степени по показателю.
        have hmono := Nat.pow_le_pow_right hM_pos hi_le
        exact hchoose.trans hmono
    -- Складываем ограничения по всем `i`.
    have hsum :=
      Finset.sum_le_sum fun i hi => hterm i hi
    -- Сумма констант `M^k` равна `(k+1) * M^k`.
    have hsum_const :
        ∑ _i ∈ Finset.range (k.succ), M ^ k = k.succ * M ^ k :=
      by
        classical
        have hconst :
            ∀ x ∈ Finset.range (k.succ), (fun _ : Nat => M ^ k) x = M ^ k := by
          intro _ _; simp
        have := Finset.sum_const_nat
          (s := Finset.range (k.succ)) (m := M ^ k)
          (f := fun _ : Nat => M ^ k) hconst
        convert this using 1
        simp [Finset.card_range]
    -- Финальный вывод — переписать исходные обозначения.
    have hsum' :
        (∑ i ∈ Finset.range (k.succ), Nat.choose D i)
          ≤ k.succ * M ^ k :=
      by
        calc
          (∑ i ∈ Finset.range (k.succ), Nat.choose D i)
              ≤ (∑ _i ∈ Finset.range (k.succ), M ^ k) := hsum
          _ = k.succ * M ^ k := hsum_const
    have hfinal : unionBound D k ≤ k.succ * M ^ k := by
      change (∑ i ∈ Finset.range (k.succ), Nat.choose D i) ≤ k.succ * M ^ k
      exact hsum'
    have hpow : M ^ k = (Nat.max 1 D) ^ k := by
      simp [hMdef]
    exact hpow ▸ hfinal

/-!
### Монотонность биномиальных коэффициентов по верхнему аргументу

Следующий блок фиксирует простые, но часто полезные наблюдения: при возрастании
верхнего аргумента `n` биномиальные коэффициенты `Nat.choose n k` растут.
Эти факты потребуются в switching-лемме глубины 1, когда мы будем заменять
индивидуальные ширины клауз грубой глобальной шириной `w` и контролировать
оставшиеся суммы без оглядки на конкретную формулу.
-/

lemma choose_le_succ (n k : Nat) :
    Nat.choose n k ≤ Nat.choose n.succ k := by
  classical
  cases hk : k with
  | zero =>
      simp [hk]
  | succ k' =>
      have hrec := Nat.choose_succ_succ n k'
      -- Для `k = k' + 1` применяем стандартную рекуррентную формулу и
      -- сравниваем с суммой `a + b ≥ b`.
      have hle :
          Nat.choose n (Nat.succ k')
            ≤ Nat.choose n k' + Nat.choose n (Nat.succ k') := by
        exact Nat.le_add_left _ _
      simpa [hk, hrec, Nat.succ_eq_add_one, add_comm, add_left_comm,
        add_assoc] using hle

/--
  Монотонность биномиального коэффициента по верхнему аргументу.  Для фиксированного
  `k` величина `Nat.choose n k` не убывает при увеличении `n`.  Доказательство —
  прямая индукция по доказательству `m ≤ n`, где на каждом шаге применяется
  лемма `choose_le_succ`.
-/
lemma choose_le_of_le {k m n : Nat} (hmn : m ≤ n) :
    Nat.choose m k ≤ Nat.choose n k := by
  classical
  induction hmn with
  | refl => simpa
  | @step n hmn ih =>
      exact ih.trans (choose_le_succ n k)

/--
  Комбинаторное равенство, связывающее биномиальные коэффициенты с «сдвигом»
  на `k` элементов.  Оно происходит из стандартной формулы
  `choose_mul` и удобно тем, что позволяет переписать
  `Nat.choose n (ℓ - k)` через произведение
  `Nat.choose n ℓ * Nat.choose ℓ k` с точным учётом остаточного множителя.
  В дальнейшем это равенство поможет контролировать вероятность того, что
  точное ограничение оставляет фиксированное подмножество литералов живым. -/
lemma choose_mul_sub (n ℓ k : Nat) (hk : k ≤ ℓ) (hℓn : ℓ ≤ n) :
    Nat.choose n ℓ * Nat.choose ℓ (ℓ - k)
      = Nat.choose n (ℓ - k) * Nat.choose (n - (ℓ - k)) k := by
  classical
  -- Применяем стандартную формулу `choose_mul` к параметрам `(n, ℓ, ℓ - k)`.
  have hsubset : ℓ - k ≤ ℓ := Nat.sub_le _ _
  simpa [Nat.sub_sub_self hk] using
    (Nat.choose_mul (n := n) (k := ℓ) (s := ℓ - k) hℓn hsubset)

/--
  Непосредственное следствие `choose_mul_sub`: после учёта положительного
  множителя `(n - ℓ + k).choose k` мы получаем верхнюю границу на
  `choose n (ℓ - k)` через произведение `choose n ℓ * choose ℓ k`.
  Эта форма пригодится при вероятностных оценках: мы грубо ограничиваем
  количество рестрикций, в которых фиксированное подмножество `k` литералов
  остаётся свободным. -/
lemma choose_sub_le_mul (n ℓ k : Nat) (hk : k ≤ ℓ) (hℓn : ℓ ≤ n) :
    Nat.choose n (ℓ - k) ≤ Nat.choose n ℓ * Nat.choose ℓ (ℓ - k) := by
  classical
  -- Начинаем с точной формулы `choose_mul_sub`.
  have hmul := choose_mul_sub (n := n) (ℓ := ℓ) (k := k) hk hℓn
  -- Показываем, что множитель слева не меньше единицы.
  have hdenom_pos : 1 ≤ Nat.choose (n - (ℓ - k)) k := by
    -- Из `ℓ ≤ n` следует `ℓ - k ≤ n`, значит биномиальный коэффициент положителен.
    have hle' : ℓ - k ≤ n := by
      exact le_trans (Nat.sub_le _ _) hℓn
    have hk_le : k ≤ n - (ℓ - k) := by
      -- Рассматриваем суммы `k + (ℓ - k)` и `n - (ℓ - k) + (ℓ - k)`.
      have hleft : k + (ℓ - k) = ℓ := by
        simpa [Nat.add_comm] using (Nat.sub_add_cancel hk)
      have hright : (n - (ℓ - k)) + (ℓ - k) = n :=
        Nat.sub_add_cancel hle'
      have hineq : k + (ℓ - k) ≤ (n - (ℓ - k)) + (ℓ - k) := by
        simpa [hleft, hright] using hℓn
      exact Nat.le_of_add_le_add_right hineq
    have hpos : 0 < Nat.choose (n - (ℓ - k)) k :=
      Nat.choose_pos hk_le
    exact Nat.succ_le_of_lt hpos
  -- Умножаем меньший множитель на фактор ≥ 1 и подставляем равенство.
  have hle :
      Nat.choose n (ℓ - k)
        ≤ Nat.choose n (ℓ - k) * Nat.choose (n - (ℓ - k)) k := by
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_left (Nat.choose n (ℓ - k)) hdenom_pos)
  -- Итоговое неравенство получаем из равенства `hmul`.
  simpa [hmul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hle

/--
  Простая монотонность: произведение `ℓ - k` на остаток `n - ℓ + 1`
  не превосходит произведения `ℓ` на расширенный остаток `n - ℓ + k + 1`.
  Обе оценки непосредственно следуют из монотонности по каждому аргументу.
-/
lemma sub_mul_le_mul_add (n ℓ k : Nat) :
    (ℓ - k) * (n - ℓ + 1) ≤ ℓ * (n - ℓ + k + 1) := by
  have hleft : ℓ - k ≤ ℓ := Nat.sub_le _ _
  have hright : n - ℓ + 1 ≤ n - ℓ + k + 1 := by
    have : n - ℓ + 1 ≤ n - ℓ + 1 + k := Nat.le_add_right _ _
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  exact Nat.mul_le_mul hleft hright

/--
  Версия рекуррентного соотношения для «сдвига» вниз на один шаг: если мы
  уменьшаем число свободных литералов с `ℓ - k` до `ℓ - (k+1)`, то отношение
  биномиальных коэффициентов выражается через фактор `(ℓ - k)/(n - ℓ + k + 1)`.
-/
lemma choose_sub_succ_mul
    (n ℓ k : Nat) (hk : k < ℓ) (hℓn : ℓ ≤ n) :
    (ℓ - k) * Nat.choose n (ℓ - k)
      = (n - ℓ + k + 1) * Nat.choose n (ℓ - Nat.succ k) := by
  classical
  have hk_succ_le : Nat.succ k ≤ ℓ := Nat.succ_le_of_lt hk
  have hleft : ℓ - Nat.succ k + 1 = ℓ - k := by
    calc
      ℓ - Nat.succ k + 1
          = Nat.succ (ℓ - Nat.succ k) := rfl
      _ = Nat.succ ℓ - Nat.succ k := (Nat.succ_sub hk_succ_le).symm
      _ = ℓ - k := by simpa [Nat.succ_eq_add_one]
            using (Nat.succ_sub_succ ℓ k)
  have hright : n - (ℓ - Nat.succ k) = n - ℓ + k + 1 := by
    calc
      n - (ℓ - Nat.succ k)
          = ((n - ℓ) + ℓ) - (ℓ - Nat.succ k) := by
              simpa [Nat.sub_add_cancel hℓn, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc]
      _ = (n - ℓ) + (ℓ - (ℓ - Nat.succ k)) :=
              Nat.add_sub_assoc (Nat.sub_le _ _) (n - ℓ)
      _ = (n - ℓ) + Nat.succ k := by
              simpa using (Nat.sub_sub_self hk_succ_le)
      _ = n - ℓ + k + 1 := by
              simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
                Nat.succ_eq_add_one]
  have h := Nat.choose_succ_right_eq (n := n) (k := ℓ - Nat.succ k)
  simpa [hleft, hright, Nat.succ_eq_add_one, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]
    using h

/--
  «p-biased» оценка отношения биномиальных коэффициентов: при фиксированных
  `n` и `ℓ ≤ n` каждая ступень `k` не превосходит степени
  `(ℓ / (n - ℓ + 1))^k`.  Доказательство — индукция по `k`, используя
  классическую рекуррентную формулу `choose_succ_right_eq` и факт
  `sub_mul_le_mul_add` для контроля одной ступени.
-/
lemma choose_sub_ratio_le_pow
    (n ℓ k : Nat) (hk : k ≤ ℓ) (hℓn : ℓ ≤ n) :
    (Nat.choose n (ℓ - k) : ℝ≥0∞)
      ≤ (Nat.choose n ℓ : ℝ≥0∞)
          * ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) ^ k := by
  classical
  revert ℓ
  induction' k with k ih
  · intro ℓ hk hℓn
    simpa [Nat.sub_zero, pow_zero]
  · intro ℓ hk hℓn
    have hk_lt : k < ℓ := Nat.succ_le.mp hk
    have hk_le : k ≤ ℓ := Nat.le_of_lt hk_lt
    set ρ := ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) with hρ
    have ρ_nonneg : 0 ≤ ρ := by simpa [hρ] using (bot_le : (0 : ℝ≥0∞) ≤ ρ)
    have hchoose_nonneg : 0 ≤ (Nat.choose n (ℓ - k) : ℝ≥0∞) := by
      simpa using (bot_le : (0 : ℝ≥0∞) ≤ (Nat.choose n (ℓ - k) : ℝ≥0∞))
    have hy_pos : (0 : ℝ≥0∞) < (n - ℓ + k + 1 : ℝ≥0∞) := by
      exact_mod_cast (Nat.succ_pos (n - ℓ + k))
    have hx_pos : (0 : ℝ≥0∞) < (n - ℓ + 1 : ℝ≥0∞) := by
      exact_mod_cast (Nat.succ_pos (n - ℓ))
    have hy_ne : (n - ℓ + k + 1 : ℝ≥0∞) ≠ 0 := hy_pos.ne'
    have hy_ne_top : (n - ℓ + k + 1 : ℝ≥0∞) ≠ ∞ := by
      simpa using (show (↑(n - ℓ + k + 1) : ℝ≥0∞) ≠ ∞ from by simp)
    have hx_ne : (n - ℓ + 1 : ℝ≥0∞) ≠ 0 := hx_pos.ne'
    have hx_ne_top : (n - ℓ + 1 : ℝ≥0∞) ≠ ∞ := by
      simpa using (show (↑(n - ℓ + 1) : ℝ≥0∞) ≠ ∞ from by simp)
    have hnat := sub_mul_le_mul_add (n := n) (ℓ := ℓ) (k := k)
    have hnat_cast :
        ((ℓ - k : ℝ≥0∞) * (n - ℓ + 1 : ℝ≥0∞))
          ≤ (ℓ : ℝ≥0∞) * (n - ℓ + k + 1 : ℝ≥0∞) := by
      exact_mod_cast hnat
    have htemp_div :
        ((ℓ - k : ℝ≥0∞) * (n - ℓ + 1 : ℝ≥0∞))
          / (n - ℓ + k + 1 : ℝ≥0∞)
          ≤ (ℓ : ℝ≥0∞) := by
      exact
        (ENNReal.div_le_iff (h1 := hy_ne) (h2 := hy_ne_top)).2 hnat_cast
    have hratio :
        ((ℓ - k : ℝ≥0∞) / (n - ℓ + k + 1 : ℝ≥0∞))
          ≤ ρ := by
      refine
        (ENNReal.le_div_iff_mul_le (h0 := Or.inl hx_ne)
            (ht := Or.inl hx_ne_top)).2 ?_
      simpa [hρ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using htemp_div
    have hk_eq :
        (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞)
          = (Nat.choose n (ℓ - k) : ℝ≥0∞)
              * ((ℓ - k : ℝ≥0∞)
                  / (n - ℓ + k + 1 : ℝ≥0∞)) := by
      have hmul_nat :=
        choose_sub_succ_mul (n := n) (ℓ := ℓ) (k := k) hk_lt hℓn
      have hcast :
          ((ℓ - k : ℝ≥0∞) * (Nat.choose n (ℓ - k) : ℝ≥0∞))
            = (n - ℓ + k + 1 : ℝ≥0∞)
                * (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞) := by
        simpa [mul_comm, mul_left_comm, mul_assoc]
          using (by exact_mod_cast hmul_nat : _)
      have hy_ne : (n - ℓ + k + 1 : ℝ≥0∞) ≠ 0 := hy_pos.ne'
      have hy_cancel :
          (n - ℓ + k + 1 : ℝ≥0∞)
              * (n - ℓ + k + 1 : ℝ≥0∞)⁻¹
            = 1 := ENNReal.mul_inv_cancel hy_ne hy_ne_top
      calc
        (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞)
            = (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞) * 1 := by
                simpa
        _ = (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞)
                * ((n - ℓ + k + 1 : ℝ≥0∞)
                    * (n - ℓ + k + 1 : ℝ≥0∞)⁻¹) := by
                simpa [hy_cancel, mul_comm, mul_left_comm, mul_assoc]
                    using
                      (congrArg
                          (fun x =>
                            (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞) * x)
                          hy_cancel.symm)
        _ = ((n - ℓ + k + 1 : ℝ≥0∞)
                * (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞))
                * (n - ℓ + k + 1 : ℝ≥0∞)⁻¹ := by
                    simp [mul_comm, mul_left_comm, mul_assoc]
        _ = ((ℓ - k : ℝ≥0∞)
                * (Nat.choose n (ℓ - k) : ℝ≥0∞))
                * (n - ℓ + k + 1 : ℝ≥0∞)⁻¹ := by
                    simpa [hcast, mul_comm, mul_left_comm, mul_assoc]
        _ = (Nat.choose n (ℓ - k) : ℝ≥0∞)
                * ((ℓ - k : ℝ≥0∞)
                    / (n - ℓ + k + 1 : ℝ≥0∞)) := by
                    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hk_bound :
        (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞)
          ≤ (Nat.choose n (ℓ - k) : ℝ≥0∞) * ρ := by
      have hmul := mul_le_mul_of_nonneg_left hratio hchoose_nonneg
      simpa [hk_eq, mul_comm, mul_left_comm, mul_assoc]
        using hmul
    have hIH := ih ℓ hk_le hℓn
    have hIH_mul := mul_le_mul_of_nonneg_right hIH ρ_nonneg
    have hpow_succ :
        (Nat.choose n ℓ : ℝ≥0∞) * ρ ^ k * ρ
          = (Nat.choose n ℓ : ℝ≥0∞) * ρ ^ Nat.succ k := by
      simp [hρ, pow_succ, mul_comm, mul_left_comm, mul_assoc]
    have hfinal :
        (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞)
          ≤ (Nat.choose n ℓ : ℝ≥0∞) * ρ ^ Nat.succ k := by
      calc
        (Nat.choose n (ℓ - Nat.succ k) : ℝ≥0∞)
            ≤ (Nat.choose n (ℓ - k) : ℝ≥0∞) * ρ := hk_bound
        _ ≤ (Nat.choose n ℓ : ℝ≥0∞) * ρ ^ k * ρ := hIH_mul
        _ = (Nat.choose n ℓ : ℝ≥0∞) * ρ ^ Nat.succ k := hpow_succ
    simpa [hρ] using hfinal


/--
  Простая оценка «сдвига» биномиального коэффициента по верхнему индексу.
  Для фиксированных `w` и `t ≤ w` увеличение верхнего аргумента на `j` не
  превосходит произведения `choose w t` и биномиального коэффициента от
  остатка `w - t`.  Это классическое равенство Vandermonde`а, переписанное в
  виде неравенства за счёт множителя `choose (t + j) t ≥ 1`.
-/
lemma choose_add_le_mul
    (w t j : Nat) (htw : t ≤ w) (hj : j ≤ w - t) :
    Nat.choose w (t + j) ≤ Nat.choose w t * Nat.choose (w - t) j := by
  classical
  -- Обрабатываем частный случай `j = 0` отдельно.
  by_cases hjzero : j = 0
  · subst hjzero
    simpa using (Nat.mul_one (Nat.choose w t)).le
  -- Общий случай опирается на формулу Vandermonde`а.
  have ht_le : t ≤ t + j := Nat.le_add_right _ _
  have htj_le : t + j ≤ w := by
    have := Nat.add_le_add_left hj t
    have hrewrite : t + (w - t) = w := Nat.add_sub_of_le htw
    simpa [hrewrite] using this
  have hmul :=
    Nat.choose_mul (n := w) (k := t + j) (s := t)
      (by exact htj_le) (by exact ht_le)
  have hrewrite :
      Nat.choose w (t + j) * Nat.choose (t + j) t
        = Nat.choose w t * Nat.choose (w - t) j := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_sub_cancel]
      using hmul
  have hpos : 0 < Nat.choose (t + j) t := by
    simpa using Nat.choose_pos ht_le
  have hone : 1 ≤ Nat.choose (t + j) t := Nat.succ_le_of_lt hpos
  have hle :
      Nat.choose w (t + j)
        ≤ Nat.choose w (t + j) * Nat.choose (t + j) t := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.choose w (t + j)) hone
  simpa [hrewrite, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle

/--
  Перестановка суммирования по отрезку `t ≤ k ≤ t + d` к диапазону
  `0 ≤ j ≤ d` после замены переменной `j = k - t`.  Используется для
  применения биномиальной теоремы к сдвинутым суммам. -/
lemma sum_Icc_choose_shift_eq (t d : Nat) (θ : ℝ≥0∞) :
    (∑ k ∈ Finset.Icc t (t + d),
        (Nat.choose d (k - t) : ℝ≥0∞) * θ ^ (k - t))
      = (∑ j ∈ Finset.range d.succ,
          (Nat.choose d j : ℝ≥0∞) * θ ^ j) := by
  classical
  refine Finset.sum_bij
      (fun k hk => k - t)
      (fun k hk => ?_)
      (fun k₁ hk₁ k₂ hk₂ h => by
        have hk₁' : t ≤ k₁ := (Finset.mem_Icc.mp hk₁).1
        have hk₂' : t ≤ k₂ := (Finset.mem_Icc.mp hk₂).1
        have := congrArg (fun x => t + x) h
        simpa [Nat.add_sub_of_le hk₁', Nat.add_sub_of_le hk₂'] using this)
      (fun j hj => ?_)
      (fun k hk => ?_)
  · -- Каждое `k ∈ Icc t (t + d)` переходит в диапазон `0..d`.
    have hk_lower : t ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_upper : k ≤ t + d := (Finset.mem_Icc.mp hk).2
    have hle : k - t ≤ d := by
      exact (Nat.sub_le_iff_le_add).2 (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hk_upper)
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
  · -- Сюръективность: для любого `j` берём `k = t + j`.
    have hj_lt : j < d.succ := Finset.mem_range.mp hj
    have hj_le : j ≤ d := Nat.lt_succ_iff.mp hj_lt
    refine ⟨t + j, ?_, ?_⟩
    · have hupper : t + j ≤ t + d := Nat.add_le_add_left hj_le _
      exact Finset.mem_Icc.mpr ⟨Nat.le_add_right _ _, hupper⟩
    · have hrewrite : t + j - t = j := by simpa using Nat.add_sub_cancel t j
      simpa [hrewrite]
  · -- Совпадение слагаемых после подстановки `j = k - t`.
    rfl

/--
  Специализация биномиальной теоремы `add_pow` для случая `1 + θ`.  Нам часто
  требуется именно такая форма, поэтому выделяем её в отдельную лемму, чтобы
  не повторять одно и то же переписывание в разных местах.
-/
lemma sum_range_choose_mul_pow_eq (d : Nat) (θ : ℝ≥0∞) :
    (∑ j ∈ Finset.range d.succ,
        (Nat.choose d j : ℝ≥0∞) * θ ^ j)
      = (1 + θ) ^ d := by
  classical
  have hpow := (add_pow θ (1 : ℝ≥0∞) d).symm
  simpa [one_pow, add_comm, mul_comm, mul_left_comm, mul_assoc] using hpow


/--
  Перенумеровка суммирования по `Fin (k+1)` и по диапазону `0..k`.
  Этот вспомогательный результат удобно применять для переиндексации
  биномиальных сумм и других комбинаторных выражений.
-/
lemma sum_fin_eq_sum_range {β : Type*} [AddCommMonoid β]
    (f : ℕ → β) (k : ℕ) :
    (∑ i : Fin (k.succ), f i) =
      ∑ i ∈ Finset.range (k.succ), f i :=
  by
    classical
    refine
      Finset.sum_bij (fun (i : Fin (k.succ)) (_ : i ∈ (Finset.univ : Finset _)) => (i : ℕ))
        (fun i _ => Finset.mem_range.mpr i.isLt)
        (fun i _ j _ h => by
          ext; exact h)
        ?_ (fun i _ => rfl)
    intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, ?_, rfl⟩
    simp

/--
  Вспомогательный подсчёт: точное количество подмножеств мощности `i`
  конечного множества `α` равно биномиальному коэффициенту.
-/
lemma card_subsets_exact_choose (α : Type*) [Fintype α] [DecidableEq α]
    (i : Nat) :
    Fintype.card {S : Finset α // S.card = i}
      = Nat.choose (Fintype.card α) i :=
  by
    classical
    have hcard :
        Fintype.card {S : Finset α // S.card = i} =
          (Finset.univ.filter fun (S : Finset α) => S.card = i).card :=
      Fintype.card_subtype (fun (S : Finset α) => S.card = i)
    have hfilter_eq :
        (Finset.univ.filter fun (S : Finset α) => S.card = i)
          = (Finset.univ : Finset α).powersetCard i := by
      apply Finset.ext
      intro S; constructor <;> intro hS
      · rcases Finset.mem_filter.1 hS with ⟨-, hcardS⟩
        have hsubset : S ⊆ (Finset.univ : Finset α) := by
          intro x _hx; simp
        exact Finset.mem_powersetCard.2 ⟨hsubset, hcardS⟩
      · have hcardS : S.card = i :=
          (Finset.mem_powersetCard.1 hS).2
        refine Finset.mem_filter.2 ?_
        refine ⟨by simp, hcardS⟩
    have hpow := Finset.card_powersetCard i (Finset.univ : Finset α)
    have hpow' :
        ((Finset.univ : Finset α).powersetCard i).card =
          Nat.choose (Fintype.card α) i :=
      by
        have :
            Nat.choose (Finset.card (Finset.univ : Finset α)) i =
              Nat.choose (Fintype.card α) i :=
          by
            simp [Finset.card_univ]
        exact Eq.trans hpow this
    calc
      Fintype.card {S : Finset α // S.card = i}
          = (Finset.univ.filter fun (S : Finset α) => S.card = i).card :=
            hcard
      _ = ((Finset.univ : Finset α).powersetCard i).card :=
            congrArg Finset.card hfilter_eq
      _ = Nat.choose (Fintype.card α) i := hpow'

/--
  Разделяем семейство всех подмножеств мощности ≤ `k` по точной мощности
  и суммируем полученные биномиальные числа.
-/
lemma card_subsets_le_unionBound (α : Type*) [Fintype α] [DecidableEq α]
    (k : Nat) :
    Fintype.card {S : Finset α // S.card ≤ k}
      = unionBound (Fintype.card α) k :=
  by
    classical
    let toSigma : {S : Finset α // S.card ≤ k} →
        Σ i : Fin (k.succ), {S : Finset α // S.card = (i : Nat)} :=
      fun S => ⟨⟨S.1.card, Nat.lt_succ_of_le S.2⟩, ⟨S.1, rfl⟩⟩
    let fromSigma : (Σ i : Fin (k.succ), {S : Finset α // S.card = (i : Nat)}) →
        {S : Finset α // S.card ≤ k} :=
      fun x =>
        ⟨x.2.1, by
          have hx : (x.1 : Nat) ≤ k := Nat.lt_succ_iff.mp x.1.isLt
          exact x.2.2.symm ▸ hx⟩
    have hleft : Function.LeftInverse fromSigma toSigma := by
      intro S
      rcases S with ⟨S, hS⟩
      rfl
    have hright : Function.RightInverse fromSigma toSigma := by
      intro x
      rcases x with ⟨i, ⟨S, hS⟩⟩
      ext <;> simp [toSigma, fromSigma, hS]
    let e : {S : Finset α // S.card ≤ k} ≃
        Σ i : Fin (k.succ), {S : Finset α // S.card = (i : Nat)} :=
      ⟨toSigma, fromSigma, hleft, hright⟩
    have hcard_equiv := Fintype.card_congr e
    have hsigma :
        Fintype.card (Σ i : Fin (k.succ), {S : Finset α // S.card = (i : Nat)}) =
          ∑ i : Fin (k.succ), Fintype.card {S : Finset α // S.card = (i : Nat)} :=
      by
        classical
        exact
          Fintype.card_sigma
            (α := fun i : Fin (k.succ) => {S : Finset α // S.card = (i : Nat)})
    have hsum_range :
        (∑ i : Fin (k.succ),
            Fintype.card {S : Finset α // S.card = (i : Nat)})
          = ∑ i ∈ Finset.range (k.succ),
              Fintype.card {S : Finset α // S.card = i} :=
      sum_fin_eq_sum_range
        (fun i => Fintype.card {S : Finset α // S.card = i}) k
    have hchoose :
        ∑ i ∈ Finset.range (k.succ),
            Fintype.card {S : Finset α // S.card = i}
          = unionBound (Fintype.card α) k :=
      by
        unfold unionBound
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact card_subsets_exact_choose (α := α) i
    refine
      (calc
        Fintype.card {S : Finset α // S.card ≤ k}
            = Fintype.card (Σ i : Fin (k.succ),
                {S : Finset α // S.card = (i : Nat)}) := hcard_equiv
        _ = ∑ i : Fin (k.succ),
              Fintype.card {S : Finset α // S.card = (i : Nat)} := hsigma
        _ = ∑ i ∈ Finset.range (k.succ),
              Fintype.card {S : Finset α // S.card = i} := hsum_range
        _ = unionBound (Fintype.card α) k := hchoose)

/--
  Добавление одного элемента в словарь не уменьшает число допустимых
  объединений.  Формулируем это как монотонность `unionBound` по первой
  переменной при переходе от `D` к `D.succ`.
-/
lemma unionBound_le_succ (D k : Nat) :
    unionBound D k ≤ unionBound D.succ k :=
  by
    classical
    -- Переписываем обе стороны через точное количество подмножеств множества `Fin D`.
    have hcardD :
        unionBound D k =
          Fintype.card {S : Finset (Fin D) // S.card ≤ k} :=
      by
        have h := card_subsets_le_unionBound (α := Fin D) (k := k)
        calc
          unionBound D k
              = unionBound (Fintype.card (Fin D)) k := by
                  have hcardFin : Fintype.card (Fin D) = D := Fintype.card_fin _
                  exact (congrArg (fun n => unionBound n k) hcardFin).symm
          _ = Fintype.card {S : Finset (Fin D) // S.card ≤ k} := h.symm
    have hcardSucc :
        unionBound D.succ k =
          Fintype.card {S : Finset (Fin D.succ) // S.card ≤ k} :=
      by
        have h := card_subsets_le_unionBound (α := Fin D.succ) (k := k)
        calc
          unionBound D.succ k
              = unionBound (Fintype.card (Fin D.succ)) k := by
                  have hcardFin : Fintype.card (Fin D.succ) = D.succ :=
                    Fintype.card_fin _
                  exact (congrArg (fun n => unionBound n k) hcardFin).symm
          _ = Fintype.card {S : Finset (Fin D.succ) // S.card ≤ k} := h.symm
    -- Инъективно расширяем каждое множество `S ⊆ Fin D` до `Fin (D.succ)` через `Fin.castSucc`.
    let lift (S : {S : Finset (Fin D) // S.card ≤ k}) :
        {T : Finset (Fin D.succ) // T.card ≤ k} :=
      ⟨Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S.1,
        by
          -- `Finset.map` по вложению сохраняет кардинальность.
          have hmap_card :
              (Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S.1).card =
                S.1.card :=
            Finset.card_map
              (f := ⟨Fin.castSucc, Fin.castSucc_injective _⟩) (s := S.1)
          exact hmap_card.symm ▸ S.2⟩
    -- Отображение `lift` является инъекцией.
    have h_inj : Function.Injective lift := by
      intro S₁ S₂ hS
      -- Сравниваем образы подмножеств и переходим к базовым элементам.
      have hsets :
          Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₁.1 =
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₂.1 :=
        congrArg Subtype.val hS
      -- Проверяем, что каждое `x` принадлежит `S₁` тогда и только тогда, когда принадлежит `S₂`.
      ext x; constructor <;> intro hx
      · -- Используем соответствие через `Fin.castSucc` и равенство образов.
        have hx' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₁.1 :=
          Finset.mem_map.mpr ⟨x, hx, rfl⟩
        have hx'' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₂.1 :=
          hsets ▸ hx'
        rcases Finset.mem_map.1 hx'' with ⟨y, hy, hyx⟩
        have : y = x := Fin.castSucc_injective _ hyx
        exact this ▸ hy
      · -- Аналогично, но меняем роли `S₁` и `S₂`.
        have hx' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₂.1 :=
          Finset.mem_map.mpr ⟨x, hx, rfl⟩
        have hx'' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₁.1 :=
          hsets.symm ▸ hx'
        rcases Finset.mem_map.1 hx'' with ⟨y, hy, hyx⟩
        have : y = x := Fin.castSucc_injective _ hyx
        exact this ▸ hy
    -- Сравниваем мощности подмножеств при помощи полученной инъекции.
    have hcard_le :=
      Fintype.card_le_of_injective lift h_inj
    -- Возвращаемся к выражению через `unionBound`.
    have hconverted : unionBound D k ≤ unionBound D.succ k :=
      by
        calc
          unionBound D k
              = Fintype.card {S : Finset (Fin D) // S.card ≤ k} := hcardD
          _ ≤ Fintype.card {S : Finset (Fin D.succ) // S.card ≤ k} := hcard_le
          _ = unionBound D.succ k := hcardSucc.symm
    exact hconverted

/--
  Монотонность `unionBound` по размеру словаря: если `D₁ ≤ D₂`, то и
  `unionBound D₁ k ≤ unionBound D₂ k`.
-/
lemma unionBound_mono_left {D₁ D₂ k : Nat}
    (h : D₁ ≤ D₂) :
    unionBound D₁ k ≤ unionBound D₂ k :=
  by
    classical
    have haux : ∀ d, unionBound D₁ k ≤ unionBound (D₁ + d) k := by
      intro d
      induction d with
      | zero =>
          -- База: добавление нуля элементов не меняет оценку.
          have hzero : unionBound D₁ k = unionBound (D₁ + 0) k := by
            simp
          exact hzero.le
        | succ d ih =>
            have hstep := unionBound_le_succ (D₁ + d) k
            have hnext := le_trans ih hstep
            have hrewrite : (D₁ + d).succ = D₁ + Nat.succ d := by
              calc
                (D₁ + d).succ = (D₁ + d) + 1 := Nat.succ_eq_add_one _
                _ = D₁ + (d + 1) := Nat.add_assoc _ _ _
                _ = D₁ + Nat.succ d :=
                  congrArg (fun t => D₁ + t) (Nat.succ_eq_add_one d).symm
            have hgoal : unionBound D₁ k ≤ unionBound (D₁ + Nat.succ d) k :=
              hrewrite ▸ hnext
            exact hgoal
    have hplus : D₁ + (D₂ - D₁) = D₂ := Nat.add_sub_of_le h
    have hresult := haux (D₂ - D₁)
    exact hplus ▸ hresult

/-- Монотонность `unionBound` по бюджету `k`: разрешая больше подкубов,
мы не уменьшаем число возможных объединений. -/
lemma unionBound_mono_right {D k₁ k₂ : Nat}
    (hk : k₁ ≤ k₂) :
    unionBound D k₁ ≤ unionBound D k₂ :=
  by
    classical
    have hsubset : Finset.range (k₁.succ) ⊆ Finset.range (k₂.succ) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le hi' (Nat.succ_le_succ hk))
    have hmono :
        (∑ i ∈ Finset.range (k₁.succ), Nat.choose D i)
          ≤ (∑ i ∈ Finset.range (k₂.succ), Nat.choose D i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro i _ _; exact Nat.zero_le _)
    change (∑ i ∈ Finset.range (k₁.succ), Nat.choose D i)
        ≤ (∑ i ∈ Finset.range (k₂.succ), Nat.choose D i)
    exact hmono

/--
  Натуральный бюджет ошибок `⌈ε ⋅ N⌉`, измеряющий допустимое число
  рассогласований в хамминговом шаре.  Он является целочисленным аналогом
  дробного ограничения `ε`, используемого в анализе SAL.
-/
noncomputable def hammingBallBudget (N : Nat) (ε : Rat) : Nat :=
  Int.toNat (Int.ceil (ε * N))

/--
  Верхняя оценка на число функций в хамминговом шаре радиуса `ε`.  Любую
  функцию внутри шара можно задать набором точек рассогласования, так что
  достаточно пересчитать подмножества мощности ≤ `hammingBallBudget`.
-/
noncomputable def hammingBallBound
  (N : Nat) (ε : Rat) (_h0 : (0 : Rat) ≤ ε) (_h1 : ε ≤ (1 : Rat) / 2) : Nat :=
  unionBound N (hammingBallBudget N ε)

/-- Раскрываем определение `hammingBallBound` для последующих переписок. -/
lemma hammingBallBound_spec
  (N : Nat) (ε : Rat) (_h0 : (0 : Rat) ≤ ε) (_h1 : ε ≤ (1 : Rat) / 2) :
    hammingBallBound N ε _h0 _h1 =
      unionBound N (hammingBallBudget N ε) :=
  rfl

/-- Увеличение допустимой ошибки `ε` не уменьшает натуральный бюджет
рассогласований.  Лемма напрямую следует из монотонности потолка и
положительности множителя `N`. -/
lemma hammingBallBudget_mono
    (N : Nat) {ε ε' : Rat}
    (hε'0 : (0 : Rat) ≤ ε') (hε : ε ≤ ε') :
    hammingBallBudget N ε ≤ hammingBallBudget N ε' :=
  by
    classical
    have hN_nonneg : (0 : Rat) ≤ (N : Rat) := by
      exact_mod_cast (Nat.zero_le N)
    have hmul : ε * (N : Rat) ≤ ε' * (N : Rat) :=
      mul_le_mul_of_nonneg_right hε hN_nonneg
    have hceil_le :
        Int.ceil (ε * (N : Rat)) ≤ Int.ceil (ε' * (N : Rat)) :=
      Int.ceil_le_ceil hmul
    have hmul_nonneg : (0 : Rat) ≤ ε' * (N : Rat) :=
      mul_nonneg hε'0 hN_nonneg
    have hceil_nonneg :
        (0 : ℤ) ≤ Int.ceil (ε' * (N : Rat)) :=
      Int.ceil_nonneg hmul_nonneg
    have htarget :
        Int.ceil (ε * (N : Rat)) ≤
          (Int.toNat (Int.ceil (ε' * (N : Rat))) : ℤ) := by
      have hcast :
          ((Int.toNat (Int.ceil (ε' * (N : Rat)))) : ℤ)
            = Int.ceil (ε' * (N : Rat)) :=
        by
          exact_mod_cast (Int.toNat_of_nonneg hceil_nonneg)
      calc
        Int.ceil (ε * (N : Rat))
            ≤ Int.ceil (ε' * (N : Rat)) := hceil_le
        _ = ((Int.toNat (Int.ceil (ε' * (N : Rat)))) : ℤ) := hcast.symm
    exact (Int.toNat_le.mpr htarget)

/-- Монотонность оценки хаммингового шара по параметру ошибки. -/
lemma hammingBallBound_mono
    (N : Nat) {ε ε' : Rat}
    (hε0 : (0 : Rat) ≤ ε) (hε'0 : (0 : Rat) ≤ ε')
    (hε1 : ε ≤ (1 : Rat) / 2) (hε'1 : ε' ≤ (1 : Rat) / 2)
    (hε : ε ≤ ε') :
    hammingBallBound N ε hε0 hε1 ≤
      hammingBallBound N ε' hε'0 hε'1 :=
  by
    classical
    have hbudget := hammingBallBudget_mono (N := N) hε'0 hε
    have hmono :=
      unionBound_mono_right (D := N)
        (k₁ := hammingBallBudget N ε)
        (k₂ := hammingBallBudget N ε') hbudget
    change unionBound N (hammingBallBudget N ε)
        ≤ unionBound N (hammingBallBudget N ε')
    exact hmono

/-- Даже уточнённая оценка не превосходит полного числа подмножеств `2^N`. -/
lemma hammingBallBound_le_pow
  (N : Nat) (ε : Rat) (_h0 : (0 : Rat) ≤ ε) (_h1 : ε ≤ (1 : Rat) / 2) :
    hammingBallBound N ε _h0 _h1 ≤ 2 ^ N :=
by
  classical
  have h := unionBound_le_pow N (hammingBallBudget N ε)
  change unionBound N (hammingBallBudget N ε) ≤ 2 ^ N
  exact h

/--
  Главная сводная величина — произведение двух оценок.  Именно она
  будет фигурировать в формулировках «Covering Power» и «Incompatibility».
  В дальнейшем, если появится потребность в более точном контроле, можно
  раскрыть это определение и подставить явные формулы.
-/
noncomputable def capacityBound
  (D k N : Nat) (ε : Rat)
  (h0 : (0 : Rat) ≤ ε) (h1 : ε ≤ (1 : Rat) / 2) : Nat :=
  unionBound D k * hammingBallBound N ε h0 h1

/--
  Комбинируя оценку `unionBound_le_pow_mul` с неравенством
  `hammingBallBound ≤ 2^N`, получаем удобную верхнюю границу для всей ёмкости.
-/
lemma capacityBound_le_pow_mul
    (D k N : Nat) (ε : Rat)
    (h0 : (0 : Rat) ≤ ε) (h1 : ε ≤ (1 : Rat) / 2) :
    capacityBound D k N ε h0 h1 ≤
      (k.succ) * (Nat.max 1 D) ^ k * 2 ^ N :=
  by
    have hmul :=
      Nat.mul_le_mul_right (unionBound N (hammingBallBudget N ε))
        (unionBound_le_pow_mul D k)
    have hball :=
      Nat.mul_le_mul_left ((k.succ) * (Nat.max 1 D) ^ k)
        (unionBound_le_pow N (hammingBallBudget N ε))
    have hchain := le_trans hmul hball
    -- Переписываем обе стороны через определения `capacityBound` и `hammingBallBound`.
    change unionBound D k * unionBound N (hammingBallBudget N ε)
        ≤ (k.succ) * (Nat.max 1 D) ^ k * 2 ^ N
    exact hchain

end Counting
end Pnp3
