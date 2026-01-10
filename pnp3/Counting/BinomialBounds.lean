import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Init
import Mathlib.Tactic

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

open scoped BigOperators

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

/-!
  ### Дополнительные грубые оценки

  Для устранения оставшегося аксиоматического блока в античекере нам нужны
  ещё более жёсткие (но элементарные) оценки.  Мы сознательно избегаем
  энтропии и вероятностных аргументов: достаточно грубой комбинаторики
  «число подмножеств ≤ число k-кортежей».

  Эти оценки используются только в пункте `capacityBound < 2^N`, поэтому их
  можно считать «техническими».  Важно, что все они доказуемы внутри Lean
  без внешних аксиом.
-/

/-! #### Сумма биномиальных коэффициентов ≤ (t+1)·N^t -/

/--
  Грубая оценка биномиальной суммы через максимальный член.

  Если `N ≥ 1`, то каждая компонента `C(N, i)` ограничена сверху `N^i`, а при
  `i ≤ t` получаем `N^i ≤ N^t`.  Отсюда сумма по `i = 0..t` не превосходит
  `(t+1) · N^t`.
-/
lemma sum_choose_le_mul_pow
    (N t : Nat) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range (t.succ), Nat.choose N i) ≤ (t.succ) * N ^ t := by
  classical
  -- Для каждого `i ≤ t` применяем `choose ≤ N^i ≤ N^t`.
  have hterm :
      ∀ i ∈ Finset.range (t.succ), Nat.choose N i ≤ N ^ t := by
    intro i hi
    have hi_le : i ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hchoose : Nat.choose N i ≤ N ^ i := Nat.choose_le_pow N i
    have hmono : N ^ i ≤ N ^ t := by
      exact Nat.pow_le_pow_right hN hi_le
    exact hchoose.trans hmono
  have hsum :=
    Finset.sum_le_sum fun i hi => hterm i hi
  have hsum_const :
      (∑ _i ∈ Finset.range (t.succ), N ^ t) = t.succ * N ^ t := by
    -- Сумма констант по диапазону равна `(t+1) * const`.
    simp [Finset.card_range]
  calc
    (∑ i ∈ Finset.range (t.succ), Nat.choose N i)
        ≤ (∑ _i ∈ Finset.range (t.succ), N ^ t) := hsum
    _ = t.succ * N ^ t := hsum_const


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

/-! #### Специализация для unionBound -/

/--
  Упрощённая оценка `unionBound`: вместо `(max 1 D)^k` можно использовать `D^k`,
  если `D ≥ 1`.
-/
lemma unionBound_le_mul_pow
    (D k : Nat) (hD : 1 ≤ D) :
    unionBound D k ≤ (k.succ) * D ^ k := by
  simpa [unionBound] using sum_choose_le_mul_pow D k hD

/-! #### Оценки для hammingBallBound -/

/-- Если `ε ≤ 1/2`, то бюджет ошибок не превышает `N`. -/
lemma hammingBallBudget_le_self
    (N : Nat) {ε : Rat} (hε1 : ε ≤ (1 : Rat) / 2) :
    hammingBallBudget N ε ≤ N := by
  classical
  have hN_nonneg : (0 : Rat) ≤ (N : Rat) := by
    exact_mod_cast (Nat.zero_le N)
  -- Из `ε ≤ 1/2` следует `ε ≤ 1`, значит `ε * N ≤ N`.
  have hε1' : ε ≤ (1 : Rat) := by
    have hhalf_le : (1 : Rat) / 2 ≤ (1 : Rat) := by norm_num
    exact hε1.trans hhalf_le
  have hmul : ε * (N : Rat) ≤ (N : Rat) := by
    have hmul' : ε * (N : Rat) ≤ (1 : Rat) * (N : Rat) := by
      exact mul_le_mul_of_nonneg_right hε1' hN_nonneg
    simpa using hmul'
  have hceil :
      Int.ceil (ε * (N : Rat)) ≤ Int.ceil (N : Rat) :=
    Int.ceil_le_ceil hmul
  -- `ceil` от целого равен самому целому.
  have hceil' : Int.ceil (ε * (N : Rat)) ≤ (N : Int) := by
    simpa using hceil
  -- Переводим неравенство в `Nat`.
  have hceil_nat :
      Int.toNat (Int.ceil (ε * (N : Rat))) ≤ N := by
    simpa [Int.toNat_le] using hceil'
  simpa [hammingBallBudget] using hceil_nat

/--
  Специализированная оценка для нашего ключевого значения
  `ε = 1/(n+2)`.  В этом случае бюджет ошибок не превосходит
  `N/(n+2) + 1`, где `N = 2^n`.

  Это ровно тот уровень точности, который нужен для строгого разрыва
  `capacityBound < 2^N` в античекере.
-/
lemma hammingBallBudget_le_div_add_one (n : Nat) :
    hammingBallBudget (Nat.pow 2 n) ((1 : Rat) / (n + 2))
      ≤ Nat.pow 2 n / (n + 2) + 1 := by
  classical
  set N := Nat.pow 2 n
  -- Переводим задачу в оценку `ceil`.
  dsimp [hammingBallBudget]
  -- Переписываем выражение `1/(n+2) * N` как обычную дробь.
  -- Связываем `ceil` и `floor` на рациональном числе `N/(n+2)`.
  have hceil_floor :
      Int.ceil ((N : Rat) / (n + 2))
        ≤ Int.floor ((N : Rat) / (n + 2)) + 1 := by
    exact Int.ceil_le_floor_add_one ((N : Rat) / (n + 2))
  -- `floor` рациональной дроби совпадает с целой частью `N / (n+2)`.
  have hfloor :
      Int.floor ((N : Rat) / (n + 2)) = (N : Int) / (n + 2) := by
    simpa [Nat.cast_add] using
      (Rat.floor_intCast_div_natCast (n := (N : Int)) (d := n + 2))
  -- Подставляем найденные переписывания.
  have hceil :
      Int.ceil (((1 : Rat) / (n + 2)) * (N : Rat))
        ≤ (N / (n + 2) + 1 : Int) := by
    -- Переводим правую часть через `Int.natCast_div`.
    have hdiv :
        ((N / (n + 2) : Nat) : Int) = (N : Int) / (n + 2) := by
      exact Int.natCast_div N (n + 2)
    have hceil_eq :
        Int.ceil (((1 : Rat) / (n + 2)) * (N : Rat))
          = Int.ceil ((N : Rat) / (n + 2)) := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      Int.ceil (((1 : Rat) / (n + 2)) * (N : Rat))
          = Int.ceil ((N : Rat) / (n + 2)) := hceil_eq
      _ ≤ Int.floor ((N : Rat) / (n + 2)) + 1 := hceil_floor
      _ = (N : Int) / (n + 2) + 1 := by
            simp [hfloor]
      _ = (N / (n + 2) : Int) + 1 := by
            -- Переписываем целое деление через `natCast_div`.
            simp
  have hceil_nat :
      Int.toNat (Int.ceil (((1 : Rat) / (n + 2)) * (N : Rat)))
        ≤ N / (n + 2) + 1 := by
    simpa [Int.toNat_le] using hceil
  simpa [N] using hceil_nat

/-!
  Следующий технический шаг: подставляем точный бюджет из
  `hammingBallBudget_le_div_add_one` в оценку для `hammingBallBound`.
  Нам важно получить явную верхнюю границу вида

  `hammingBallBound ≤ (t+1) * N^t` при `t = N/(n+2)+1`.
-/
lemma hammingBallBound_twoPow_le_mul_pow_div_add_one (n : Nat)
    (hε0 : (0 : Rat) ≤ (1 : Rat) / (n + 2))
    (hε1 : (1 : Rat) / (n + 2) ≤ (1 : Rat) / 2) :
    hammingBallBound (Nat.pow 2 n) ((1 : Rat) / (n + 2)) hε0 hε1
      ≤ (Nat.pow 2 n / (n + 2) + 2)
          * (Nat.pow 2 n) ^ (Nat.pow 2 n / (n + 2) + 1) := by
  classical
  -- Зафиксируем основное обозначение `N = 2^n`.
  set N := Nat.pow 2 n
  -- Из `hammingBallBudget_le_div_add_one` получаем верхнюю границу на бюджет.
  have hbudget :
      hammingBallBudget N ((1 : Rat) / (n + 2)) ≤ N / (n + 2) + 1 := by
    simpa [N] using hammingBallBudget_le_div_add_one n
  -- Монотонность `unionBound` по бюджету даёт переход к `N/(n+2)+1`.
  have hmono :
      unionBound N (hammingBallBudget N ((1 : Rat) / (n + 2)))
        ≤ unionBound N (N / (n + 2) + 1) :=
    unionBound_mono_right (D := N) hbudget
  -- Нам нужна положительность `N`, чтобы применить `unionBound_le_mul_pow`.
  have hN : 1 ≤ N := by
    have hpos : 0 < N := by
      have htwo : 0 < (2 : Nat) := by decide
      dsimp [N]
      exact Nat.pow_pos htwo
    exact Nat.succ_le_iff.mpr hpos
  -- Применяем грубую оценку для `unionBound`.
  have hbound :
      unionBound N (N / (n + 2) + 1)
        ≤ (N / (n + 2) + 1).succ * N ^ (N / (n + 2) + 1) :=
    unionBound_le_mul_pow N (N / (n + 2) + 1) hN
  -- Склеиваем все шаги и переводим `(t+1).succ` в `t+2`.
  have hchain := le_trans hmono hbound
  have hsucc :
      (N / (n + 2) + 1).succ = N / (n + 2) + 2 := by
    calc
      (N / (n + 2) + 1).succ = N / (n + 2) + 1 + 1 := by
        simp [Nat.succ_eq_add_one]
      _ = N / (n + 2) + (1 + 1) := by
        simp [Nat.add_assoc]
      _ = N / (n + 2) + 2 := by
        simp
  -- Возвращаемся к `hammingBallBound` и переписываем итог.
  dsimp [hammingBallBound, N] at hchain
  simpa [N, hsucc] using hchain

/-!
  Вспомогательная «чисто арифметическая» лемма: для достаточно больших `n`
  экспонента `2^n` превосходит квадратичный многочлен `n (n+2)`.

  Эта оценка будет ключом для перехода от грубого «полиномиального»
  множителя к строгому разрыву с `2^(2^n)` в дальнейших доказательствах.
-/
lemma twoPow_gt_mul (n : Nat) (hn : 8 ≤ n) :
    n * (n + 2) < Nat.pow 2 n := by
  -- Делаем индукцию, начиная с `n = 8`.
  refine Nat.le_induction ?base ?step n hn
  · -- База: `n = 8` проверяется вычислением.
    decide
  · -- Шаг: из `2^n > n(n+2)` выводим `2^(n+1) > (n+1)(n+3)`.
    intro k hk ih
    have hk2 : 2 ≤ k := by
      exact le_trans (by decide : 2 ≤ 8) hk
    -- Оцениваем `(k+1)(k+3)` через `2*k*(k+2)`.
    have hbound : (k + 1) * (k + 3) ≤ 2 * (k * (k + 2)) := by
      nlinarith [hk2]
    -- Удваиваем индукционную гипотезу: `2 * (k*(k+2)) < 2 * 2^k`.
    have hdouble :
        2 * (k * (k + 2)) < 2 * (Nat.pow 2 k) := by
      exact Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < (2 : Nat))
    -- Переходим к `2^(k+1) = 2 * 2^k`.
    have hpow : 2 * Nat.pow 2 k = Nat.pow 2 (k + 1) := by
      simp [Nat.pow_succ, Nat.mul_comm]
    -- Склеиваем: `(k+1)(k+3) ≤ 2*k*(k+2) < 2^(k+1)`.
    exact lt_of_le_of_lt hbound (hdouble.trans_eq hpow)

/-- Вспомогательная оценка: при `n ≥ 8` верно `2 * n * (n + 2) ≤ 2^n`. -/
lemma twoPow_ge_twoMul_mul (n : Nat) (hn : 8 ≤ n) :
    2 * n * (n + 2) ≤ Nat.pow 2 n := by
  -- Индукция начиная с `n = 8`.
  refine Nat.le_induction ?base ?step n hn
  · -- База: `n = 8` проверяется вычислением.
    decide
  · -- Шаг: используем оценку `(k+1)(k+3) ≤ 2*k*(k+2)` при `k ≥ 2`.
    intro k hk ih
    have hk2 : 2 ≤ k := by
      exact le_trans (by decide : 2 ≤ 8) hk
    have hbound : (k + 1) * (k + 3) ≤ 2 * (k * (k + 2)) := by
      nlinarith [hk2]
    -- Из индукционной гипотезы получаем `4 * k * (k+2) ≤ 2^(k+1)`.
    have hdouble :
        2 * (2 * (k * (k + 2))) ≤ 2 * (Nat.pow 2 k) := by
      have ih' : 2 * (k * (k + 2)) ≤ Nat.pow 2 k := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ih
      exact Nat.mul_le_mul_left 2 ih'
    have hpow : 2 * Nat.pow 2 k = Nat.pow 2 (k + 1) := by
      simp [Nat.pow_succ, Nat.mul_comm]
    have hchain :
        2 * (k + 1) * (k + 3) ≤ 2 * (2 * (k * (k + 2))) := by
      -- Домножаем `hbound` на 2 и раскрываем ассоциативность.
      simpa [Nat.mul_assoc] using (Nat.mul_le_mul_left 2 hbound)
    exact
      (le_trans hchain (hdouble.trans_eq hpow))

/-- Строгая верхняя граница: при `n ≥ 8` оценка хаммингового шара
  заметно меньше `2^(2^n)`. -/
lemma hammingBallBound_twoPow_lt_twoPowPow (n : Nat) (hn : 8 ≤ n)
    (hε0 : (0 : Rat) ≤ (1 : Rat) / (n + 2))
    (hε1 : (1 : Rat) / (n + 2) ≤ (1 : Rat) / 2) :
    hammingBallBound (Nat.pow 2 n) ((1 : Rat) / (n + 2)) hε0 hε1
      < Nat.pow 2 (Nat.pow 2 n) := by
  classical
  -- Вводим обозначения `N = 2^n` и `t = N/(n+2)`.
  set N := Nat.pow 2 n
  set t := N / (n + 2)
  -- Переходим к явной верхней границе из предыдущей леммы.
  have hbound :
      hammingBallBound N ((1 : Rat) / (n + 2)) hε0 hε1
        ≤ (t + 2) * N ^ (t + 1) := by
    simpa [N, t] using
      (hammingBallBound_twoPow_le_mul_pow_div_add_one n hε0 hε1)
  -- Базовые факты о положительности степеней.
  have hNpos : 0 < N := by
    have htwo : 0 < (2 : Nat) := by decide
    dsimp [N]
    exact Nat.pow_pos htwo
  -- Свойство деления: `(n+2) * t ≤ N`.
  have hmul_le : (n + 2) * t ≤ N := by
    have h := Nat.mul_div_le N (n + 2)
    simpa [t, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  -- Из `n*(n+2) ≤ N` получаем `n ≤ t`.
  have hn_le_t : n ≤ t := by
    have hmul : n * (n + 2) ≤ N := le_of_lt (twoPow_gt_mul n hn)
    have hpos : 0 < n + 2 := by
      exact Nat.succ_pos (n + 1)
    have hdiv : n ≤ N / (n + 2) := (Nat.le_div_iff_mul_le hpos).2 hmul
    simpa [t] using hdiv
  -- Ключевое сравнение показателей: `n*(t+2) < N`.
  have hExp : n * (t + 2) < N := by
    by_cases ht : t = n
    · simpa [t, ht, N] using twoPow_gt_mul n hn
    · have hlt : n < t := lt_of_le_of_ne hn_le_t (Ne.symm ht)
      have h2lt : 2 * n < 2 * t := by
        exact Nat.mul_lt_mul_of_pos_left hlt (by decide : 0 < (2 : Nat))
      have hlt_mul : n * t + 2 * n < n * t + 2 * t := by
        exact Nat.add_lt_add_left h2lt (n * t)
      have hlt_mul' : n * (t + 2) < (n + 2) * t := by
        simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using hlt_mul
      exact lt_of_lt_of_le hlt_mul' hmul_le
  -- Из `n*(t+2) < N` следует `t+2 < N`, что нужно для умножения.
  have ht_lt : t + 2 < N := by
    have hn_pos : 0 < n := by
      exact Nat.succ_le_iff.mp (le_trans (by decide : 1 ≤ 8) hn)
    have hle : t + 2 ≤ n * (t + 2) := Nat.le_mul_of_pos_left _ hn_pos
    exact lt_of_le_of_lt hle hExp
  -- Убираем множитель `(t+2)` заменой на `N`.
  have hmul_pow :
      (t + 2) * N ^ (t + 1) < N ^ (t + 2) := by
    have hpowpos : 0 < N ^ (t + 1) := by
      exact Nat.pow_pos hNpos
    have hmul_lt := Nat.mul_lt_mul_of_pos_right ht_lt hpowpos
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul_lt
  -- Переводим степень `N^(t+2)` в `2^(n*(t+2))` и сравниваем с `2^N`.
  have hpow_lt : N ^ (t + 2) < Nat.pow 2 N := by
    have hpow_lt' : Nat.pow 2 (n * (t + 2)) < Nat.pow 2 N :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).2 hExp
    simpa [N, Nat.pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hpow_lt'
  -- Собираем итоговую цепочку.
  exact lt_of_le_of_lt hbound (lt_trans hmul_pow hpow_lt)

/--
  Грубая оценка на объём хаммингового шара: сводим к `unionBound` и затем
  применяем `sum_choose_le_mul_pow`.
-/
lemma hammingBallBound_le_mul_pow
    (N : Nat) (ε : Rat)
    (hN : 1 ≤ N)
    (hε0 : (0 : Rat) ≤ ε) (hε1 : ε ≤ (1 : Rat) / 2) :
    hammingBallBound N ε hε0 hε1
      ≤ (hammingBallBudget N ε).succ * N ^ (hammingBallBudget N ε) := by
  classical
  -- Раскрываем определение и применяем `unionBound_le_mul_pow`.
  dsimp [hammingBallBound]
  exact unionBound_le_mul_pow N (hammingBallBudget N ε) hN

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

/-- Монотонность `capacityBound` по словарю, бюджету и допустимой ошибке. -/
lemma capacityBound_mono
    {D D' k k' N : Nat} {ε ε' : Rat}
    (h0 : (0 : Rat) ≤ ε) (h1 : ε ≤ (1 : Rat) / 2)
    (h0' : (0 : Rat) ≤ ε') (h1' : ε' ≤ (1 : Rat) / 2)
    (hD : D ≤ D') (hk : k ≤ k') (hε : ε ≤ ε') :
    capacityBound D k N ε h0 h1 ≤
      capacityBound D' k' N ε' h0' h1' :=
  by
    classical
    have hUnionD : unionBound D k ≤ unionBound D' k :=
      unionBound_mono_left (k := k) hD
    have hUnion : unionBound D k ≤ unionBound D' k' :=
      le_trans hUnionD (unionBound_mono_right (D := D') hk)
    have hBall :
        hammingBallBound N ε h0 h1 ≤
          hammingBallBound N ε' h0' h1' :=
      hammingBallBound_mono (N := N) h0 h0' h1 h1' hε
    exact Nat.mul_le_mul hUnion hBall

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
