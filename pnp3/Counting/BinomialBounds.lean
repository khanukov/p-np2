import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
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
                  simpa using hsplit.symm
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
      have hM_ge : 1 ≤ M := by
        simpa [hMdef] using (le_max_left (1 : Nat) D)
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
        have hchoose : Nat.choose D i ≤ M ^ i := by
          simpa [hMdef] using choose_le_pow_max D i
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
        simpa [Finset.card_range] using this
    -- Финальный вывод — переписать исходные обозначения.
    simpa [unionBound, hMdef, hsum_const] using hsum


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
          ext; simpa using h)
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
          (Finset.univ.filter fun (S : Finset α) => S.card = i).card := by
      simpa using
        (Fintype.card_subtype (fun (S : Finset α) => S.card = i))
    have hfilter_eq :
        (Finset.univ.filter fun (S : Finset α) => S.card = i)
          = (Finset.univ : Finset α).powersetCard i := by
      apply Finset.ext
      intro S; constructor <;> intro hS
      · rcases Finset.mem_filter.1 hS with ⟨-, hcardS⟩
        have hsubset : S ⊆ (Finset.univ : Finset α) := by
          intro x _hx; simp
        simpa [Finset.mem_powersetCard, hsubset, hcardS]
      · have hcardS : S.card = i :=
          (Finset.mem_powersetCard.1 hS).2
        simp [Finset.mem_filter, hcardS]
    have hpow := Finset.card_powersetCard i (Finset.univ : Finset α)
    simpa [hcard, hfilter_eq, Finset.card_univ] using hpow

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
          simpa [x.2.2] using hx⟩
    have hleft : Function.LeftInverse fromSigma toSigma := by
      intro S
      rcases S with ⟨S, hS⟩
      rfl
    have hright : Function.RightInverse fromSigma toSigma := by
      intro x
      rcases x with ⟨i, ⟨S, hS⟩⟩
      ext <;> simp [toSigma, fromSigma, hS, Nat.lt_succ_iff]
    let e : {S : Finset α // S.card ≤ k} ≃
        Σ i : Fin (k.succ), {S : Finset α // S.card = (i : Nat)} :=
      ⟨toSigma, fromSigma, hleft, hright⟩
    have hcard_equiv := Fintype.card_congr e
    have hsigma :
        Fintype.card (Σ i : Fin (k.succ), {S : Finset α // S.card = (i : Nat)}) =
          ∑ i : Fin (k.succ), Fintype.card {S : Finset α // S.card = (i : Nat)} := by
      classical
      simpa using
        (Fintype.card_sigma (fun i : Fin (k.succ) =>
          {S : Finset α // S.card = (i : Nat)}))
    have hsum_range :
        (∑ i : Fin (k.succ),
            Fintype.card {S : Finset α // S.card = (i : Nat)})
          = ∑ i ∈ Finset.range (k.succ),
              Fintype.card {S : Finset α // S.card = i} :=
      by
        classical
        simpa using
          (sum_fin_eq_sum_range
            (fun i => Fintype.card {S : Finset α // S.card = i}) k)
    have hchoose :
        ∑ i ∈ Finset.range (k.succ),
            Fintype.card {S : Finset α // S.card = i}
          = unionBound (Fintype.card α) k :=
      by
        simp [unionBound, card_subsets_exact_choose]
    refine
      (calc
        Fintype.card {S : Finset α // S.card ≤ k}
            = Fintype.card (Σ i : Fin (k.succ),
                {S : Finset α // S.card = (i : Nat)}) := by
                simpa using hcard_equiv
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
          Fintype.card {S : Finset (Fin D) // S.card ≤ k} := by
      have :=
        (card_subsets_le_unionBound (α := Fin D) (k := k))
      -- Учитываем, что `|Fin D| = D`.
      simpa [Finset.card_fin] using this.symm
    have hcardSucc :
        unionBound D.succ k =
          Fintype.card {S : Finset (Fin D.succ) // S.card ≤ k} := by
      have :=
        (card_subsets_le_unionBound (α := Fin D.succ) (k := k))
      simpa [Finset.card_fin] using this.symm
    -- Инъективно расширяем каждое множество `S ⊆ Fin D` до `Fin (D.succ)` через `Fin.castSucc`.
    let lift (S : {S : Finset (Fin D) // S.card ≤ k}) :
        {T : Finset (Fin D.succ) // T.card ≤ k} :=
      ⟨Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S.1,
        by
          -- `Finset.map` по вложению сохраняет кардинальность.
          simpa [Finset.card_map] using S.2⟩
    -- Отображение `lift` является инъекцией.
    have h_inj : Function.Injective lift := by
      intro S₁ S₂ hS
      -- Сравниваем образы подмножеств и переходим к базовым элементам.
      have hsets :
          Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₁.1 =
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₂.1 := by
        simpa [lift] using congrArg Subtype.val hS
      -- Проверяем, что каждое `x` принадлежит `S₁` тогда и только тогда, когда принадлежит `S₂`.
      ext x; constructor <;> intro hx
      · -- Используем соответствие через `Fin.castSucc` и равенство образов.
        have hx' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₁.1 :=
          Finset.mem_map.mpr ⟨x, hx, rfl⟩
        have hx'' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₂.1 := by
          simpa [hsets] using hx'
        rcases Finset.mem_map.1 hx'' with ⟨y, hy, hyx⟩
        have : y = x := Fin.castSucc_injective _ hyx
        simpa [this] using hy
      · -- Аналогично, но меняем роли `S₁` и `S₂`.
        have hx' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₂.1 :=
          Finset.mem_map.mpr ⟨x, hx, rfl⟩
        have hx'' : Fin.castSucc x ∈
            Finset.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩ S₁.1 := by
          simpa [hsets] using hx'
        rcases Finset.mem_map.1 hx'' with ⟨y, hy, hyx⟩
        have : y = x := Fin.castSucc_injective _ hyx
        simpa [this] using hy
    -- Сравниваем мощности подмножеств при помощи полученной инъекции.
    have hcard_le :=
      Fintype.card_le_of_injective lift h_inj
    -- Возвращаемся к выражению через `unionBound`.
    simpa [hcardD, hcardSucc, lift]
      using hcard_le

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
      | zero => simpa
      | succ d ih =>
          have hstep := unionBound_le_succ (D₁ + d) k
          have hnext := le_trans ih hstep
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.succ_eq_add_one] using hnext
    have hplus : D₁ + (D₂ - D₁) = D₂ := Nat.add_sub_of_le h
    simpa [hplus] using haux (D₂ - D₁)

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
    simpa [unionBound] using hmono

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
    (hε0 : (0 : Rat) ≤ ε) (hε'0 : (0 : Rat) ≤ ε') (hε : ε ≤ ε') :
    hammingBallBudget N ε ≤ hammingBallBudget N ε' :=
  by
    classical
    have hN_nonneg : (0 : Rat) ≤ (N : Rat) := by
      exact_mod_cast (Nat.zero_le N)
    have hceil_le :
        Int.ceil (ε * (N : Rat)) ≤ Int.ceil (ε' * (N : Rat)) := by
      have hmul : ε * (N : Rat) ≤ ε' * (N : Rat) :=
        mul_le_mul_of_nonneg_right hε hN_nonneg
      simpa using (Int.ceil_le_ceil hmul)
    have hceil_nonneg :
        (0 : ℤ) ≤ Int.ceil (ε' * (N : Rat)) := by
      have hmul_nonneg : (0 : Rat) ≤ ε' * (N : Rat) :=
        mul_nonneg hε'0 hN_nonneg
      simpa using (Int.ceil_nonneg hmul_nonneg)
    have htarget :
        Int.ceil (ε * (N : Rat)) ≤
          (Int.toNat (Int.ceil (ε' * (N : Rat))) : ℤ) := by
      simpa [Int.toNat_of_nonneg hceil_nonneg] using hceil_le
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
    have hbudget := hammingBallBudget_mono (N := N) hε0 hε'0 hε
    simpa [hammingBallBound_spec] using
      (unionBound_mono_right (D := N)
        (k₁ := hammingBallBudget N ε)
        (k₂ := hammingBallBudget N ε') hbudget)

/-- Даже уточнённая оценка не превосходит полного числа подмножеств `2^N`. -/
lemma hammingBallBound_le_pow
  (N : Nat) (ε : Rat) (_h0 : (0 : Rat) ≤ ε) (_h1 : ε ≤ (1 : Rat) / 2) :
    hammingBallBound N ε _h0 _h1 ≤ 2 ^ N :=
by
  classical
  simpa [hammingBallBound_spec] using
    (unionBound_le_pow N (hammingBallBudget N ε))

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
    simpa [capacityBound, hammingBallBound_spec, Nat.mul_assoc,
      Nat.mul_left_comm] using hchain

end Counting
end Pnp3
