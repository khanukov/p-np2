import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Core.BooleanBasics
import Core.Atlas
import Counting.BinomialBounds

/-!
  pnp3/Counting/Atlas_to_LB_Core.lean

  Здесь собраны базовые определения счётной части «атласа» и их связь
  с полученными в `BinomialBounds.lean` абстрактными оценками.  Файл
  формализует три ключевые конструкции:

  * `UnionClass R k` — семейство булевых функций, получаемых как
    объединения не более чем `k` подкубов из фиксированного словаря `R`.
  * `ApproxClass R k ε` — все функции, которые можно аппроксимировать
    с ошибкой `ε` некоторой функцией из `UnionClass R k`.
  * `covering_power_bound` — утверждение о существовании верхней границы
    на мощность `ApproxClass` через параметры `(D, k, ε, m)`.

  Фактические численные оценки сейчас инкапсулированы в аксиомы, вынесенные
  в `BinomialBounds.lean`.  Это позволяет строить логику части C, не дожидаясь
  полного аналитического развития.
-/

namespace Pnp3
namespace Counting

open Pnp3.Core

/-- Для удобства переобозначим рациональные числа. -/
abbrev Q := Rat

/--
  Полное пространство входов `X = {0,1}^m` реализовано как вектора битов.
  Тип объявлен в базовом модуле `BooleanBasics`, здесь лишь вводим
  сокращённое обозначение для читаемости формул.  Явно указываем, что
  используем версию `BitVec` из пространства `Core`, чтобы избежать
  неоднозначности с одноимённым типом из стандартной библиотеки Lean.
-/
abbrev Domain (m : Nat) := Core.BitVec m

/--
  Хаммингово расстояние между двумя функциями: число точек, где они различны.
  Формально это мощность фильтра `Finset`, выделяющего несовпадающие элементы
  пространства `Domain m`.
-/
def distU {m : Nat} (f g : Domain m → Bool) : Nat :=
  ((Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)).card

/--
  Класс функций, которые являются объединением не более чем `k` подкубов
  из словаря `R`.  Мы представляем подкубы списком и используем булев
  индикатор `coveredB` из базовой библиотеки.
-/
def UnionClass {m : Nat} (R : List (Subcube m)) (k : Nat) :
    Set (Domain m → Bool) :=
  { g | ∃ (S : List (Subcube m)),
      S.length ≤ k ∧
      listSubset S R ∧
      g = fun x => coveredB S x }

/--
  Класс `ApproxClass R k ε` содержит все функции `f`, которые можно
  аппроксимировать с ошибкой не более `ε` функцией из `UnionClass`.
  Ошибка измеряется через `distU` и нормируется на размер пространства `2^m`.
-/
def ApproxClass {m : Nat}
    (R : List (Subcube m)) (k : Nat) (ε : Q) :
    Set (Domain m → Bool) :=
  { f | ∃ g, g ∈ UnionClass R k ∧
        (distU f g : Q) ≤ ε * ((Nat.pow 2 m : Nat) : Q) }

/-- Нулевая ошибка на расстоянии соответствует точному совпадению функций. -/
lemma distU_eq_zero_of_eq
    {m : Nat} {f g : Domain m → Bool} (h : f = g) :
    distU f g = 0 := by
  subst h
  simp [distU]

/-- Обратное направление: нулевая дистанция означает, что функции совпадают. -/
lemma distU_eq_zero_iff
    {m : Nat} {f g : Domain m → Bool} :
    distU f g = 0 ↔ f = g := by
  constructor
  · intro h
    have hempty :
        ((Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)) =
          (∅ : Finset (Domain m)) := by
      exact Finset.card_eq_zero.mp h
    funext x
    have hx_mem : x ∈ (Finset.univ : Finset (Domain m)) := by
      simpa using (Finset.mem_univ x)
    have hx_not :
        x ∉ ((Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)) := by
      simpa [hempty] using (Finset.not_mem_empty x)
    have hx_contra : f x ≠ g x → False := by
      intro hne
      have hx_filter :
          x ∈ ((Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)) :=
        Finset.mem_filter.mpr ⟨hx_mem, hne⟩
      exact hx_not hx_filter
    by_contra hne
    exact hx_contra hne
  · intro h
    simpa [distU, h]

/-- Связываем `errU` с `distU`: ошибка аппроксимации равна числу несовпадений,
  делённому на размер пространства `2^m`. -/
lemma errU_eq_distU_div_pow
    {m : Nat} (f : Domain m → Bool) (S : List (Subcube m)) :
    errU f S =
      (distU f (fun x => coveredB S x) : Q) /
        ((Nat.pow 2 m : Nat) : Q) := by
  classical
  unfold errU distU
  simp

/-- Если ошибка аппроксимации мала, то и расстояние `distU` удовлетворяет
  соответствующей границе. -/
lemma distU_le_of_errU_le
    {m : Nat} (f : Domain m → Bool) (S : List (Subcube m))
    (ε : Q) (h : errU f S ≤ ε) :
    (distU f (fun x => coveredB S x) : Q)
      ≤ ε * ((Nat.pow 2 m : Nat) : Q) := by
  classical
  have hpow_pos :
      (0 : Q) < ((Nat.pow 2 m : Nat) : Q) := by
    have hNat : 0 < Nat.pow 2 m := by
      induction m with
      | zero => simp
      | succ m ih =>
          have hbase : 0 < 2 := by decide
          simpa [Nat.pow_succ] using Nat.mul_pos hbase ih
    exact_mod_cast hNat
  have h' :
      (distU f (fun x => coveredB S x) : Q)
        / ((Nat.pow 2 m : Nat) : Q) ≤ ε := by
    simpa [errU_eq_distU_div_pow] using h
  have hmul := mul_le_mul_of_nonneg_right h' (le_of_lt hpow_pos)
  have hden_ne : ((Nat.pow 2 m : Nat) : Q) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpow_pos)
  simpa [div_mul_eq_mul_div, hden_ne, mul_left_comm, mul_assoc]
    using hmul

/-- Обратное неравенство: если расстояние `distU` малое, то и ошибка `errU`
    не превосходит `ε`. -/
lemma errU_le_of_distU_le
    {m : Nat} (f : Domain m → Bool) (S : List (Subcube m))
    (ε : Q)
    (h : (distU f (fun x => coveredB S x) : Q)
          ≤ ε * ((Nat.pow 2 m : Nat) : Q)) :
    errU (n := m) f S ≤ ε := by
  classical
  have hpow_pos : 0 < ((Nat.pow 2 m : Nat) : Q) := by
    have hNat : 0 < Nat.pow 2 m := by
      induction m with
      | zero => simp
      | succ m ih =>
          have : 0 < 2 := by decide
          simpa [Nat.pow_succ] using Nat.mul_pos this ih
    exact_mod_cast hNat
  have hden_ne : ((Nat.pow 2 m : Nat) : Q) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpow_pos)
  have hmul :=
    mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hpow_pos))
  have hdiv :
      (distU f (fun x => coveredB S x) : Q)
          / ((Nat.pow 2 m : Nat) : Q) ≤ ε := by
    simpa [div_eq_mul_inv, hden_ne, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  simpa [errU_eq_distU_div_pow] using hdiv

/-- Обобщённое включение: если существует поднабор словаря, аппроксимирующий
  функцию `f` с ошибкой ≤ `ε`, то `f` принадлежит классу `ApproxClass`. -/
lemma approx_mem_of_errU_le
    {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
    {f : Domain m → Bool}
    (h : ∃ S : List (Subcube m),
      S.length ≤ k ∧ listSubset S R ∧ errU f S ≤ ε) :
    f ∈ ApproxClass (R := R) (k := k) (ε := ε) := by
  classical
  rcases h with ⟨S, hlen, hsubset, herr⟩
  refine ⟨(fun x => coveredB S x), ?_, ?_⟩
  · exact ⟨S, hlen, hsubset, rfl⟩
  · exact distU_le_of_errU_le (f := f) (S := S) (ε := ε) herr

/-- Из принадлежности классу `ApproxClass` извлекаем явный набор подкубов,
    аппроксимирующий функцию `f` с ошибкой `ε`. -/
lemma errU_exists_of_mem_approx
    {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
    {f : Domain m → Bool}
    (hf : f ∈ ApproxClass (R := R) (k := k) (ε := ε)) :
    ∃ S : List (Subcube m),
      S.length ≤ k ∧ listSubset S R ∧ errU (n := m) f S ≤ ε := by
  classical
  rcases hf with ⟨g, hg_union, hdist⟩
  rcases hg_union with ⟨S, hlen, hsubset, hfun⟩
  refine ⟨S, hlen, hsubset, ?_⟩
  have hdist' :
      (distU f (fun x => coveredB S x) : Q)
        ≤ ε * ((Nat.pow 2 m : Nat) : Q) := by
    simpa [hfun] using hdist
  exact errU_le_of_distU_le (f := f) (S := S) (ε := ε) hdist'

/-- Любая функция из `UnionClass` автоматически лежит в `ApproxClass` при ε = 0. -/
lemma union_subset_approx_zero
    {m : Nat} (R : List (Subcube m)) (k : Nat) :
    UnionClass R k ⊆ ApproxClass (R := R) (k := k) (ε := 0) := by
  classical
  intro f hf
  refine ⟨f, ?_, ?_⟩
  · simpa using hf
  · have hdist : distU f f = 0 :=
      distU_eq_zero_of_eq (m := m) (f := f) (g := f) rfl
    have hco : (distU f f : Q) = 0 := by exact_mod_cast hdist
    have : (distU f f : Q) ≤ 0 := by simpa [hco]
    simpa using this

/-- Обратное включение: при `ε = 0` аппроксимация совпадает с исходным
  объединением подкубов. -/
lemma approx_subset_union_zero
    {m : Nat} (R : List (Subcube m)) (k : Nat) :
    ApproxClass (R := R) (k := k) (ε := 0) ⊆ UnionClass R k := by
  classical
  intro f hf
  rcases hf with ⟨g, hg_union, hdist⟩
  have hdist' : (distU f g : Q) ≤ 0 := by
    simpa using hdist
  have hnonneg : (0 : Q) ≤ (distU f g : Q) := by
    exact_mod_cast (Nat.zero_le (distU f g))
  have hzero : (distU f g : Q) = 0 := le_antisymm hdist' hnonneg
  have hdistNat : distU f g = 0 := by
    exact_mod_cast hzero
  have hfg : f = g := (distU_eq_zero_iff (f := f) (g := g)).mp hdistNat
  simpa [hfg] using hg_union

/-- Полное равенство классов при нулевой ошибке. -/
lemma approx_zero_eq_union
    {m : Nat} (R : List (Subcube m)) (k : Nat) :
    ApproxClass (R := R) (k := k) (ε := 0) = UnionClass R k := by
  apply Set.Subset.antisymm
  · exact approx_subset_union_zero (R := R) (k := k)
  · exact union_subset_approx_zero (R := R) (k := k)

/--
  Размер словаря.  Отдельное определение помогает сделать последующие
  формулы более читабельными.
-/
def dictLen {m : Nat} (R : List (Subcube m)) : Nat := R.length

/--
  Удобное обозначение для подтипа, отвечающего элементам класса
  `UnionClass`.  Хранится сама функция и доказательство принадлежности.
-/
abbrev UnionSubtype {m : Nat} (R : List (Subcube m)) (k : Nat) :=
  {g : Domain m → Bool // g ∈ UnionClass R k}

/-- Подтип функций, удовлетворяющих ограничению на расстояние до `g`. -/
abbrev HammingBallSubtype {m : Nat} (g : Domain m → Bool)
    (ε : Q) : Type :=
  {f : Domain m → Bool //
      (distU f g : Q) ≤ ε * ((Nat.pow 2 m : Nat) : Q)}

/-- Подтип для ε-аппроксимируемых функций. -/
abbrev ApproxSubtype {m : Nat} (R : List (Subcube m))
    (k : Nat) (ε : Q) : Type :=
  {f : Domain m → Bool // f ∈ ApproxClass R k ε}

/-- На подтипах автоматически наследуем конечность из пространства всех функций. -/
noncomputable instance instFintypeUnionSubtype
    {m : Nat} (R : List (Subcube m)) (k : Nat) :
    Fintype (UnionSubtype (R := R) (k := k)) := by
  classical
  infer_instance

noncomputable instance instFintypeHammingBallSubtype
    {m : Nat} (g : Domain m → Bool) (ε : Q) :
    Fintype (HammingBallSubtype (m := m) (g := g) (ε := ε)) := by
  classical
  infer_instance

noncomputable instance instFintypeApproxSubtype
    {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q) :
    Fintype (ApproxSubtype (R := R) (k := k) (ε := ε)) := by
  classical
  infer_instance

/--
  Верхняя оценка на число различных объединений `≤ k` подкубов словаря.
  Аксиома фиксирует существование конечного `Bound`, совпадающего со значением
  `unionBound (|R|, k)` из файла `BinomialBounds`.  В дальнейшем, когда
  комбинаторная часть будет полностью формализована, этот факт заменится на
  доказательство через биномиальные коэффициенты.
-/
axiom unionClass_card_bound
  {m : Nat} (R : List (Subcube m)) (k : Nat) :
  Fintype.card (UnionSubtype (R := R) (k := k))
    ≤ unionBound (dictLen R) k

/--
  Верхняя оценка на размер хаммингового шара около фиксированной функции `g`.
  Аналитическая часть спрятана в значении `hammingBallBound`.  Как только в
  проект будет добавлена строгая энтропийная оценка, эту аксиому можно будет
  заменить на доказанную лемму.
-/
axiom hammingBall_card_bound
  {m : Nat} (g : Domain m → Bool) (ε : Q)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
  Fintype.card (HammingBallSubtype (m := m) (g := g) (ε := ε))
    ≤ hammingBallBound (Nat.pow 2 m) ε hε0 hε1

/--
  Каждой ε-аппроксимируемой функции сопоставляем пару: выбранный центр `g`
  из `UnionClass` и саму функцию как элемент соответствующего хаммингового шара.
  Для «сюръективного» описания используется аксиома выбора (доступная через
  `classical`).  Эта конструкция понадобится при оценке мощности `ApproxClass`.
-/
noncomputable def approxWitness
    {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
    (_hε0 : (0 : Q) ≤ ε) (_hε1 : ε ≤ (1 : Q) / 2) :
    ApproxSubtype (R := R) (k := k) (ε := ε) →
      Σ g : UnionSubtype (R := R) (k := k),
        HammingBallSubtype (m := m) (g := g.1) (ε := ε) :=
  by
    classical
    intro f
    -- Используем классический выбор, чтобы извлечь центр аппроксимации.
    let g := Classical.choose f.property
    have hg : g ∈ UnionClass R k := (Classical.choose_spec f.property).1
    have hdist : (distU f.1 g : Q) ≤ ε * ((Nat.pow 2 m : Nat) : Q) :=
      (Classical.choose_spec f.property).2
    refine ⟨⟨g, hg⟩, ⟨f.1, ?_⟩⟩
    simpa using hdist

/--
  Конструкция `approxWitness` инъективна: если две функции отображаются в одну
  и ту же пару `(g, f)`, то совпадают и сами функции.
-/
lemma approxWitness_injective
    {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
    (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
    Function.Injective
      (approxWitness (m := m) (R := R) (k := k) (ε := ε) hε0 hε1) :=
  by
    classical
    intro f₁ f₂ h
    have hfun := congrArg (fun x => x.2.1) h
    -- `Subtype.ext` сводит равенство элементов подтипа к равенству носителей.
    apply Subtype.ext
    simpa using hfun

/--
  Вспомогательное равенство: мощность множества «свидетельств» равна сумме
  мощностей соответствующих хамминговых шаров.
-/
lemma card_witness
    {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q) :
    Fintype.card
      (Σ g : UnionSubtype (R := R) (k := k),
        HammingBallSubtype (m := m) (g := g.1) (ε := ε)) =
      ∑ g : UnionSubtype (R := R) (k := k),
        Fintype.card
          (HammingBallSubtype (m := m) (g := g.1) (ε := ε)) :=
    by
      classical
      simpa using (Fintype.card_sigma (fun g =>
        HammingBallSubtype (m := m) (g := g.1) (ε := ε)))

/--
  Основное утверждение «Covering Power»: мощность ε-аппроксимируемых функций
  ограничена произведением оценок из `BinomialBounds`.
-/
theorem covering_power_bound
  {m : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
  Fintype.card (ApproxSubtype (R := R) (k := k) (ε := ε)) ≤
    capacityBound (dictLen R) k (Nat.pow 2 m) ε hε0 hε1 := by
  classical
  -- Обозначим параметры ёмкости словаря.
  let D := dictLen R
  let hBall := hammingBallBound (Nat.pow 2 m) ε hε0 hε1
  let Cap := capacityBound D k (Nat.pow 2 m) ε hε0 hε1
  -- Инъекция из `ApproxClass` в пространство свидетелей.
  have h_inj := Fintype.card_le_of_injective
    (approxWitness (m := m) (R := R) (k := k) (ε := ε) hε0 hε1)
    (approxWitness_injective (m := m) (R := R) (k := k)
      (ε := ε) hε0 hε1)
  -- Суммарная мощность пространства свидетелей.
  have h_card := card_witness (m := m) (R := R) (k := k) (ε := ε)
  -- Для каждого центра `g` используем энтропийную оценку хаммингового шара.
  have h_ball_le : ∀ g : UnionSubtype (R := R) (k := k),
      Fintype.card
          (HammingBallSubtype (m := m) (g := g.1) (ε := ε))
        ≤ hBall :=
    by
      intro g
      simpa using hammingBall_card_bound (m := m) (g := g.1)
        (ε := ε) hε0 hε1
  -- Переписываем оценку на сумму мощностей шаров.
  have h_sum_le :
      ∑ g : UnionSubtype (R := R) (k := k),
          Fintype.card
            (HammingBallSubtype (m := m) (g := g.1) (ε := ε))
        ≤ ∑ _g : UnionSubtype (R := R) (k := k), hBall :=
    by
      refine Finset.sum_le_sum ?_
      intro g _
      exact h_ball_le g
  -- Сумма констант равна произведению мощности индексного множества на константу.
  have h_sum_const :
      ∑ _g : UnionSubtype (R := R) (k := k), hBall =
        Fintype.card (UnionSubtype (R := R) (k := k)) * hBall :=
    by
      classical
      simpa using Finset.sum_const_nat hBall
        (Finset.univ : Finset (UnionSubtype (R := R) (k := k)))
  -- Соединяем предыдущие равенства.
  have h_witness_le :
      Fintype.card
          (Σ g : UnionSubtype (R := R) (k := k),
            HammingBallSubtype (m := m) (g := g.1) (ε := ε))
        ≤ Fintype.card (UnionSubtype (R := R) (k := k)) * hBall :=
    by
      -- Подставляем `card_witness` и упрощаем.
      simpa [h_card, h_sum_const] using h_sum_le
  -- Замыкаем оценку через границу на число базовых объединений.
  have h_union_le :
      Fintype.card (UnionSubtype (R := R) (k := k)) ≤ unionBound D k :=
    unionClass_card_bound (R := R) (k := k)
  have h_mul_le :
      Fintype.card (UnionSubtype (R := R) (k := k)) * hBall ≤
        unionBound D k * hBall :=
    Nat.mul_le_mul_right _ h_union_le
  -- Сводим оценку на мощности свидетельств к заявленной ёмкости.
  have h_witness_cap :
      Fintype.card
          (Σ g : UnionSubtype (R := R) (k := k),
            HammingBallSubtype (m := m) (g := g.1) (ε := ε))
        ≤ Cap :=
    by
      have := Nat.le_trans h_witness_le h_mul_le
      simpa [Cap, capacityBound, hBall] using this
  -- Теперь окончательно ограничиваем мощность `ApproxClass`.
  exact Nat.le_trans h_inj h_witness_cap

/--
  Удобная переформулировка: если заранее известно, что словарь имеет
  длину `D`, можно подставить это значение напрямую.
-/
theorem covering_power_bound_by_size
  {m D : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
  (hR : dictLen R = D)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
  Fintype.card (ApproxSubtype (R := R) (k := k) (ε := ε)) ≤
    capacityBound D k (Nat.pow 2 m) ε hε0 hε1 := by
  -- Используем общую границу и переписываем правую часть через условие `|R| = D`.
  have h := covering_power_bound (R := R) (k := k) (ε := ε) hε0 hε1
  have hcap :
      capacityBound (dictLen R) k (Nat.pow 2 m) ε hε0 hε1 =
        capacityBound D k (Nat.pow 2 m) ε hε0 hε1 := by
    simp [hR]
  simpa [hcap] using h

/-- Удобная форма через `Nat.card`: совпадает с предыдущей теоремой. -/
lemma approxClass_card_le_capacity
  {m D : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
  (hR : dictLen R = D)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
  Nat.card (ApproxSubtype (R := R) (k := k) (ε := ε)) ≤
    capacityBound D k (Nat.pow 2 m) ε hε0 hε1 := by
  classical
  simpa [Nat.card_eq_fintype_card] using
    (covering_power_bound_by_size (R := R) (k := k) (ε := ε)
      (hR := hR) hε0 hε1)

/--
  Обобщённый критерий несовместимости.  Если семейство `Y` имеет мощность,
  превышающую ёмкость, то никакой словарь размера `D` не может ε-аппроксимировать
  все функции из `Y` выбором ≤ k подкубов.  Формальное содержание — внешняя
  аксиома, которая будет заменена на строгий вывод после интеграции части C.
-/
axiom incompatibility
  {m D : Nat} (k : Nat) (ε : Q)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2)
  (CardY : Nat)
  (hLarge : CardY >
    capacityBound D k (Nat.pow 2 m) ε hε0 hε1) : True

end Counting
end Pnp3
