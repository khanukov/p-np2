import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
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

  Все численные оценки берутся из строго доказанных лемм файла
  `BinomialBounds.lean`, поэтому логика части C использует исключительно
  проверенные внутри Lean факты без каких-либо аксиом.
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

/-- Множество точек, на которых функции `f` и `g` различаются.  Это «маска»
  для восстановления функции по центру шара. -/
def mismatchSet {m : Nat} (g : Domain m → Bool) (f : Domain m → Bool) :
    Finset (Domain m) :=
  (Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)

@[simp] lemma mem_mismatchSet {m : Nat}
    (g : Domain m → Bool) (f : Domain m → Bool) (x : Domain m) :
    x ∈ mismatchSet (m := m) g f ↔ f x ≠ g x := by
  classical
  simp [mismatchSet]

/-- Переключаем функцию `g` на точках из `S`, оставляя остальные значения
  без изменений. -/
def flipOn {m : Nat} (g : Domain m → Bool) (S : Finset (Domain m)) :
    Domain m → Bool :=
  fun x => if x ∈ S then ! g x else g x

@[simp] lemma mismatchSet_flipOn {m : Nat}
    (g : Domain m → Bool) (S : Finset (Domain m)) :
    mismatchSet (m := m) g (flipOn g S) = S := by
  classical
  ext x
  by_cases hx : x ∈ S
  · by_cases hg : g x
    · simp [mismatchSet, flipOn, hx]
    · simp [mismatchSet, flipOn, hx]
  · by_cases hg : g x
    · simp [mismatchSet, flipOn, hx]
    · simp [mismatchSet, flipOn, hx]

private lemma bool_eq_not_of_ne {b c : Bool} (h : b ≠ c) : b = ! c := by
  -- Перебираем случаи на булевых значениях; при `b = c` получаем противоречие,
  -- а в остальных случаях равенство тривиально.
  cases b <;> cases c
  · exact (False.elim (h rfl))
  · simp
  · simp
  · exact (False.elim (h rfl))

@[simp] lemma flipOn_mismatchSet {m : Nat}
    (g : Domain m → Bool) (f : Domain m → Bool) :
    flipOn g (mismatchSet (m := m) g f) = f := by
  classical
  funext x
  by_cases hx : f x = g x
  · have hx' : x ∉ mismatchSet (m := m) g f := by
      simp [mismatchSet, hx]
    simp [flipOn, hx, hx']
  · have hx' : x ∈ mismatchSet (m := m) g f := by
      simp [mismatchSet, hx]
    have hflip : f x = ! g x := bool_eq_not_of_ne hx
    simp [flipOn, hx', hflip]

lemma distU_card_mismatch {m : Nat}
    (g : Domain m → Bool) (f : Domain m → Bool) :
    distU f g = (mismatchSet (m := m) g f).card := by
  classical
  simp [distU, mismatchSet]

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
      simp
    have hx_not :
        x ∉ ((Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)) := by
      simp [hempty]
    have hx_contra : f x ≠ g x → False := by
      intro hne
      have hx_filter :
          x ∈ ((Finset.univ : Finset (Domain m)).filter (fun x => f x ≠ g x)) :=
        Finset.mem_filter.mpr ⟨hx_mem, hne⟩
      exact hx_not hx_filter
    by_contra hne
    exact hx_contra hne
  · intro h
    simp [distU, h]

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
      | succ m _ =>
          exact Nat.pow_pos (by decide : 0 < (2 : Nat))
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
      | succ m _ =>
          exact Nat.pow_pos (by decide : 0 < (2 : Nat))
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
  · exact hf
  · have hdist : distU f f = 0 :=
      distU_eq_zero_of_eq (m := m) (f := f) (g := f) rfl
    have hco : (distU f f : Q) = 0 := by exact_mod_cast hdist
    have : (distU f f : Q) ≤ 0 * ((Nat.pow 2 m : Nat) : Q) := by
      simp [hco, zero_mul]
    exact this

/-- Обратное включение: при `ε = 0` аппроксимация совпадает с исходным
  объединением подкубов. -/
lemma approx_subset_union_zero
    {m : Nat} (R : List (Subcube m)) (k : Nat) :
    ApproxClass (R := R) (k := k) (ε := 0) ⊆ UnionClass R k := by
  classical
  intro f hf
  rcases hf with ⟨g, hg_union, hdist⟩
  have hdistNat : distU f g = 0 := by
    have h := hdist
    simp [zero_mul] at h
    exact h
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

private def subsetSubtypeEquivPowerset
    {α : Type*} [DecidableEq α] (T : Finset α) :
    {S : Finset α // S ⊆ T} ≃ {S : Finset α // S ∈ T.powerset} :=
  { toFun :=
      fun S =>
        ⟨S.1,
          by
            have hsubset := S.2
            exact Finset.mem_powerset.mpr hsubset⟩,
    invFun :=
      fun S =>
        ⟨S.1,
          by
            have hmem := Finset.mem_powerset.mp S.2
            exact hmem⟩,
    left_inv :=
      by
        intro S
        cases' S with S hS
        rfl,
    right_inv :=
      by
        intro S
        cases' S with S hS
        rfl }

noncomputable instance instFintypeSubsetSubtype
    {α : Type*} [DecidableEq α] (T : Finset α) :
    Fintype {S : Finset α // S ⊆ T} :=
  Fintype.ofEquiv _ (subsetSubtypeEquivPowerset (T := T)).symm
lemma subsetsSubtype_card_eq_pow
    {α : Type*} [DecidableEq α] (T : Finset α) :
    Fintype.card {S : Finset α // S ⊆ T} = 2 ^ T.card :=
  by
    classical
    have hcongr :
        Fintype.card {S : Finset α // S ⊆ T} =
          Fintype.card {S : Finset α // S ∈ T.powerset} := by
      refine Fintype.card_congr ?hEquiv
      exact subsetSubtypeEquivPowerset (T := T)
    have hcard :
        Fintype.card {S : Finset α // S ∈ T.powerset} = T.powerset.card := by
      exact Fintype.card_coe (s := T.powerset)
    have hpow : T.powerset.card = 2 ^ T.card := Finset.card_powerset T
    calc
      Fintype.card {S : Finset α // S ⊆ T}
          = Fintype.card {S : Finset α // S ∈ T.powerset} := hcongr
      _ = T.powerset.card := hcard
      _ = 2 ^ T.card := hpow

private def sigmaConstEquiv (α β : Type*) : (Σ _ : α, β) ≃ α × β :=
  { toFun := fun x => ⟨x.1, x.2⟩,
    invFun := fun x => ⟨x.1, x.2⟩,
    left_inv := by intro x; cases x; rfl,
    right_inv := by intro x; cases x; rfl }

/-
  Верхняя оценка на число различных объединений `≤ k` подкубов словаря.
  Ранее она была зафиксирована в виде аксиомы, но после полной формализации
  биномиальных оценок мы можем предъявить явный перебор: любой кандидат
  задаётся подмножеством словаря мощности ≤ `k`, а число таких подмножеств
  ограничено `unionBound (dictLen R) k`.
-/
theorem unionClass_card_bound
  {m : Nat} (R : List (Subcube m)) (k : Nat) :
  Fintype.card (UnionSubtype (R := R) (k := k))
    ≤ unionBound (dictLen R) k := by
  classical
  -- Тип элементов словаря без дубликатов и соответствующий домен подсчёта.
  set DictSubtype := {β : Subcube m // β ∈ R.toFinset}
  let Domain := {S : Finset DictSubtype // S.card ≤ k}
  -- Получаем список подкубов из конечного множества без повторов.
  let toList : Finset DictSubtype → List (Subcube m) := fun S =>
    S.1.toList.map Subtype.val
  -- Отображение домена подсчёта в семейство `UnionClass`.
  let toUnion : Domain → UnionSubtype (R := R) (k := k) :=
    fun S =>
      ⟨fun x => coveredB (toList S.1) x, by
        refine ⟨toList S.1, ?_, ?_, rfl⟩
        · -- Длина списка совпадает с кардинальностью подмножества.
          have hlen : (toList S.1).length = S.1.card := by
            simp [toList]
          simpa [hlen] using S.2
        · -- Каждый подкуб списка принадлежит исходному словарю.
          intro β hβ
          rcases List.mem_map.1 hβ with ⟨δ, hδ, rfl⟩
          have hδS : δ ∈ S.1 := by
            simpa [Finset.mem_toList] using hδ
          have hδR : δ.val ∈ R := List.mem_toFinset.mp δ.property
          exact hδR⟩
  -- Сюръективность: любой элемент `UnionClass` получается из некоторого подмножества.
  have hsurj : Function.Surjective toUnion := by
    intro g
    rcases g.property with ⟨S, hS_len, hS_subset, hcover⟩
    -- Удаляем дубликаты и поднимаем их до финсета.
    set T := S.dedup
    have hT_subset : listSubset T R := by
      simpa [T] using
        (listSubset_dedup (xs := S) (ys := R) hS_subset)
    have hsubset_fin : T.toFinset ⊆ R.toFinset := by
      simpa [T] using
        (listSubset_toFinset_subset (xs := T) (ys := R) hT_subset)
    -- Инъективная упаковка элементов `T` в словарь.
    let embedding : {β // β ∈ T.toFinset} ↪ DictSubtype :=
      { toFun := fun β => ⟨β.1, hsubset_fin β.2⟩
        , inj' := by
            intro β₁ β₂ hβ
            apply Subtype.ext
            simpa using congrArg Subtype.val hβ }
    let subset : Finset DictSubtype :=
      (T.toFinset).attach.map embedding
    -- Бюджет подмножества ограничен `k`.
    have hsubset_card : subset.card ≤ k := by
      classical
      have hattach := Finset.card_attach (s := T.toFinset)
      have hmap :=
        Finset.card_map (f := embedding) (s := (T.toFinset).attach)
      have hcard_eq : subset.card = T.toFinset.card := by
        simpa [subset, hattach] using hmap
      have hsubset_TS : T.toFinset ⊆ S.toFinset := by
        intro β hβ
        have hβlist : β ∈ T := List.mem_toFinset.mp hβ
        have hβS : β ∈ S := by
          simpa [T] using List.mem_dedup.mp hβlist
        exact List.mem_toFinset.mpr hβS
      have hcard_le : T.toFinset.card ≤ S.toFinset.card := by
        refine Finset.card_le_card ?_
        intro β hβ
        exact hsubset_TS hβ
      have hS_card : S.toFinset.card ≤ S.length :=
        toFinset_card_le_length (xs := S)
      have : T.toFinset.card ≤ k :=
        Nat.le_trans (Nat.le_trans hcard_le hS_card) hS_len
      simpa [hcard_eq] using this
    refine ⟨⟨subset, hsubset_card⟩, ?_⟩
    -- Связываем значения списков через равенство соответствующих финсетов.
    have hsubset_image :
        subset.image (fun δ : DictSubtype => δ.val) = T.toFinset := by
      apply Finset.ext
      intro β
      constructor
      · intro hβ
        rcases Finset.mem_image.1 hβ with ⟨δ, hδsubset, hδβ⟩
        rcases Finset.mem_map.1 hδsubset with ⟨γ, hγattach, rfl⟩
        rcases γ with ⟨γ, hγ⟩
        have hγmem : γ ∈ T.toFinset := hγ
        have hγβ : γ = β := by
          simpa [embedding] using hδβ
        simpa [hγβ] using hγmem
      · intro hβ
        have hattach : ⟨β, hβ⟩ ∈ (T.toFinset).attach := by
          simp
        have hδsubset : embedding ⟨β, hβ⟩ ∈ subset := by
          refine (Finset.mem_map.2 ?_)
          refine ⟨⟨β, hβ⟩, hattach, rfl⟩
        exact Finset.mem_image.2 ⟨embedding ⟨β, hβ⟩, hδsubset, rfl⟩
    have hlist_finset :
        (toList subset).toFinset = subset.image (fun δ : DictSubtype => δ.val) := by
      classical
      simpa [toList] using
        (Core.toList_mapSubtype_val_toFinset (S := subset))
    have hvals : (toList subset).toFinset = T.toFinset := by
      simpa [hsubset_image] using hlist_finset
    -- Функция покрытия совпадает с исходной.
    apply Subtype.ext
    funext x
    have hcov_subset : coveredB (toList subset) x = coveredB T x := by
      have := coveredB_eq_of_toFinset_eq (n := m) (R₁ := toList subset)
          (R₂ := T) (by simpa [toList] using hvals)
      simpa [toList] using congrArg (fun f => f x) this
    have hcov_dedup : coveredB T x = coveredB S x := by
      simpa [T] using coveredB_dedup (n := m) (R := S) (x := x)
    have hgoal : coveredB (toList subset) x = coveredB S x :=
      hcov_subset.trans hcov_dedup
    have hg_eq : g.1 x = coveredB S x := by
      simp [hcover]
    have hfinal : coveredB (toList subset) x = g.1 x :=
      hgoal.trans hg_eq.symm
    simpa [toList] using hfinal
  -- Мощность домена подсчёта совпадает с `unionBound`.
  have hdomain_card :
      Fintype.card Domain = unionBound (R.toFinset.card) k := by
    classical
    have h :=
      (card_subsets_le_unionBound (α := DictSubtype) (k := k))
    have hdict_card : Fintype.card DictSubtype = R.toFinset.card := by
      simpa [DictSubtype] using Fintype.card_coe (R.toFinset)
    calc
      Fintype.card Domain
          = unionBound (Fintype.card DictSubtype) k := h
      _ = unionBound (R.toFinset.card) k := by
          simp [hdict_card]
  -- Сюръективность даёт верхнюю границу через мощность домена.
  have hcard_le :
      Fintype.card (UnionSubtype (R := R) (k := k))
        ≤ Fintype.card Domain :=
    Fintype.card_le_of_surjective toUnion hsurj
  -- Переписываем мощность домена через `unionBound` и увеличиваем словарь до длины списка.
  have :
      Fintype.card (UnionSubtype (R := R) (k := k))
        ≤ unionBound (R.toFinset.card) k := by
    simpa [hdomain_card] using hcard_le
  have hmono : unionBound (R.toFinset.card) k ≤ unionBound (dictLen R) k := by
    have hcard_le_len : R.toFinset.card ≤ dictLen R :=
      by simpa [dictLen] using toFinset_card_le_length (xs := R)
    exact unionBound_mono_left (k := k) hcard_le_len
  exact this.trans hmono

/--
  Верхняя оценка на размер хаммингового шара около фиксированной функции `g`.
  В отличие от ранних версий проекта мы доказываем её напрямую: подтип
  `HammingBallSubtype` вложен в множество всех булевых функций на `Domain m`,
  а потому его мощность не превосходит `2^(2^m)` — именно эту величину и
  возвращает `hammingBallBound`.
-/
theorem hammingBall_card_bound
  {m : Nat} (g : Domain m → Bool) (ε : Q)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
  Fintype.card (HammingBallSubtype (m := m) (g := g) (ε := ε))
    ≤ hammingBallBound (Nat.pow 2 m) ε hε0 hε1 :=
by
  classical
  -- Бюджет ошибок в натуральных единицах.
  let budget := hammingBallBudget (Nat.pow 2 m) ε
  -- Отображаем элемент шара в множество рассогласований, снабжённое доказательством
  -- того, что его размер не превышает `budget`.
  let toSubset :
      HammingBallSubtype (m := m) (g := g) (ε := ε) →
        {S : Finset (Domain m) // S.card ≤ budget} :=
    fun f => by
      refine ⟨mismatchSet (m := m) g f.1, ?_⟩
      -- Основная оценка: число рассогласований не превосходит `⌈ε⋅2^m⌉`.
      have hdist : (distU f.1 g : Q)
          ≤ ε * ((Nat.pow 2 m : Nat) : Q) := f.2
      let q : Q := ε * ((Nat.pow 2 m : Nat) : Q)
      have hceil_le : (distU f.1 g : Q) ≤ Int.ceil q :=
        le_trans hdist (by
          have hceil : q ≤ (Int.ceil q : Q) := by
            simpa using (Int.le_ceil (a := q))
          exact hceil)
      have hmul_nonneg : (0 : Q) ≤ q := by
        have hpow_nonneg : (0 : Q) ≤ ((Nat.pow 2 m : Nat) : Q) := by
          exact_mod_cast (Nat.zero_le _)
        exact mul_nonneg hε0 hpow_nonneg
      have hceil_nonneg : (0 : ℤ) ≤ Int.ceil q := by
        have : (0 : Q) ≤ Int.ceil q :=
          le_trans hmul_nonneg (by
            have hceil : q ≤ (Int.ceil q : Q) := by
              simpa using (Int.le_ceil (a := q))
            exact hceil)
        exact_mod_cast this
      have hdist_int : (distU f.1 g : ℤ) ≤ Int.ceil q := by
        exact_mod_cast hceil_le
      have htoNat :
          distU f.1 g ≤ Int.toNat (Int.ceil q) := by
        have hcomp :
            Int.ofNat (distU f.1 g)
              ≤ Int.ofNat (Int.toNat (Int.ceil q)) := by
          simpa [Int.toNat_of_nonneg hceil_nonneg]
            using hdist_int
        exact Int.ofNat_le.mp hcomp
      have hcard := distU_card_mismatch (m := m) (g := g) (f := f.1)
      simpa [budget, hcard] using htoNat
  have h_inj : Function.Injective toSubset := by
    intro f₁ f₂ h
    have hsets :
        mismatchSet (m := m) g f₁.1 = mismatchSet (m := m) g f₂.1 := by
      simpa using congrArg Subtype.val h
    apply Subtype.ext
    have hf₁ := flipOn_mismatchSet (m := m) (g := g) (f := f₁.1)
    have hf₂ := flipOn_mismatchSet (m := m) (g := g) (f := f₂.1)
    calc
      f₁.1 = flipOn g (mismatchSet (m := m) g f₁.1) := by
        exact hf₁.symm
      _ = flipOn g (mismatchSet (m := m) g f₂.1) := by
        simp [hsets]
      _ = f₂.1 := by
        exact hf₂
  have hcard_le :
      Fintype.card (HammingBallSubtype (m := m) (g := g) (ε := ε)) ≤
        Fintype.card {S : Finset (Domain m) // S.card ≤ budget} :=
    Fintype.card_le_of_injective toSubset h_inj
  have cardDomain : Fintype.card (Domain m) = Nat.pow 2 m := by
    classical
    simp [Domain, Core.BitVec, Fintype.card_bool, Fintype.card_fin]
  have hbound :
      Fintype.card {S : Finset (Domain m) // S.card ≤ budget}
        = unionBound (Nat.pow 2 m) budget := by
    simpa [cardDomain] using
      (card_subsets_le_unionBound (α := Domain m) (k := budget))
  have hcap :
      unionBound (Nat.pow 2 m) budget
        = hammingBallBound (Nat.pow 2 m) ε hε0 hε1 := rfl
  simpa [hbound, hcap]
    using hcard_le

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
  Семейство функций, которые совпадают с некоторым объединением подкубов
  на всех точках вне тестового набора `T`.  На самих точках `T` поведение
  допускается произвольное.
-/
def ApproxOnTestset
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m)) :
    Set (Domain m → Bool) :=
  { f | ∃ g, g ∈ UnionClass R k ∧ mismatchSet (m := m) g f ⊆ T }

/-- Полезный синоним для подтипа функций, удовлетворяющих условию тест-набора. -/
abbrev ApproxOnTestsetSubtype
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m)) :=
  {f : Domain m → Bool // f ∈ ApproxOnTestset (R := R) (k := k) (T := T)}

noncomputable instance instFintypeApproxOnTestsetSubtype
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m)) :
    Fintype (ApproxOnTestsetSubtype (R := R) (k := k) (T := T)) := by
  classical
  infer_instance

/--
  Отображение, сопоставляющее функции из `ApproxOnTestsetSubtype` их
  каноническому свидетелю: выбранному объединению и множеству точек, где
  функция отличается от объединения.  Множество всегда лежит внутри `T`.
-/
noncomputable def approxOnTestsetWitness
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m)) :
    ApproxOnTestsetSubtype (R := R) (k := k) (T := T) →
      Σ _g : UnionSubtype (R := R) (k := k),
        {S : Finset (Domain m) // S ⊆ T} :=
  by
    intro f
    classical
    rcases f with ⟨fFun, hf⟩
    let g := Classical.choose hf
    have hWitness := Classical.choose_spec hf
    have hgUnion : g ∈ UnionClass R k := hWitness.1
    have hsubset : mismatchSet (m := m) g fFun ⊆ T := hWitness.2
    refine ⟨⟨g, hgUnion⟩, ⟨mismatchSet (m := m) g fFun, hsubset⟩⟩

lemma approxOnTestsetWitness_injective
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m)) :
    Function.Injective
      (approxOnTestsetWitness (R := R) (k := k) (T := T)) :=
  by
    intro f₁ f₂ hEq
    classical
    cases' f₁ with f₁ h₁
    cases' f₂ with f₂ h₂
    dsimp [approxOnTestsetWitness] at hEq
    have hgEq := congrArg Sigma.fst hEq
    have hsubsetEq := congrArg Sigma.snd hEq
    set g₁ := Classical.choose h₁
    set g₂ := Classical.choose h₂
    have hggRaw := congrArg Subtype.val hgEq
    have hgg : g₁ = g₂ := by
      have htmp := hggRaw
      simp at htmp
      exact htmp
    have hsetRaw := congrArg Subtype.val hsubsetEq
    have hset' :
        mismatchSet (m := m) g₁ f₁ = mismatchSet (m := m) g₂ f₂ := by
      have htmp := hsetRaw
      simp at htmp
      exact htmp
    apply Subtype.ext
    have hf₁ := flipOn_mismatchSet (m := m) g₁ f₁
    have hf₂ := flipOn_mismatchSet (m := m) g₂ f₂
    have step₁ :
        f₁ = flipOn g₁ (mismatchSet (m := m) g₁ f₁) := hf₁.symm
    have step₂a :
        flipOn g₁ (mismatchSet (m := m) g₁ f₁) =
          flipOn g₁ (mismatchSet (m := m) g₂ f₂) :=
      congrArg (fun S => flipOn g₁ S) hset'
    have step₂b :
        flipOn g₁ (mismatchSet (m := m) g₂ f₂) =
          flipOn g₂ (mismatchSet (m := m) g₂ f₂) :=
      by
        have htmp := congrArg
            (fun g => flipOn g (mismatchSet (m := m) g₂ f₂)) hgg
        exact htmp
    have step₃ : flipOn g₂ (mismatchSet (m := m) g₂ f₂) = f₂ := hf₂
    exact step₁.trans (step₂a.trans (step₂b.trans step₃))

lemma approxOnTestset_card_le
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m)) :
    Fintype.card
        (ApproxOnTestsetSubtype (R := R) (k := k) (T := T))
      ≤ unionBound (dictLen R) k * 2 ^ T.card :=
  by
    classical
    have h_inj :=
      (Fintype.card_le_of_injective
        (approxOnTestsetWitness (R := R) (k := k) (T := T))
        (approxOnTestsetWitness_injective (R := R) (k := k) (T := T)))
    have h_sigma_card :
        Fintype.card
            (Σ g : UnionSubtype (R := R) (k := k),
              {S : Finset (Domain m) // S ⊆ T})
          =
            Fintype.card (UnionSubtype (R := R) (k := k)) *
              Fintype.card {S : Finset (Domain m) // S ⊆ T} := by
      have hcongr :=
        (Fintype.card_congr
          (sigmaConstEquiv
            (UnionSubtype (R := R) (k := k))
            ({S : Finset (Domain m) // S ⊆ T})))
      have hprod :=
        (Fintype.card_prod (UnionSubtype (R := R) (k := k))
          ({S : Finset (Domain m) // S ⊆ T}))
      exact Eq.trans hcongr hprod
    have h_subsets := subsetsSubtype_card_eq_pow (T := T)
    have hpow :
        Fintype.card (UnionSubtype (R := R) (k := k)) * 2 ^ T.card ≤
          unionBound (dictLen R) k * 2 ^ T.card :=
      Nat.mul_le_mul_right (2 ^ T.card)
        (unionClass_card_bound (R := R) (k := k))
    have h_sigma_pow_eq :
        Fintype.card
            (Σ g : UnionSubtype (R := R) (k := k),
              {S : Finset (Domain m) // S ⊆ T})
          = Fintype.card (UnionSubtype (R := R) (k := k)) * 2 ^ T.card := by
      have hprodEq :=
        congrArg
          (fun n => Fintype.card (UnionSubtype (R := R) (k := k)) * n)
          h_subsets
      exact Eq.trans h_sigma_card hprodEq
    have h_sigma_pow :
        Fintype.card
            (Σ g : UnionSubtype (R := R) (k := k),
              {S : Finset (Domain m) // S ⊆ T})
          ≤ unionBound (dictLen R) k * 2 ^ T.card :=
      h_sigma_pow_eq.symm ▸ hpow
    exact h_inj.trans h_sigma_pow

lemma approxOnTestset_subset_card_le
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m))
    (Y : Finset (Domain m → Bool))
    (hY : ∀ f ∈ Y, f ∈ ApproxOnTestset (R := R) (k := k) (T := T)) :
    Y.card ≤ unionBound (dictLen R) k * 2 ^ T.card :=
  by
    classical
    let embed : {f // f ∈ Y} →
        ApproxOnTestsetSubtype (R := R) (k := k) (T := T) :=
      fun f => ⟨f.1, hY f.1 f.2⟩
    have hinj : Function.Injective embed := by
      intro f₁ f₂ hEq
      apply Subtype.ext
      have := congrArg Subtype.val hEq
      exact this
    have h_card_coe : Fintype.card {f // f ∈ Y} = Y.card :=
      Fintype.card_coe (s := Y)
    have h_le_sub :
        Y.card ≤
          Fintype.card
            (ApproxOnTestsetSubtype (R := R) (k := k) (T := T)) := by
      have hcard := Fintype.card_le_of_injective embed hinj
      have hcard' := hcard
      rw [h_card_coe] at hcard'
      exact hcard'
    have hcap := approxOnTestset_card_le (R := R) (k := k) (T := T)
    exact h_le_sub.trans hcap

theorem incompatibility_on_testset
    {m : Nat} (R : List (Subcube m)) (k : Nat)
    (T : Finset (Domain m))
    (Y : Finset (Domain m → Bool))
    (hY : ∀ f ∈ Y, f ∈ ApproxOnTestset (R := R) (k := k) (T := T))
    (hLarge : unionBound (dictLen R) k * 2 ^ T.card < Y.card) : False :=
  by
    have h_le :=
      approxOnTestset_subset_card_le (R := R) (k := k) (T := T)
        (Y := Y) hY
    have hcontr := Nat.lt_of_le_of_lt h_le hLarge
    exact Nat.lt_irrefl _ hcontr

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
  simpa [hR] using h

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
  Явная численная форма границы: использует доказанные выше оценки
  `unionBound_le_pow_mul` и `capacityBound_le_pow_mul`.  Такая версия
  удобна при автоматическом поиске контрпримеров — все параметры выражены
  через чисто арифметические функции от `D`, `k` и размера пространства `m`.
-/
lemma approxClass_card_le_explicit
  {m D : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
  (hR : dictLen R = D)
  (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2) :
  Nat.card (ApproxSubtype (R := R) (k := k) (ε := ε)) ≤
    (k.succ) * (Nat.max 1 D) ^ k * 2 ^ (Nat.pow 2 m) :=
by
  have hcap := approxClass_card_le_capacity
    (R := R) (k := k) (ε := ε) (hR := hR) hε0 hε1
  have hexp := capacityBound_le_pow_mul
    (D := D) (k := k) (N := Nat.pow 2 m) (ε := ε) hε0 hε1
  exact Nat.le_trans hcap hexp

/--
  Если все элементы конечного множества `Y` лежат в `ApproxClass`, то его
  мощность не превосходит ёмкости словаря.  Это чисто счётный вариант леммы
  `family_card_le_capacity`, применимый до упаковки данных в сценарий SAL.
  Он понадобится античекеру, чтобы немедленно получить противоречие из
  предположения о «слишком большом» семействе входов.
-/
theorem approx_subset_card_le_capacity
    {m D : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
    (hR : dictLen R = D)
    (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2)
    (Y : Finset (Domain m → Bool))
    (hY : ∀ f ∈ Y, f ∈ ApproxClass (R := R) (k := k) (ε := ε)) :
    Y.card ≤ capacityBound D k (Nat.pow 2 m) ε hε0 hε1 :=
by
  classical
  -- Рассматриваем отображение из элементов множества `Y` в `ApproxSubtype`.
  let embed : {f // f ∈ Y} →
      ApproxSubtype (R := R) (k := k) (ε := ε) := fun f => ⟨f.1, hY f.1 f.2⟩
  have hinj : Function.Injective embed := by
    intro f g hfg
    apply Subtype.ext
    simpa using congrArg Subtype.val hfg
  -- Через мощность `Subtype` переписываем кардинальность `Y`.
  have h_card_coe : Fintype.card {f // f ∈ Y} = Y.card :=
    Fintype.card_coe (s := Y)
  -- Применяем инъективность, чтобы оценить `Y.card` через `ApproxSubtype`.
  have h_le_sub :
      Y.card ≤ Fintype.card (ApproxSubtype (R := R) (k := k) (ε := ε)) := by
    simpa [h_card_coe] using
      (Fintype.card_le_of_injective embed hinj)
  have h_le :
      Y.card ≤ Nat.card (ApproxSubtype (R := R) (k := k) (ε := ε)) := by
    simpa [Nat.card_eq_fintype_card] using h_le_sub
  -- Завершаем, подставляя найденную ранее границу на `ApproxSubtype`.
  have hcap :=
    (approxClass_card_le_capacity (R := R) (k := k) (ε := ε)
      (hR := hR) hε0 hε1)
  exact h_le.trans hcap

/--
  Обобщённый критерий несовместимости: если конечное семейство `Y` содержит
  только ε-аппроксимируемые функции, но его мощность превышает ёмкость, то
  такое семейство существовать не может.  Этого результата достаточно, чтобы
  этап C немедленно получал противоречие от любого «малого» решателя.
-/
theorem incompatibility
    {m D : Nat} (R : List (Subcube m)) (k : Nat) (ε : Q)
    (hR : dictLen R = D)
    (hε0 : (0 : Q) ≤ ε) (hε1 : ε ≤ (1 : Q) / 2)
    (Y : Finset (Domain m → Bool))
    (hY : ∀ f ∈ Y, f ∈ ApproxClass (R := R) (k := k) (ε := ε))
    (hLarge : capacityBound D k (Nat.pow 2 m) ε hε0 hε1 < Y.card) : False :=
by
  have h_le := approx_subset_card_le_capacity (R := R) (k := k) (ε := ε)
      (hR := hR) hε0 hε1 Y hY
  have hcontr := Nat.lt_of_le_of_lt h_le hLarge
  exact (Nat.lt_irrefl _ hcontr)

end Counting
end Pnp3
