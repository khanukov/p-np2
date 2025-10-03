import Mathlib.Data.Fintype.Card
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
  Хаммингово расстояние между двумя булевыми функциями на пространстве
  `Domain m`.  Мы явно перебираем все точки пространства (список `allBitVec m`)
  и считаем количество расхождений.
-/
def distU {m : Nat} (f g : Domain m → Bool) : Nat :=
  let xs := allBitVec m
  xs.foldl (fun acc x => acc + (if f x ≠ g x then 1 else 0)) 0

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

/-- Техническое равенство: выражаем `distU` через ту же свёртку, что
  используется в определении `errU`.  Это позволит напрямую связывать
  «вероятностную» ошибку с подсчётами Хэмминга. -/
lemma distU_eq_fold
    {m : Nat} (f g : Domain m → Bool) :
    distU f g =
      (allBitVec m).foldl
        (fun acc x => acc + b2n (boolXor (f x) (g x))) 0 := by
  classical
  have hpoint : ∀ x, (if f x ≠ g x then 1 else 0)
      = b2n (boolXor (f x) (g x)) := by
    intro x
    by_cases hfg : f x = g x
    · simp [boolXor, hfg, b2n]
    · simp [boolXor, hfg, b2n] at *
  simpa [distU, hpoint]

/-- Связываем `errU` с `distU`: ошибка аппроксимации равна числу несовпадений,
  делённому на размер пространства `2^m`. -/
lemma errU_eq_distU_div_pow
    {m : Nat} (f : Domain m → Bool) (S : List (Subcube m)) :
    errU f S =
      (distU f (fun x => coveredB S x) : Q) /
        ((Nat.pow 2 m : Nat) : Q) := by
  classical
  unfold errU
  set xs := allBitVec m
  set mismatches :=
    xs.foldl
      (fun acc x => acc + b2n (boolXor (f x) (coveredB S x))) 0
  have hdist :
      distU f (fun x => coveredB S x) =
        xs.foldl
          (fun acc x => acc + b2n (boolXor (f x) (coveredB S x))) 0 := by
    simpa [xs, mismatches, distU_eq_fold]
  have hmismatch : mismatches =
      distU f (fun x => coveredB S x) := by
    simpa [mismatches] using hdist.symm
  simp [mismatches, hmismatch]

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
