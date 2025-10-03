import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Core.Atlas
import Core.BooleanBasics
import Core.SAL_Core
import Counting.Atlas_to_LB_Core
import Counting.Count_EasyFuncs

/-!
  pnp3/LowerBounds/LB_Formulas.lean

  Этот файл реализует «мостик» между общими оценками ёмкости
  (из `Counting/Atlas_to_LB_Core.lean`) и будущими нижними оценками
  на формулы.  Мы формализуем сценарий, когда фиксированный атлас
  аппроксимирует семейство функций выбором не более `k` подкубов с
  ошибкой `ε`, и показываем, что тогда мощность такого семейства
  ограничена ёмкостью словаря.  Избыточные предположения вроде
  `WorksFor` остаются полезными для согласования с SAL, но ключевой
  шаг — перевод этих данных в ограничения на количество функций.

  Конечная цель — применять этот результат в части C: предполагая
  существование маленькой формулы (или схемы), через SAL получаем
  атлас с ограниченными параметрами, что приводит к противоречию с
  большим числом YES-функций.
-/

namespace Pnp3
namespace LowerBounds

open Classical
open Pnp3.Core
open Pnp3.Counting
open Finset

/--
  Сценарий «малого атласа»: словарь `atlas.dict` аппроксимирует
  семейство функций `family`, причём для каждой функции достаточно
  выбрать не более `k` подкубов, а ошибка не превосходит `atlas.epsilon`.
  Дополнительно фиксируем границы на `atlas.epsilon`, чтобы применять
  энтропийные оценки из части B.
-/
structure BoundedAtlasScenario (n : Nat) where
  atlas    : Core.Atlas n
  family   : Core.Family n
  k        : Nat
  hε0      : (0 : Core.Q) ≤ atlas.epsilon
  hε1      : atlas.epsilon ≤ (1 : Core.Q) / 2
  works    : Core.WorksFor atlas family
  bounded  : ∀ f ∈ family,
      ∃ (S : List (Core.Subcube n)),
        S.length ≤ k ∧
          Core.listSubset S atlas.dict ∧
          Core.errU f S ≤ atlas.epsilon

/-- Для удобства переводим список функций в конечное множество. -/
def familyFinset {n : Nat} (sc : BoundedAtlasScenario n) :
    Finset (Core.BitVec n → Bool) :=
  sc.family.toFinset

lemma mem_familyFinset {n : Nat}
    (sc : BoundedAtlasScenario n) (f : Core.BitVec n → Bool) :
    f ∈ familyFinset sc ↔ f ∈ sc.family := by
  classical
  simp [familyFinset]

/-- Свидетельство: элемент семейства даёт точку в `ApproxSubtype`. -/
noncomputable def approxSubtypeOf
    {n : Nat} (sc : BoundedAtlasScenario n) :
    {f // f ∈ familyFinset sc} →
      Counting.ApproxSubtype (R := sc.atlas.dict)
        (k := sc.k) (ε := sc.atlas.epsilon) :=
  by
    classical
    intro f
    have hf_mem : f.1 ∈ sc.family := by
      have hmem := (mem_familyFinset (sc := sc) (f := f.1)).mp f.property
      exact hmem
    have happrox : f.1 ∈ Counting.ApproxClass (R := sc.atlas.dict)
        (k := sc.k) (ε := sc.atlas.epsilon) :=
      approx_mem_of_errU_le
        (R := sc.atlas.dict) (k := sc.k)
        (ε := sc.atlas.epsilon)
        (f := f.1)
        (sc.bounded f.1 hf_mem)
    exact ⟨f.1, happrox⟩

lemma approxSubtypeOf_injective
    {n : Nat} (sc : BoundedAtlasScenario n) :
    Function.Injective (approxSubtypeOf (sc := sc)) := by
  classical
  intro f₁ f₂ h
  have hfun := congrArg Subtype.val h
  apply Subtype.ext
  change f₁.1 = f₂.1
  simpa [approxSubtypeOf] using hfun

/--
  Мощность семейства функций, для которых работает атлас,
  ограничена ёмкостью словаря.
-/
theorem family_card_le_capacity
    {n : Nat} (sc : BoundedAtlasScenario n) :
    (familyFinset sc).card ≤
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k
        (Nat.pow 2 n) sc.atlas.epsilon sc.hε0 sc.hε1 := by
  classical
  have h_inj := Fintype.card_le_of_injective
      (approxSubtypeOf (sc := sc))
      (approxSubtypeOf_injective (sc := sc))
  have h_cover := covering_power_bound
      (R := sc.atlas.dict) (k := sc.k)
      (ε := sc.atlas.epsilon) sc.hε0 sc.hε1
  have hdomain :
      (familyFinset sc).card =
        Fintype.card {f // f ∈ familyFinset sc} := by
    classical
    exact (Fintype.card_coe (familyFinset sc)).symm
  have h_inj' :
      (familyFinset sc).card ≤
        Fintype.card
          (Counting.ApproxSubtype (R := sc.atlas.dict)
            (k := sc.k) (ε := sc.atlas.epsilon)) := by
    classical
    simpa [hdomain.symm]
      using h_inj
  exact Nat.le_trans h_inj' h_cover

/-- Удобная запись величины ёмкости в текущем сценарии. -/
noncomputable def scenarioCapacity {n : Nat} (sc : BoundedAtlasScenario n) : Nat :=
  Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k (Nat.pow 2 n)
    sc.atlas.epsilon sc.hε0 sc.hε1

/--
  Если множество `Y` функций содержится в семействе, обслуживаемом
  атласом, и при этом его размер превышает ёмкость, то получаем
  противоречие.  Именно так в части C будут извлекаться нижние оценки.
-/
theorem no_bounded_atlas_of_large_family
    {n : Nat} (sc : BoundedAtlasScenario n)
    (Y : Finset (Core.BitVec n → Bool))
    (hYsubset : Y ⊆ familyFinset sc)
    (hLarge : scenarioCapacity (sc := sc) < Y.card) : False :=
  by
    classical
    have hY_le_cap : Y.card ≤ scenarioCapacity (sc := sc) := by
      have hYleFamily := Finset.card_le_card hYsubset
      have hFamily := family_card_le_capacity (sc := sc)
      exact Nat.le_trans hYleFamily hFamily
    have hcontr := Nat.lt_of_le_of_lt hY_le_cap hLarge
    exact (Nat.lt_irrefl _ hcontr)

/--
  ### От shrinkage к сценарию ограниченного атласа

  В практических применениях SAL выдаёт «сырой» сертификат вида `Shrinkage`: у нас
  есть PDT небольшой глубины, и для каждой функции из семейства задан набор листьев,
  обеспечивающий малую ошибку.  Чтобы воспользоваться счётными результатами части B,
  удобно упаковать эти данные в `BoundedAtlasScenario`.  Следующая конструкция
  выполняет именно это преобразование, если заранее известна граница `k` на число
  листьев, используемых для каждой функции.
-/
noncomputable def BoundedAtlasScenario.ofShrinkage
    {n : Nat} (S : Core.Shrinkage n) (k : Nat)
    (hlen : ∀ f ∈ S.F, (S.Rsel f).length ≤ k)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    BoundedAtlasScenario n :=
  { atlas := Core.Atlas.fromShrinkage S
    family := S.F
    k := k
    hε0 := hε0
    hε1 := hε1
    works := by
      -- Конструкция SAL непосредственно показывает, что полученный атлас
      -- работает для семейства `S.F`.
      simpa [Core.Atlas.fromShrinkage] using Core.SAL_from_Shrinkage S
    bounded := by
      -- Используем данные shrinkage: список `S.Rsel f` подмножеством словаря,
      -- имеет ограниченную длину и даёт требуемую ошибку.
      intro f hf
      refine ⟨S.Rsel f, ?_, ?_, ?_⟩
      · exact hlen f hf
      · -- Цель переформулируем напрямую через листья PDT, чтобы воспользоваться
        -- условием shrinkage о подмножестве словаря.
        change Core.listSubset (S.Rsel f) (Core.PDT.leaves S.tree)
        simpa using S.Rsel_sub f hf
      · simpa using S.err_le f hf }

/--
  Для shrinkage-сертификата полезно знать, что словарь полученного атласа
  не длиннее `2^{t}`, где `t` — заявленная глубина PDT.  Эта оценка напрямую
  следует из стандартной границы на число листьев дерева решений.
-/
lemma dictLen_fromShrinkage_le_pow
    {n : Nat} (S : Core.Shrinkage n) :
    Counting.dictLen (Core.Atlas.fromShrinkage S).dict ≤ Nat.pow 2 S.t :=
  by
    have hLeaves :
        (Core.PDT.leaves S.tree).length ≤ Nat.pow 2 (Core.PDT.depth S.tree) :=
      Core.leaves_count_bound (t := S.tree)
    have hDepth :
        Nat.pow 2 (Core.PDT.depth S.tree) ≤ Nat.pow 2 S.t :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) S.depth_le
    have hDict :
        Counting.dictLen (Core.Atlas.fromShrinkage S).dict =
          (Core.PDT.leaves S.tree).length := rfl
    exact (hDict ▸ hLeaves).trans hDepth

/--
  Версия критерия несовместимости, заточенная под shrinkage: если для
  построенного из него сценария существует большое подсемейство функций,
  то получить такой shrinkage невозможно.
-/
theorem no_shrinkage_of_large_family
    {n : Nat} (S : Core.Shrinkage n) (k : Nat)
    (hlen : ∀ f ∈ S.F, (S.Rsel f).length ≤ k)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2)
    (Y : Finset (Core.BitVec n → Bool))
    (hYsubset :
      Y ⊆ familyFinset (sc := BoundedAtlasScenario.ofShrinkage S k hlen hε0 hε1))
    (hLarge :
      scenarioCapacity
          (sc := BoundedAtlasScenario.ofShrinkage S k hlen hε0 hε1) < Y.card) :
    False :=
  by
    classical
    -- Применяем общий критерий к специально построенному сценарию.
    exact
      no_bounded_atlas_of_large_family
        (sc := BoundedAtlasScenario.ofShrinkage S k hlen hε0 hε1)
        (Y := Y) hYsubset hLarge


end LowerBounds
end Pnp3
