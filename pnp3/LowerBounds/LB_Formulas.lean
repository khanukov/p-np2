import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Core.Atlas
import Core.BooleanBasics
import Core.SAL_Core
import Counting.Atlas_to_LB_Core
import Counting.Count_EasyFuncs
import ThirdPartyFacts.LeafBudget
import ThirdPartyFacts.Facts_Switching

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
  ### От общего PDT к сценарию ограниченного атласа

  В практических применениях SAL (и родственных конструкций) мы часто получаем
  не только готовый атлас, но и общий частичный решающий дерево `CommonPDT`.  Это
  более гибкий интерфейс по сравнению с голым `Shrinkage`: он содержит дерево,
  допускающее совместное использование листьев несколькими функциями, и явно
  хранит списки листьев для каждой функции.  Следующая конструкция преобразует
  такие данные в `BoundedAtlasScenario`, если известна граница `k` на длину
  очищенных (`dedup`) списков селекторов.
-/
noncomputable def BoundedAtlasScenario.ofCommonPDT
    {n : Nat}
    {F : Core.Family n}
    (C : Core.CommonPDT n F) (k : Nat)
    (hlen : ∀ f ∈ F, ((C.selectors f).dedup).length ≤ k)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    BoundedAtlasScenario n :=
  by
    classical
    refine
      { atlas := C.toAtlas
        family := F
        k := k
        hε0 := hε0
        hε1 := hε1
        works := C.worksFor
        bounded := by
          intro f hf
          refine ⟨(C.selectors f).dedup, hlen f hf, ?_, ?_⟩
          ·
            have hsubset_mem :
                ∀ β : Subcube n,
                  β ∈ (C.selectors f).dedup → β ∈ C.toAtlas.dict := by
              intro β hβ
              have hsel : β ∈ C.selectors f := List.mem_dedup.mp hβ
              have hleaf : β ∈ Core.PDT.leaves C.tree :=
                C.selectors_sub (F := F) (f := f) (β := β) hf hsel
              simpa [Core.CommonPDT.toAtlas, Core.Atlas.ofPDT] using hleaf
            exact
              ((Core.listSubset_iff_mem
                    (xs := (C.selectors f).dedup)
                    (ys := C.toAtlas.dict)).2)
                hsubset_mem
          ·
            simpa using
              (ThirdPartyFacts.err_le_of_dedup_commonPDT
                (n := n) (F := F) (C := C) (f := f) hf) }

noncomputable def BoundedAtlasScenario.ofShrinkage
    {n : Nat}
    (S : Core.Shrinkage n) (k : Nat)
    (hlen : ∀ f ∈ S.F, ((S.Rsel f).dedup).length ≤ k)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    BoundedAtlasScenario n :=
  by
    classical
    refine BoundedAtlasScenario.ofCommonPDT (C := S.commonPDT) k ?hlen ?hε0 ?hε1
    · intro f hf
      simpa [Core.Shrinkage.commonPDT_selectors] using hlen f hf
    · simpa [Core.Shrinkage.commonPDT_epsilon] using hε0
    · simpa [Core.Shrinkage.commonPDT_epsilon] using hε1

/-
  ### От shrinkage к сценарию ограниченного атласа

  Специализация предыдущего шага: SAL обычно возвращает `Shrinkage`, который можно
  рассматривать как частный случай `CommonPDT`.  Поэтому дальнейшие конструкции
  могут работать с общим интерфейсом, а `ofShrinkage` лишь аккуратно упаковывает
  преобразование.
-/

/--
  Общий вариант построения ограниченного сценария по данному `CommonPDT`.
  Используем внешнюю оценку `leaf_budget_from_commonPDT`, чтобы выбрать
  подходящее число `k` листьев, после чего применяем `ofCommonPDT`.
-/
noncomputable def scenarioFromCommonPDT
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    Σ' _ : Nat, BoundedAtlasScenario n :=
  by
    classical
    let witness :=
      ThirdPartyFacts.leaf_budget_from_commonPDT (n := n) (F := F) (C := C)
    let k := Classical.choose witness
    have hkSpec := Classical.choose_spec witness
    have hlen : ∀ f ∈ F, ((C.selectors f).dedup).length ≤ k := by
      intro f hf
      have hkLen := hkSpec.2 hf
      simpa using hkLen
    exact ⟨k, BoundedAtlasScenario.ofCommonPDT (C := C) k hlen hε0 hε1⟩

/--
  Полезная граница на параметр `k`, возвращаемый конструкцией
  `scenarioFromCommonPDT`.  Он не превышает `2^{depthBound}` — число, которое
  ограничивает количество листьев исходного PDT.  Именно это значение
  появляется в дальнейших оценках ёмкости.
-/
lemma scenarioFromCommonPDT_k_le_pow
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    (scenarioFromCommonPDT (n := n) (F := F) (C := C) hε0 hε1).1
      ≤ Nat.pow 2 C.depthBound := by
  classical
  -- Теперь определение `scenarioFromCommonPDT` доступно — раскрываем его.
  unfold scenarioFromCommonPDT
  set witness :=
      ThirdPartyFacts.leaf_budget_from_commonPDT
        (n := n) (F := F) (C := C)
    with hwitness
  set k := Classical.choose witness with hk
  change k ≤ Nat.pow 2 C.depthBound
  have hk_spec := Classical.choose_spec witness
  have hk_leaves : k ≤ (Core.PDT.leaves C.tree).length := by
    simpa [hk] using hk_spec.1
  have hlen_bound :
      (Core.PDT.leaves C.tree).length ≤ Nat.pow 2 (Core.PDT.depth C.tree) :=
    Core.leaves_count_bound (t := C.tree)
  have hdepth_bound :
      Nat.pow 2 (Core.PDT.depth C.tree) ≤ Nat.pow 2 C.depthBound :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) C.depth_le
  exact hk_leaves.trans (hlen_bound.trans hdepth_bound)

/--
  Для shrinkage-сертификата полезно знать, что словарь полученного атласа
  не длиннее `2^{t}`, где `t` — заявленная глубина PDT.  Эта оценка напрямую
  следует из стандартной границы на число листьев дерева решений.
-/
lemma dictLen_fromCommonPDT_le_pow
    {n : Nat} {F : Core.Family n} (C : Core.CommonPDT n F) :
    Counting.dictLen C.toAtlas.dict ≤ Nat.pow 2 C.depthBound :=
  by
    classical
    have hLeaves :
        (Core.PDT.leaves C.tree).length ≤ Nat.pow 2 (Core.PDT.depth C.tree) :=
      Core.leaves_count_bound (t := C.tree)
    have hDepth :
        Nat.pow 2 (Core.PDT.depth C.tree) ≤ Nat.pow 2 C.depthBound :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) C.depth_le
    have hDict :
        Counting.dictLen C.toAtlas.dict =
          (Core.PDT.leaves C.tree).length := rfl
    exact (hDict ▸ hLeaves).trans hDepth

/--
  Специализация предыдущей оценки на случай shrinkage.  Граница выражается
  через параметр `t`, управляющий глубиной PDT.
-/
lemma dictLen_fromShrinkage_le_pow
    {n : Nat} (S : Core.Shrinkage n) :
    Counting.dictLen (Core.Atlas.fromShrinkage S).dict ≤ Nat.pow 2 S.t :=
  by
    classical
    have :=
      dictLen_fromCommonPDT_le_pow
        (n := n) (F := S.F) (C := S.commonPDT)
    simpa [Core.Atlas.fromShrinkage, Core.Atlas.ofPDT,
      Core.CommonPDT.toAtlas, Core.Shrinkage.commonPDT_depthBound,
      Core.Shrinkage.commonPDT_tree]
      using this

/-- У `scenarioFromCommonPDT` семейство во втором компоненте равно исходному `F`. -/
@[simp]
lemma scenarioFromCommonPDT_family
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    (scenarioFromCommonPDT (n := n) (F := F) (C := C) hε0 hε1).2.family = F := by
  rfl

@[simp]
lemma scenarioFromCommonPDT_epsilon
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    (scenarioFromCommonPDT (n := n) (F := F) (C := C) hε0 hε1).2.atlas.epsilon =
      C.epsilon := by
  rfl

lemma scenarioFromCommonPDT_dictLen_le_pow
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    Counting.dictLen
        (scenarioFromCommonPDT (n := n) (F := F) (C := C) hε0 hε1).2.atlas.dict
      ≤ Nat.pow 2 C.depthBound := by
  classical
  have hbound := dictLen_fromCommonPDT_le_pow (n := n) (F := F) (C := C)
  -- В полученном сценарии атлас совпадает с `C.toAtlas`, поэтому оценка
  -- на длину словаря переносится напрямую.
  simpa [scenarioFromCommonPDT, BoundedAtlasScenario.ofCommonPDT,
    Core.CommonPDT.toAtlas]
    using hbound

/--
  Версия критерия несовместимости, заточенная под shrinkage: если для
  построенного из него сценария существует большое подсемейство функций,
  то получить такой shrinkage невозможно.
-/
theorem no_commonPDT_of_large_family
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F) (k : Nat)
    (hlen : ∀ f ∈ F, ((C.selectors f).dedup).length ≤ k)
    (hε0 : (0 : Core.Q) ≤ C.epsilon) (hε1 : C.epsilon ≤ (1 : Core.Q) / 2)
    (Y : Finset (Core.BitVec n → Bool))
    (hYsubset :
      Y ⊆ familyFinset (sc := BoundedAtlasScenario.ofCommonPDT (C := C) k hlen hε0 hε1))
    (hLarge :
      scenarioCapacity
          (sc := BoundedAtlasScenario.ofCommonPDT (C := C) k hlen hε0 hε1) < Y.card) :
    False :=
  by
    classical
    exact
      no_bounded_atlas_of_large_family
        (sc := BoundedAtlasScenario.ofCommonPDT (C := C) k hlen hε0 hε1)
        (Y := Y) hYsubset hLarge

/--
  Версия критерия для shrinkage-сертификата.  Следует из общей формы, применённой
  к `S.commonPDT`.
-/
theorem no_shrinkage_of_large_family
    {n : Nat} (S : Core.Shrinkage n) (k : Nat)
    (hlen : ∀ f ∈ S.F, ((S.Rsel f).dedup).length ≤ k)
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
    have hsubset' :
        Y ⊆
          familyFinset
            (sc := BoundedAtlasScenario.ofCommonPDT
              (C := S.commonPDT) k
              (hlen := by
                intro f hf
                simpa [Core.Shrinkage.commonPDT_selectors] using hlen f hf)
              (hε0 := by
                simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
              (hε1 := by
                simpa [Core.Shrinkage.commonPDT_epsilon] using hε1)) :=
      by
        simpa using hYsubset
    have hLarge' :
        scenarioCapacity
            (sc := BoundedAtlasScenario.ofCommonPDT
              (C := S.commonPDT) k
              (hlen := by
                intro f hf
                simpa [Core.Shrinkage.commonPDT_selectors] using hlen f hf)
              (hε0 := by
                simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
              (hε1 := by
                simpa [Core.Shrinkage.commonPDT_epsilon] using hε1))
          < Y.card :=
      by
        simpa using hLarge
    exact
      no_commonPDT_of_large_family
        (C := S.commonPDT) (k := k)
        (hlen := by
          intro f hf
          simpa [Core.Shrinkage.commonPDT_selectors] using hlen f hf)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε1)
        (Y := Y)
        hsubset' hLarge'

/--
  ### Автоматический переход от Shrinkage к ограниченному сценарию

  Комбинируем SAL и внешний факт о бюджете листьев (теперь сформулированный на
  уровне `CommonPDT`), получая готовый объект `BoundedAtlasScenario` и общую
  границу `k`.  Это базовый клей между частями A и B: дальше можно напрямую
  применять Covering-Power.
-/
noncomputable def scenarioFromShrinkage
    {n : Nat}
    (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    Σ' _ : Nat, BoundedAtlasScenario n :=
  by
    classical
    exact
      scenarioFromCommonPDT
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε1)

/--
  Специализация к случаю AC⁰: из shrinkage-конструкции, предоставленной
  внешним фактом, автоматически получаем ограниченный сценарий.  Лемма
  также заботится об условиях `0 ≤ ε ≤ 1/2`, необходимых для применения
  ёмкостных оценок.
-/
noncomputable def scenarioFromAC0
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n) :
    Σ' _ : Nat, BoundedAtlasScenario params.n :=
  by
    classical
    let shrinkWitness := ThirdPartyFacts.shrinkage_for_AC0 params F
    let t := Classical.choose shrinkWitness
    let rest₁ := Classical.choose_spec shrinkWitness
    let ε := Classical.choose rest₁
    let rest₂ := Classical.choose_spec rest₁
    let S := Classical.choose rest₂
    have hspec := Classical.choose_spec rest₂
    have hF : S.F = F := hspec.1
    have hchain := hspec.2
    have ht : S.t = t := hchain.1
    have hchain' := hchain.2
    have hε : S.ε = ε := hchain'.1
    have hchain'' := hchain'.2
    have htBound : t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := hchain''.1
    have hchain''' := hchain''.2
    have hε0 : (0 : Core.Q) ≤ ε := hchain'''.1
    have hεBound : ε ≤ (1 : Core.Q) / (params.n + 2) := hchain'''.2
    let hε' : ε = S.ε := hε.symm
    have hε_le_half_base :=
      ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := ε) hεBound
    have hε_le_half : S.ε ≤ (1 : Core.Q) / 2 := hε' ▸ hε_le_half_base
    have hε_nonneg : (0 : Core.Q) ≤ S.ε := hε' ▸ hε0
    let base :=
      scenarioFromCommonPDT
        (n := params.n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε_nonneg)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε_le_half)
    have base_family : base.2.family = S.F := by
      simp [base, scenarioFromCommonPDT, BoundedAtlasScenario.ofCommonPDT]
    refine ⟨base.1, { base.2 with family := F, works := ?_, bounded := ?_ }⟩
    ·
      have hworksBase : WorksFor base.2.atlas S.F := by
        simpa [base_family] using base.2.works
      exact hF ▸ hworksBase
    · intro f hf
      have hfS : f ∈ S.F := hF ▸ hf
      have hfBase : f ∈ base.2.family := by
        simpa [base_family] using hfS
      have hbounded := base.2.bounded f hfBase
      simpa [base_family] using hbounded

/-- Семейство функций в сценарии, построенном из факта `AC⁰ → shrinkage`,
  совпадает с исходным списком `F`.  Это удобное переписывание для дальнейших
  аргументов о подсемействах и мощностях. -/
@[simp]
lemma scenarioFromAC0_family_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n) :
    (scenarioFromAC0 params F).2.family = F := by
  classical
  unfold scenarioFromAC0
  set shrinkWitness := ThirdPartyFacts.shrinkage_for_AC0 params F
  set t := Classical.choose shrinkWitness
  set rest₁ := Classical.choose_spec shrinkWitness
  set ε := Classical.choose rest₁
  set rest₂ := Classical.choose_spec rest₁
  set S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  rcases hspec with ⟨hF, hchain⟩
  rcases hchain with ⟨ht, hchain⟩
  rcases hchain with ⟨hε, hchain⟩
  rcases hchain with ⟨htBound, hchain⟩
  rcases hchain with ⟨hε0, hεBound⟩
  simp

/--
  Аналог конструкции `scenarioFromAC0`, но для shrinkage факта о
  локальных схемах.  Логика полностью идентична: извлекаем общий PDT,
  приводим ошибку к формату SAL и упаковываем в ограниченный сценарий.
-/
noncomputable def scenarioFromLocalCircuit
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n) :
    Σ' _ : Nat, BoundedAtlasScenario params.n :=
  by
    classical
    let shrinkWitness := ThirdPartyFacts.shrinkage_for_localCircuit params F
    let t := Classical.choose shrinkWitness
    let rest₁ := Classical.choose_spec shrinkWitness
    let ε := Classical.choose rest₁
    let rest₂ := Classical.choose_spec rest₁
    let S := Classical.choose rest₂
    have hspec := Classical.choose_spec rest₂
    have hF : S.F = F := hspec.1
    have hchain := hspec.2
    have ht : S.t = t := hchain.1
    have hchain' := hchain.2
    have hε : S.ε = ε := hchain'.1
    have hchain'' := hchain'.2
    have htBound : t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) := hchain''.1
    have hchain''' := hchain''.2
    have hε0 : (0 : Core.Q) ≤ ε := hchain'''.1
    have hεBound : ε ≤ (1 : Core.Q) / (params.n + 2) := hchain'''.2
    let hε' : ε = S.ε := hε.symm
    have hε_le_half_base :=
      ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := ε) hεBound
    have hε_le_half : S.ε ≤ (1 : Core.Q) / 2 := hε' ▸ hε_le_half_base
    have hε_nonneg : (0 : Core.Q) ≤ S.ε := hε' ▸ hε0
    let base :=
      scenarioFromCommonPDT
        (n := params.n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε_nonneg)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε_le_half)
    have base_family : base.2.family = S.F := by
      simp [base, scenarioFromCommonPDT, BoundedAtlasScenario.ofCommonPDT]
    refine ⟨base.1, { base.2 with family := F, works := ?_, bounded := ?_ }⟩
    ·
      have hworksBase : WorksFor base.2.atlas S.F := by
        simpa [base_family] using base.2.works
      exact hF ▸ hworksBase
    · intro f hf
      have hfS : f ∈ S.F := hF ▸ hf
      have hfBase : f ∈ base.2.family := by
        simpa [base_family] using hfS
      have hbounded := base.2.bounded f hfBase
      simpa [base_family] using hbounded

/-- Семейство в сценарии для локальных схем совпадает с исходным списком `F`. -/
@[simp]
lemma scenarioFromLocalCircuit_family_eq
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n) :
    (scenarioFromLocalCircuit params F).2.family = F := by
  classical
  unfold scenarioFromLocalCircuit
  set shrinkWitness := ThirdPartyFacts.shrinkage_for_localCircuit params F
  set t := Classical.choose shrinkWitness
  set rest₁ := Classical.choose_spec shrinkWitness
  set ε := Classical.choose rest₁
  set rest₂ := Classical.choose_spec rest₁
  set S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  rcases hspec with ⟨hF, hchain⟩
  rcases hchain with ⟨ht, hchain⟩
  rcases hchain with ⟨hε, hchain⟩
  rcases hchain with ⟨htBound, hchain⟩
  rcases hchain with ⟨hε0, hεBound⟩
  simp

/--
  Для сценария, построенного из shrinkage, параметр `k` не превышает числа
  листьев PDT, то есть `2^{t}`.  Это прямое следствие определения
  `scenarioFromShrinkage` через `scenarioFromCommonPDT`.
-/
lemma scenarioFromShrinkage_k_le_pow
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    (scenarioFromShrinkage (n := n) S hε0 hε1).1 ≤ Nat.pow 2 S.t := by
  classical
  simpa [scenarioFromShrinkage, Core.Shrinkage.commonPDT_depthBound,
    Core.Shrinkage.commonPDT_epsilon]
    using
      scenarioFromCommonPDT_k_le_pow
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε1)

/--
  Аналогичная оценка для длины словаря: `scenarioFromShrinkage` наследует
  границу `|dict| ≤ 2^{t}` от общего PDT.
-/
lemma scenarioFromShrinkage_dictLen_le_pow
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    Counting.dictLen
        (scenarioFromShrinkage (n := n) S hε0 hε1).2.atlas.dict
      ≤ Nat.pow 2 S.t := by
  classical
  simpa [scenarioFromShrinkage, Core.Shrinkage.commonPDT_depthBound,
    Core.Shrinkage.commonPDT_epsilon]
    using
      scenarioFromCommonPDT_dictLen_le_pow
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε1)

@[simp]
lemma scenarioFromShrinkage_family_eq
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    (scenarioFromShrinkage (n := n) S hε0 hε1).2.family = S.F := by
  classical
  simpa [scenarioFromShrinkage]
    using
      (scenarioFromCommonPDT_family
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε1))

@[simp]
lemma scenarioFromShrinkage_epsilon_eq
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    (scenarioFromShrinkage (n := n) S hε0 hε1).2.atlas.epsilon = S.ε := by
  classical
  simpa [scenarioFromShrinkage]
    using
      (scenarioFromCommonPDT_epsilon
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε0)
        (hε1 := by
          simpa [Core.Shrinkage.commonPDT_epsilon] using hε1))

/--
  Параметр `k` в сценарии AC⁰ не превышает `2^{(log₂(M+2))^{d+1}}`.  Получаем
  его из границы `t ≤ (log₂(M+2))^{d+1}`, предоставленной внешним фактом.
-/
lemma scenarioFromAC0_k_le_pow
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n) :
    (scenarioFromAC0 params F).1
      ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
  classical
  unfold scenarioFromAC0
  set shrinkWitness := ThirdPartyFacts.shrinkage_for_AC0 params F with hwit
  let t := Classical.choose shrinkWitness
  set rest₁ := Classical.choose_spec shrinkWitness with hrest₁
  let ε := Classical.choose rest₁
  set rest₂ := Classical.choose_spec rest₁ with hrest₂
  let S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  rcases hspec with ⟨hF, hchain⟩
  rcases hchain with ⟨ht_eq, hchain⟩
  rcases hchain with ⟨hε_eq, hchain⟩
  rcases hchain with ⟨htBound, hchain⟩
  rcases hchain with ⟨hε0, hεBound⟩
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := by
    simpa using (hε_eq ▸ hε0)
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    (hε_eq ▸
      ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := ε) hεBound)
  have hk_base :=
    scenarioFromShrinkage_k_le_pow
      (n := params.n) (S := S)
      (hε0 := hε_nonneg)
      (hε1 := hε_half)
  have hbound_pow :
      Nat.pow 2 S.t ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
    have : S.t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
      simpa using (ht_eq.symm ▸ htBound)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) this
  exact hk_base.trans hbound_pow

/--
  Оценка на длину словаря в AC⁰-сценарии: она не превосходит того же `2^{(log₂(M+2))^{d+1}}`.
-/
lemma scenarioFromAC0_dictLen_le_pow
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n) :
    Counting.dictLen (scenarioFromAC0 params F).2.atlas.dict
      ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
  classical
  unfold scenarioFromAC0
  set shrinkWitness := ThirdPartyFacts.shrinkage_for_AC0 params F with hwit
  let t := Classical.choose shrinkWitness
  set rest₁ := Classical.choose_spec shrinkWitness with hrest₁
  let ε := Classical.choose rest₁
  set rest₂ := Classical.choose_spec rest₁ with hrest₂
  let S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  rcases hspec with ⟨hF, hchain⟩
  rcases hchain with ⟨ht_eq, hchain⟩
  rcases hchain with ⟨hε_eq, hchain⟩
  rcases hchain with ⟨htBound, hchain⟩
  rcases hchain with ⟨hε0, hεBound⟩
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := by
    simpa using (hε_eq ▸ hε0)
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    (hε_eq ▸
      ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := ε) hεBound)
  have hdict_base :=
    scenarioFromShrinkage_dictLen_le_pow
      (n := params.n) (S := S)
      (hε0 := hε_nonneg)
      (hε1 := hε_half)
  have hbound_pow :
      Nat.pow 2 S.t ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
    have : S.t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
      simpa using (ht_eq.symm ▸ htBound)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) this
  exact hdict_base.trans hbound_pow

/--
  Локальные схемы дают аналогичную границу: `k ≤ 2^{ℓ · (log₂(M+2) + depth + 1)}`.
-/
lemma scenarioFromLocalCircuit_k_le_pow
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n) :
    (scenarioFromLocalCircuit params F).1
      ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
  classical
  unfold scenarioFromLocalCircuit
  set shrinkWitness := ThirdPartyFacts.shrinkage_for_localCircuit params F with hwit
  let t := Classical.choose shrinkWitness
  set rest₁ := Classical.choose_spec shrinkWitness with hrest₁
  let ε := Classical.choose rest₁
  set rest₂ := Classical.choose_spec rest₁ with hrest₂
  let S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  rcases hspec with ⟨hF, hchain⟩
  rcases hchain with ⟨ht_eq, hchain⟩
  rcases hchain with ⟨hε_eq, hchain⟩
  rcases hchain with ⟨htBound, hchain⟩
  rcases hchain with ⟨hε0, hεBound⟩
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := by
    simpa using (hε_eq ▸ hε0)
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    (hε_eq ▸
      ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := ε) hεBound)
  have hk_base :=
    scenarioFromShrinkage_k_le_pow
      (n := params.n) (S := S)
      (hε0 := hε_nonneg)
      (hε1 := hε_half)
  have hbound_pow :
      Nat.pow 2 S.t ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
    have : S.t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) := by
      simpa using (ht_eq.symm ▸ htBound)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) this
  exact hk_base.trans hbound_pow

/--
  И для длины словаря в локальных схемах действует та же оценка.
-/
lemma scenarioFromLocalCircuit_dictLen_le_pow
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n) :
    Counting.dictLen (scenarioFromLocalCircuit params F).2.atlas.dict
      ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
  classical
  unfold scenarioFromLocalCircuit
  set shrinkWitness := ThirdPartyFacts.shrinkage_for_localCircuit params F with hwit
  let t := Classical.choose shrinkWitness
  set rest₁ := Classical.choose_spec shrinkWitness with hrest₁
  let ε := Classical.choose rest₁
  set rest₂ := Classical.choose_spec rest₁ with hrest₂
  let S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  rcases hspec with ⟨hF, hchain⟩
  rcases hchain with ⟨ht_eq, hchain⟩
  rcases hchain with ⟨hε_eq, hchain⟩
  rcases hchain with ⟨htBound, hchain⟩
  rcases hchain with ⟨hε0, hεBound⟩
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := by
    simpa using (hε_eq ▸ hε0)
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    (hε_eq ▸
      ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := ε) hεBound)
  have hdict_base :=
    scenarioFromShrinkage_dictLen_le_pow
      (n := params.n) (S := S)
      (hε0 := hε_nonneg)
      (hε1 := hε_half)
  have hbound_pow :
      Nat.pow 2 S.t ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
    have : S.t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) := by
      simpa using (ht_eq.symm ▸ htBound)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) this
  exact hdict_base.trans hbound_pow

-- Дополнительные оценки будут добавлены ниже при необходимости.
end LowerBounds
end Pnp3
