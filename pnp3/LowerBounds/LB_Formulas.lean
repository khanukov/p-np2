import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Core.Atlas
import Core.BooleanBasics
import Core.SAL_Core
import Core.ShrinkageWitness
import Counting.Atlas_to_LB_Core
import Counting.Count_EasyFuncs
import ThirdPartyFacts.Facts_Switching
import ThirdPartyFacts.LeafBudget

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

noncomputable section

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
  exact hfun

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
    exact (hdomain ▸ h_inj)
  exact Nat.le_trans h_inj' h_cover

/-- Удобная запись величины ёмкости в текущем сценарии. -/
noncomputable def scenarioCapacity {n : Nat} (sc : BoundedAtlasScenario n) : Nat :=
  Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k (Nat.pow 2 n)
    sc.atlas.epsilon sc.hε0 sc.hε1

/--
  Ёмкость для тест-набора: число кандидатных функций, которые можно построить из
  словаря, умноженное на количество способов ошибиться на `T`.  Именно эта величина
  фигурирует в «тестовой» версии Covering-Power.
-/
def testsetCapacity {n : Nat} (sc : BoundedAtlasScenario n)
    (T : Finset (Core.BitVec n)) : Nat :=
  Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k * 2 ^ T.card

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
  Версия критерия с тест-набором: если все функции из `Y` совпадают с объединением
  словаря за пределами `T`, а мощность `Y` превосходит тестовую ёмкость, то атлас
  не может покрыть такое семейство.  Граница `testsetCapacity` напрямую использует
  комбинаторику `ApproxOnTestset` из части B.
-/
theorem no_bounded_atlas_on_testset_of_large_family
    {n : Nat} (sc : BoundedAtlasScenario n)
    (T : Finset (Core.BitVec n))
    (Y : Finset (Core.BitVec n → Bool))
    (_hYsubset : Y ⊆ familyFinset sc)
    (hApprox : ∀ f ∈ Y,
      f ∈ Counting.ApproxOnTestset
        (R := sc.atlas.dict) (k := sc.k) (T := T))
    (hLarge : testsetCapacity (sc := sc) (T := T) < Y.card) : False :=
  by
    classical
    have hBound :=
      Counting.approxOnTestset_subset_card_le
        (R := sc.atlas.dict) (k := sc.k) (T := T) (Y := Y) hApprox
    have hContr := Nat.lt_of_le_of_lt hBound hLarge
    exact Nat.lt_irrefl _ hContr

end

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
              change β ∈ Core.PDT.leaves C.tree
              exact hleaf
            exact
              ((Core.listSubset_iff_mem
                    (xs := (C.selectors f).dedup)
                    (ys := C.toAtlas.dict)).2)
                hsubset_mem
          ·
            have herr :=
              (ThirdPartyFacts.err_le_of_dedup_commonPDT
                (n := n) (F := F) (C := C) (f := f) hf)
            exact herr }

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
      have htmp := hlen f hf
      change ((S.commonPDT.selectors f).dedup).length ≤ k
      dsimp [Core.Shrinkage.commonPDT_selectors]
      exact htmp
    ·
      have htmp := hε0
      change (0 : Core.Q) ≤ S.commonPDT.epsilon
      dsimp [Core.Shrinkage.commonPDT_epsilon]
      exact htmp
    ·
      have htmp := hε1
      change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
      dsimp [Core.Shrinkage.commonPDT_epsilon]
      exact htmp

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
      exact hkSpec.2 hf
    exact ⟨k, BoundedAtlasScenario.ofCommonPDT (C := C) k hlen hε0 hε1⟩

/--
  Первая компонента пары в `scenarioFromCommonPDT` совпадает с полем `k`
  построенного сценария.  Далее мы будем активно использовать это
  переписывание, чтобы переносить численные границы на длину списков
  селекторов.
-/
@[simp]
lemma scenarioFromCommonPDT_k_eq
    {n : Nat} {F : Core.Family n}
    (C : Core.CommonPDT n F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    (scenarioFromCommonPDT (n := n) (F := F) (C := C) hε0 hε1).2.k =
      (scenarioFromCommonPDT (n := n) (F := F) (C := C) hε0 hε1).1 := by
  classical
  unfold scenarioFromCommonPDT
  set witness :=
      ThirdPartyFacts.leaf_budget_from_commonPDT
        (n := n) (F := F) (C := C) with hwitness
  set k := Classical.choose witness with hk
  simp [BoundedAtlasScenario.ofCommonPDT]

/--
  Версия построения сценария напрямую из частичного свидетельства: сначала
  переводим его в `CommonPDT`, затем применяем предыдущую конструкцию.
-/
noncomputable def scenarioFromPartialCertificate
    {n : Nat} {F : Core.Family n} {ℓ : Nat}
    (C : Core.PartialCertificate n ℓ F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    Σ' _ : Nat, BoundedAtlasScenario n :=
  by
    classical
    have h0 : (0 : Core.Q) ≤ (Core.PartialCertificate.toCommonPDT
        (n := n) (ℓ := ℓ) (F := F) C).epsilon := by
      change (0 : Core.Q) ≤ C.epsilon
      exact hε0
    have h1 : (Core.PartialCertificate.toCommonPDT
        (n := n) (ℓ := ℓ) (F := F) C).epsilon ≤ (1 : Core.Q) / 2 := by
      change C.epsilon ≤ (1 : Core.Q) / 2
      exact hε1
    exact
      scenarioFromCommonPDT
        (n := n) (F := F)
        (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C)
        h0 h1

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
    have htmp := hk_spec.1
    simp [hk] at htmp
    exact htmp
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
    have hbound :=
      dictLen_fromCommonPDT_le_pow
        (n := n) (F := S.F) (C := S.commonPDT)
    have hbound' := hbound
    simp [Core.Atlas.fromShrinkage, Core.Atlas.ofPDT,
      Core.CommonPDT.toAtlas, Core.Shrinkage.commonPDT_depthBound,
      Core.Shrinkage.commonPDT_tree] at hbound'
    exact hbound'

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
  have hbound' := hbound
  simp [scenarioFromCommonPDT, BoundedAtlasScenario.ofCommonPDT,
    Core.CommonPDT.toAtlas] at hbound'
  exact hbound'

/--
  Верхняя граница на параметр `k` для сценария, построенного из частичного
  свидетельства.
-/
lemma scenarioFromPartialCertificate_k_le_pow
    {n : Nat} {F : Core.Family n} {ℓ : Nat}
    (C : Core.PartialCertificate n ℓ F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    (scenarioFromPartialCertificate (n := n) (F := F) (ℓ := ℓ)
        (C := C) hε0 hε1).1
      ≤ Nat.pow 2 (C.depthBound + ℓ) :=
  by
    classical
    have hcommon := scenarioFromCommonPDT_k_le_pow
      (n := n) (F := F)
      (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C)
      (hε0 := by
        change (0 : Core.Q) ≤ C.epsilon
        exact hε0)
      (hε1 := by
        change C.epsilon ≤ (1 : Core.Q) / 2
        exact hε1)
    have hrewrite : Nat.pow 2
        (Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C).depthBound
          = Nat.pow 2 (C.depthBound + ℓ) := by
      change Nat.pow 2 (C.depthBound + ℓ) = Nat.pow 2 (C.depthBound + ℓ)
      exact rfl
    have htarget : (scenarioFromCommonPDT (n := n) (F := F)
        (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C)
        (hε0 := by
          change (0 : Core.Q) ≤ C.epsilon
          exact hε0)
        (hε1 := by
          change C.epsilon ≤ (1 : Core.Q) / 2
          exact hε1)).1
        ≤ Nat.pow 2 (C.depthBound + ℓ) :=
      Eq.subst
        (motive := fun s =>
          (scenarioFromCommonPDT (n := n) (F := F)
              (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ)
                (F := F) C)
              (hε0 := by
                change (0 : Core.Q) ≤ C.epsilon
                exact hε0)
              (hε1 := by
                change C.epsilon ≤ (1 : Core.Q) / 2
                exact hε1)).1
            ≤ s)
        hrewrite hcommon
    -- Переводим доказательство обратно к сценарию из частичного свидетельства.
    unfold scenarioFromPartialCertificate
    exact htarget

/-- Длина словаря в сценарии из частичного свидетельства контролируется тем же образом. -/
lemma scenarioFromPartialCertificate_dictLen_le_pow
    {n : Nat} {F : Core.Family n} {ℓ : Nat}
    (C : Core.PartialCertificate n ℓ F)
    (hε0 : (0 : Core.Q) ≤ C.epsilon)
    (hε1 : C.epsilon ≤ (1 : Core.Q) / 2) :
    Counting.dictLen
        (scenarioFromPartialCertificate (n := n) (F := F) (ℓ := ℓ)
            (C := C) hε0 hε1).2.atlas.dict
      ≤ Nat.pow 2 (C.depthBound + ℓ) :=
  by
    classical
    have hcommon := scenarioFromCommonPDT_dictLen_le_pow
      (n := n) (F := F)
      (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C)
      (hε0 := by
        change (0 : Core.Q) ≤ C.epsilon
        exact hε0)
      (hε1 := by
        change C.epsilon ≤ (1 : Core.Q) / 2
        exact hε1)
    have hrewrite : Nat.pow 2
        (Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C).depthBound
          = Nat.pow 2 (C.depthBound + ℓ) := by
      change Nat.pow 2 (C.depthBound + ℓ) = Nat.pow 2 (C.depthBound + ℓ)
      exact rfl
    have htarget : Counting.dictLen
        (scenarioFromCommonPDT (n := n) (F := F)
            (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C)
            (hε0 := by
              change (0 : Core.Q) ≤ C.epsilon
              exact hε0)
            (hε1 := by
              change C.epsilon ≤ (1 : Core.Q) / 2
              exact hε1)).2.atlas.dict
        ≤ Nat.pow 2 (C.depthBound + ℓ) :=
      Eq.subst
        (motive := fun s =>
          Counting.dictLen
            (scenarioFromCommonPDT (n := n) (F := F)
                (C := Core.PartialCertificate.toCommonPDT (n := n) (ℓ := ℓ) (F := F) C)
                (hε0 := by
                  change (0 : Core.Q) ≤ C.epsilon
                  exact hε0)
                (hε1 := by
                  change C.epsilon ≤ (1 : Core.Q) / 2
                  exact hε1)).2.atlas.dict
            ≤ s)
        hrewrite hcommon
    unfold scenarioFromPartialCertificate
    exact htarget

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
                have htmp := hlen f hf
                change ((S.commonPDT.selectors f).dedup).length ≤ k
                dsimp [Core.Shrinkage.commonPDT_selectors]
                exact htmp)
              (hε0 := by
                have htmp := hε0
                change (0 : Core.Q) ≤ S.commonPDT.epsilon
                dsimp [Core.Shrinkage.commonPDT_epsilon]
                exact htmp)
              (hε1 := by
                have htmp := hε1
                change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
                dsimp [Core.Shrinkage.commonPDT_epsilon]
                exact htmp)) :=
      by
        exact hYsubset
    have hLarge' :
        scenarioCapacity
            (sc := BoundedAtlasScenario.ofCommonPDT
              (C := S.commonPDT) k
              (hlen := by
                intro f hf
                have htmp := hlen f hf
                change ((S.commonPDT.selectors f).dedup).length ≤ k
                dsimp [Core.Shrinkage.commonPDT_selectors]
                exact htmp)
              (hε0 := by
                have htmp := hε0
                change (0 : Core.Q) ≤ S.commonPDT.epsilon
                dsimp [Core.Shrinkage.commonPDT_epsilon]
                exact htmp)
              (hε1 := by
                have htmp := hε1
                change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
                dsimp [Core.Shrinkage.commonPDT_epsilon]
                exact htmp))
          < Y.card :=
      by
        exact hLarge
    exact
      no_commonPDT_of_large_family
        (C := S.commonPDT) (k := k)
        (hlen := by
          intro f hf
          have htmp := hlen f hf
          change ((S.commonPDT.selectors f).dedup).length ≤ k
          dsimp [Core.Shrinkage.commonPDT_selectors]
          exact htmp)
        (hε0 := by
          have htmp := hε0
          change (0 : Core.Q) ≤ S.commonPDT.epsilon
          dsimp [Core.Shrinkage.commonPDT_epsilon]
          exact htmp)
        (hε1 := by
          have htmp := hε1
          change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
          dsimp [Core.Shrinkage.commonPDT_epsilon]
          exact htmp)
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
    have hε0' : (0 : Core.Q) ≤ S.commonPDT.epsilon := by
      dsimp [Core.Shrinkage.commonPDT_epsilon]
      exact hε0
    have hε1' : S.commonPDT.epsilon ≤ (1 : Core.Q) / 2 := by
      dsimp [Core.Shrinkage.commonPDT_epsilon]
      exact hε1
    exact
      scenarioFromCommonPDT
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := hε0')
        (hε1 := hε1')

@[simp]
lemma scenarioFromShrinkage_family_eq
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    (scenarioFromShrinkage (n := n) S hε0 hε1).2.family = S.F := by
  classical
  have hε0' : (0 : Core.Q) ≤ S.commonPDT.epsilon := by
    dsimp [Core.Shrinkage.commonPDT_epsilon]
    exact hε0
  have hε1' : S.commonPDT.epsilon ≤ (1 : Core.Q) / 2 := by
    dsimp [Core.Shrinkage.commonPDT_epsilon]
    exact hε1
  have hfamily :=
    scenarioFromCommonPDT_family
      (n := n) (F := S.F) (C := S.commonPDT)
      (hε0 := hε0') (hε1 := hε1')
  change
    (scenarioFromCommonPDT
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := hε0') (hε1 := hε1')).2.family = S.F
    at hfamily
  change
    (scenarioFromCommonPDT
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := hε0') (hε1 := hε1')).2.family = S.F
  exact hfamily

@[simp]
lemma scenarioFromShrinkage_epsilon_eq
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    (scenarioFromShrinkage (n := n) S hε0 hε1).2.atlas.epsilon = S.ε := by
  classical
  have hε0' : (0 : Core.Q) ≤ S.commonPDT.epsilon := by
    dsimp [Core.Shrinkage.commonPDT_epsilon]
    exact hε0
  have hε1' : S.commonPDT.epsilon ≤ (1 : Core.Q) / 2 := by
    dsimp [Core.Shrinkage.commonPDT_epsilon]
    exact hε1
  have heps :=
    scenarioFromCommonPDT_epsilon
      (n := n) (F := S.F) (C := S.commonPDT)
      (hε0 := hε0') (hε1 := hε1')
  change
    (scenarioFromCommonPDT
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := hε0') (hε1 := hε1')).2.atlas.epsilon = S.ε
    at heps
  change
    (scenarioFromCommonPDT
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := hε0') (hε1 := hε1')).2.atlas.epsilon = S.ε
  exact heps

/--
  Первая компонента пары `scenarioFromShrinkage` совпадает с полем `k`
  внутри построенного сценария.  Это напрямую следует из предыдущей леммы
  для `scenarioFromCommonPDT`.
-/
@[simp]
lemma scenarioFromShrinkage_k_eq
    {n : Nat} (S : Core.Shrinkage n)
    (hε0 : (0 : Core.Q) ≤ S.ε) (hε1 : S.ε ≤ (1 : Core.Q) / 2) :
    (scenarioFromShrinkage (n := n) S hε0 hε1).2.k =
      (scenarioFromShrinkage (n := n) S hε0 hε1).1 := by
  classical
  have hε0' : (0 : Core.Q) ≤ S.commonPDT.epsilon := by
    dsimp [Core.Shrinkage.commonPDT_epsilon]
    exact hε0
  have hε1' : S.commonPDT.epsilon ≤ (1 : Core.Q) / 2 := by
    dsimp [Core.Shrinkage.commonPDT_epsilon]
    exact hε1
  simpa [scenarioFromShrinkage, Core.Shrinkage.commonPDT_epsilon]
    using
      (scenarioFromCommonPDT_k_eq
        (n := n) (F := S.F) (C := S.commonPDT)
        (hε0 := hε0') (hε1 := hε1'))

/--
  Специализация к случаю AC⁰: из shrinkage-конструкции, предоставленной
  внешним фактом, автоматически получаем ограниченный сценарий.  Лемма
  также заботится об условиях `0 ≤ ε ≤ 1/2`, необходимых для применения
  ёмкостных оценок.
-/
noncomputable def scenarioFromAC0
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    Σ' _ : Nat, BoundedAtlasScenario params.n :=
  by
    classical
    let S := ThirdPartyFacts.certificate_from_AC0 params F hF hSmall
    let hε0 := ThirdPartyFacts.certificate_from_AC0_eps_nonneg
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    let hε1 := ThirdPartyFacts.certificate_from_AC0_eps_le_half
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    let base :=
      scenarioFromShrinkage (n := params.n) (S := S) hε0 hε1
    have hFamily : base.2.family = S.F :=
      scenarioFromShrinkage_family_eq
        (n := params.n) (S := S) hε0 hε1
    have hSF : S.F = F :=
      ThirdPartyFacts.certificate_from_AC0_family
        (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    refine ⟨base.1, { base.2 with family := F, works := ?_, bounded := ?_ }⟩
    ·
      have hworksS : WorksFor base.2.atlas S.F :=
        Eq.subst (motive := fun fam => WorksFor base.2.atlas fam)
          (Eq.symm hFamily) base.2.works
      exact Eq.subst (motive := fun fam => WorksFor base.2.atlas fam)
        hSF hworksS
    · intro f hf
      have hfS : f ∈ S.F :=
        Eq.subst (motive := fun fam => f ∈ fam) (Eq.symm hSF) hf
      have hfBase : f ∈ base.2.family :=
        Eq.subst (motive := fun fam => f ∈ fam) (Eq.symm hFamily) hfS
      exact base.2.bounded f hfBase

/--
  Версия `scenarioFromAC0`, использующая явную strong‑границу на число подкубов.
  Она не зависит от предположения `AC0SmallEnough` и является прямой точкой
  для будущей polylog‑леммы.
-/
noncomputable def scenarioFromAC0_with_bound
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    Σ' _ : Nat, BoundedAtlasScenario params.n := by
  classical
  let S := ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound
  let hε0 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_nonneg
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  let hε1 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_le_half
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  let base := scenarioFromShrinkage (n := params.n) (S := S) hε0 hε1
  have hFamily : base.2.family = S.F :=
    scenarioFromShrinkage_family_eq
      (n := params.n) (S := S) hε0 hε1
  have hSF : S.F = F :=
    ThirdPartyFacts.certificate_from_AC0_with_bound_family
      (params := params) (F := F) (hF := hF) (hBound := hBound)
  refine ⟨base.1, { base.2 with family := F, works := ?_, bounded := ?_ }⟩
  ·
    have hworksS : WorksFor base.2.atlas S.F :=
      Eq.subst (motive := fun fam => WorksFor base.2.atlas fam)
        (Eq.symm hFamily) base.2.works
    exact Eq.subst (motive := fun fam => WorksFor base.2.atlas fam)
      hSF hworksS
  · intro f hf
    have hfS : f ∈ S.F :=
      Eq.subst (motive := fun fam => f ∈ fam) (Eq.symm hSF) hf
    have hfBase : f ∈ base.2.family :=
      Eq.subst (motive := fun fam => f ∈ fam) (Eq.symm hFamily) hfS
    exact base.2.bounded f hfBase

/--
  Первая компонента пары `scenarioFromAC0` совпадает с параметром `k` внутри
  построенного сценария.  Это упрощает перенос численных оценок на поле `k`.
-/
@[simp]
lemma scenarioFromAC0_k_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    (scenarioFromAC0 params F hF hSmall).2.k =
      (scenarioFromAC0 params F hF hSmall).1 := by
  classical
  unfold scenarioFromAC0
  set S := ThirdPartyFacts.certificate_from_AC0 params F hF hSmall
  set hε0 := ThirdPartyFacts.certificate_from_AC0_eps_nonneg
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_eps_le_half
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  simp [scenarioFromShrinkage_k_eq]

@[simp]
lemma scenarioFromAC0_with_bound_k_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    (scenarioFromAC0_with_bound params F hF hBound).2.k =
      (scenarioFromAC0_with_bound params F hF hBound).1 := by
  classical
  unfold scenarioFromAC0_with_bound
  set S := ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound
  set hε0 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_nonneg
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_le_half
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  simp [scenarioFromShrinkage_k_eq]

/-- Семейство функций в сценарии, построенном из факта `AC⁰ → shrinkage`,
  совпадает с исходным списком `F`.  Это удобное переписывание для дальнейших
  аргументов о подсемействах и мощностях. -/
@[simp]
lemma scenarioFromAC0_family_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    (scenarioFromAC0 params F hF hSmall).2.family = F := by
  classical
  unfold scenarioFromAC0
  simp

@[simp]
lemma scenarioFromAC0_with_bound_family_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    (scenarioFromAC0_with_bound params F hF hBound).2.family = F := by
  classical
  unfold scenarioFromAC0_with_bound
  simp

/--
  Аналог конструкции `scenarioFromAC0`, но для shrinkage факта о
  локальных схемах.  Логика полностью идентична: извлекаем общий PDT,
  приводим ошибку к формату SAL и упаковываем в ограниченный сценарий.
-/
noncomputable def scenarioFromLocalCircuit
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    Σ' _ : Nat, BoundedAtlasScenario params.n :=
  by
    classical
    let witness := ThirdPartyFacts.localCircuitWitness params F hF
    let S := witness.shrinkage
    have hF : S.F = F := witness.family_eq
    have hε_le_half : S.ε ≤ (1 : Core.Q) / 2 := by
      have hbase := witness.epsilon_le_inv
      have hhalf := ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
        params.n (ε := S.ε) hbase
      exact hhalf
    have hε_nonneg : (0 : Core.Q) ≤ S.ε := witness.epsilon_nonneg
    let base :=
      scenarioFromCommonPDT
        (n := params.n) (F := S.F) (C := S.commonPDT)
        (hε0 := by
          have htmp := hε_nonneg
          change (0 : Core.Q) ≤ S.commonPDT.epsilon
          dsimp [Core.Shrinkage.commonPDT_epsilon]
          exact htmp)
        (hε1 := by
          have htmp := hε_le_half
          change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
          dsimp [Core.Shrinkage.commonPDT_epsilon]
          exact htmp)
    have base_family : base.2.family = S.F := by
      simp [base, scenarioFromCommonPDT, BoundedAtlasScenario.ofCommonPDT]
    refine ⟨base.1, { base.2 with family := F, works := ?_, bounded := ?_ }⟩
    ·
      have hworksBase : WorksFor base.2.atlas S.F := by
        have htmp := base.2.works
        simp [base_family] at htmp
        exact htmp
      exact hF ▸ hworksBase
    · intro f hf
      have hfS : f ∈ S.F := hF ▸ hf
      have hfBase : f ∈ base.2.family := by
        have htmp := hfS
        simp [base_family] at htmp
        exact htmp
      have hbounded := base.2.bounded f hfBase
      have htmp := hbounded
      simp [base_family] at htmp
      exact htmp

/-- Семейство в сценарии для локальных схем совпадает с исходным списком `F`. -/
@[simp]
lemma scenarioFromLocalCircuit_family_eq
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    (scenarioFromLocalCircuit params F hF).2.family = F := by
  classical
  unfold scenarioFromLocalCircuit
  set witness := ThirdPartyFacts.localCircuitWitness params F hF
  set S := witness.shrinkage
  simp [scenarioFromLocalCircuit, witness, S]

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
  have hbound :=
    scenarioFromCommonPDT_k_le_pow
      (n := n) (F := S.F) (C := S.commonPDT)
      (hε0 := by
        have htmp := hε0
        change (0 : Core.Q) ≤ S.commonPDT.epsilon
        dsimp [Core.Shrinkage.commonPDT_epsilon]
        exact htmp)
      (hε1 := by
        have htmp := hε1
        change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
        dsimp [Core.Shrinkage.commonPDT_epsilon]
        exact htmp)
  have hbound' := hbound
  simp [scenarioFromShrinkage, Core.Shrinkage.commonPDT_depthBound,
    Core.Shrinkage.commonPDT_epsilon] at hbound'
  exact hbound'

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
  have hbound :=
    scenarioFromCommonPDT_dictLen_le_pow
      (n := n) (F := S.F) (C := S.commonPDT)
      (hε0 := by
        have htmp := hε0
        change (0 : Core.Q) ≤ S.commonPDT.epsilon
        dsimp [Core.Shrinkage.commonPDT_epsilon]
        exact htmp)
      (hε1 := by
        have htmp := hε1
        change S.commonPDT.epsilon ≤ (1 : Core.Q) / 2
        dsimp [Core.Shrinkage.commonPDT_epsilon]
        exact htmp)
  have hbound' := hbound
  simp [scenarioFromShrinkage, Core.Shrinkage.commonPDT_depthBound,
    Core.Shrinkage.commonPDT_epsilon] at hbound'
  exact hbound'

/--
  Параметр `k` в сценарии AC⁰ не превышает `2^{ac0DepthBound params}`.
  Получаем его из границы `t ≤ ac0DepthBound params`, предоставленной
  constructive shrinkage.
-/
lemma scenarioFromAC0_k_le_pow
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    (scenarioFromAC0 params F hF hSmall).1
      ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) := by
  classical
  unfold scenarioFromAC0
  set S := ThirdPartyFacts.certificate_from_AC0 params F hF hSmall
  set hε0 := ThirdPartyFacts.certificate_from_AC0_eps_nonneg
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_eps_le_half
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hk_base :=
    scenarioFromShrinkage_k_le_pow
      (n := params.n) (S := S) (hε0 := hε0) (hε1 := hε1)
  have htBound :=
    ThirdPartyFacts.certificate_from_AC0_depth_bound
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hpow_bound :
      Nat.pow 2 S.t ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) := by
    have hS : S.t ≤ ThirdPartyFacts.ac0DepthBound params := by
      have htmp := htBound
      change Core.Shrinkage.depthBound (S := S)
          ≤ ThirdPartyFacts.ac0DepthBound params at htmp
      have hrewrite := htmp
      simp [Core.Shrinkage.depthBound] at hrewrite
      exact hrewrite
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hS
  have hresult := hk_base.trans hpow_bound
  have hrewrite :
      (scenarioFromShrinkage (n := params.n) S hε0 hε1).1
        = (scenarioFromAC0 params F hF hSmall).1 := by
    simp [scenarioFromAC0, S, hε0, hε1]
  have hfinal := Eq.subst (motive := fun x => x ≤ _) (Eq.symm hrewrite) hresult
  exact hfinal

/--
  Усиленная версия: параметр `k` в AC⁰-сценарии ограничен
  `2^{ac0DepthBound_strong params}`.  Мы поднимаем уже полученную
  оценку через условие `AC0SmallEnough`.
-/
lemma scenarioFromAC0_k_le_pow_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    (scenarioFromAC0 params F hF hSmall).1
      ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params) := by
  -- Берём слабую границу и поднимаем её монотонностью степени двойки.
  have hweak := scenarioFromAC0_k_le_pow
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hbound := ThirdPartyFacts.ac0DepthBound_le_strong params
  have hpow :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hbound
  exact hweak.trans hpow

lemma scenarioFromAC0_with_bound_k_le_pow_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    (scenarioFromAC0_with_bound params F hF hBound).1
      ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params) := by
  classical
  unfold scenarioFromAC0_with_bound
  set S := ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound
  set hε0 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_nonneg
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_le_half
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hk_base :=
    scenarioFromShrinkage_k_le_pow
      (n := params.n) (S := S) (hε0 := hε0) (hε1 := hε1)
  have htBound :=
    ThirdPartyFacts.certificate_from_AC0_with_bound_depth_bound
      (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hpow_bound :
      Nat.pow 2 S.t ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) := by
    have hS : S.t ≤ ThirdPartyFacts.ac0DepthBound params := by
      have htmp := htBound
      change Core.Shrinkage.depthBound (S := S)
          ≤ ThirdPartyFacts.ac0DepthBound params at htmp
      have hrewrite := htmp
      simp [Core.Shrinkage.depthBound] at hrewrite
      exact hrewrite
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hS
  have hresult := hk_base.trans hpow_bound
  have hrewrite :
      (scenarioFromShrinkage (n := params.n) S hε0 hε1).1
        = (scenarioFromAC0_with_bound params F hF hBound).1 := by
    simp [scenarioFromAC0_with_bound, S, hε0, hε1]
  have hfinal := Eq.subst (motive := fun x => x ≤ _) (Eq.symm hrewrite) hresult
  simpa [ThirdPartyFacts.ac0DepthBound] using hfinal

/--
  Оценка на длину словаря в AC⁰-сценарии:
  она не превосходит `2^{ac0DepthBound params}`.
-/
lemma scenarioFromAC0_dictLen_le_pow
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    Counting.dictLen (scenarioFromAC0 params F hF hSmall).2.atlas.dict
      ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) := by
  classical
  unfold scenarioFromAC0
  set S := ThirdPartyFacts.certificate_from_AC0 params F hF hSmall
  set hε0 := ThirdPartyFacts.certificate_from_AC0_eps_nonneg
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_eps_le_half
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hdict_base :=
    scenarioFromShrinkage_dictLen_le_pow
      (n := params.n) (S := S) (hε0 := hε0) (hε1 := hε1)
  have htBound :=
    ThirdPartyFacts.certificate_from_AC0_depth_bound
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hpow_bound :
      Nat.pow 2 S.t ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) := by
    have hS : S.t ≤ ThirdPartyFacts.ac0DepthBound params := by
      have htmp := htBound
      change Core.Shrinkage.depthBound (S := S)
          ≤ ThirdPartyFacts.ac0DepthBound params at htmp
      have hrewrite := htmp
      simp [Core.Shrinkage.depthBound] at hrewrite
      exact hrewrite
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hS
  have hresult := hdict_base.trans hpow_bound
  have hrewrite :
      Counting.dictLen
          (scenarioFromShrinkage (n := params.n) S hε0 hε1).2.atlas.dict
        = Counting.dictLen (scenarioFromAC0 params F hF hSmall).2.atlas.dict := by
    simp [scenarioFromAC0, S, hε0, hε1]
  have hfinal := Eq.subst (motive := fun x => x ≤ _) (Eq.symm hrewrite) hresult
  exact hfinal

/--
  Усиленная оценка длины словаря: `|dict| ≤ 2^{ac0DepthBound_strong params}`.
  Лемма следует из слабой версии и монотонности степени двойки.
-/
lemma scenarioFromAC0_dictLen_le_pow_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    Counting.dictLen (scenarioFromAC0 params F hF hSmall).2.atlas.dict
      ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params) := by
  -- Используем слабую оценку и поднимаем её.
  have hweak := scenarioFromAC0_dictLen_le_pow
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hbound := ThirdPartyFacts.ac0DepthBound_le_strong params
  have hpow :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hbound
  exact hweak.trans hpow

lemma scenarioFromAC0_with_bound_dictLen_le_pow_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    Counting.dictLen (scenarioFromAC0_with_bound params F hF hBound).2.atlas.dict
      ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params) := by
  classical
  unfold scenarioFromAC0_with_bound
  set S := ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound
  set hε0 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_nonneg
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_le_half
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hdict_base :=
    scenarioFromShrinkage_dictLen_le_pow
      (n := params.n) (S := S) (hε0 := hε0) (hε1 := hε1)
  have htBound :=
    ThirdPartyFacts.certificate_from_AC0_with_bound_depth_bound
      (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hpow_bound :
      Nat.pow 2 S.t ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) := by
    have hS : S.t ≤ ThirdPartyFacts.ac0DepthBound params := by
      have htmp := htBound
      change Core.Shrinkage.depthBound (S := S)
          ≤ ThirdPartyFacts.ac0DepthBound params at htmp
      have hrewrite := htmp
      simp [Core.Shrinkage.depthBound] at hrewrite
      exact hrewrite
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hS
  have hresult := hdict_base.trans hpow_bound
  have hrewrite :
      Counting.dictLen
          (scenarioFromShrinkage (n := params.n) S hε0 hε1).2.atlas.dict
        = Counting.dictLen
            (scenarioFromAC0_with_bound params F hF hBound).2.atlas.dict := by
    simp [scenarioFromAC0_with_bound, S, hε0, hε1]
  have hfinal := Eq.subst (motive := fun x => x ≤ _) (Eq.symm hrewrite) hresult
  simpa [ThirdPartyFacts.ac0DepthBound] using hfinal

/--
  Полезное переписывание: погрешность атласа в `scenarioFromAC0` совпадает
  с ε shrinkage-сертификата, предоставленного фактом `certificate_from_AC0`.
  Это связывает шаг A (усадка) со сценарием шага B на уровне точных чисел. -/
@[simp]
lemma scenarioFromAC0_epsilon_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    (scenarioFromAC0 params F hF hSmall).2.atlas.epsilon
      = (ThirdPartyFacts.certificate_from_AC0 params F hF hSmall).ε := by
  classical
  unfold scenarioFromAC0
  set S := ThirdPartyFacts.certificate_from_AC0 params F hF hSmall
  set hε0 := ThirdPartyFacts.certificate_from_AC0_eps_nonneg
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_eps_le_half
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  set base := scenarioFromShrinkage (n := params.n) S hε0 hε1
  have hbase : base.2.atlas.epsilon = S.ε :=
    scenarioFromShrinkage_epsilon_eq
      (n := params.n) (S := S) (hε0 := hε0) (hε1 := hε1)
  -- Конструкция `scenarioFromAC0` меняет только поле `family`, поэтому ε
  -- совпадает с ε базового сценария `base`.
  have hsc :
      (scenarioFromAC0 params F hF hSmall).2.atlas.epsilon
        = base.2.atlas.epsilon := by
    unfold scenarioFromAC0
    simp [S, base]
  exact hsc.trans hbase

@[simp]
lemma scenarioFromAC0_with_bound_epsilon_eq
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    (scenarioFromAC0_with_bound params F hF hBound).2.atlas.epsilon
      = (ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound).ε := by
  classical
  unfold scenarioFromAC0_with_bound
  set S := ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound
  set hε0 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_nonneg
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  set hε1 := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_le_half
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  set base := scenarioFromShrinkage (n := params.n) S hε0 hε1
  have hbase : base.2.atlas.epsilon = S.ε :=
    scenarioFromShrinkage_epsilon_eq
      (n := params.n) (S := S) (hε0 := hε0) (hε1 := hε1)
  have hsc :
      (scenarioFromAC0_with_bound params F hF hBound).2.atlas.epsilon
        = base.2.atlas.epsilon := by
    unfold scenarioFromAC0_with_bound
    simp [S, base]
  exact hsc.trans hbase

/--
  Совокупное описание ограниченного сценария из `scenarioFromAC0`.
  Мы собираем в одну точку все численные границы, необходимые для шага B:

  * параметр `k` не превосходит `2^{ac0DepthBound params}`;
  * длина словаря ограничена тем же числом;
  * погрешность лежит в диапазоне `0 ≤ ε ≤ 1/2` и дополнительно
    `ε ≤ 1/(n+2)`.

  Такая формулировка подчёркивает, что шаг A уже поставляет именно те
  данные, которые требуются Covering/Leaf-Budget анализу шага B. -/
lemma scenarioFromAC0_completeBounds
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params)
    let sc := scenarioFromAC0 params F hF hSmall
    sc.1 ≤ bound ∧
      Counting.dictLen sc.2.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.2.atlas.epsilon ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  intro bound sc
  -- Первая граница: параметр `k` ограничен степенью двух от глубины PDT.
  have hk := scenarioFromAC0_k_le_pow
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  -- Вторая граница: длина словаря не превосходит того же значения.
  have hdict := scenarioFromAC0_dictLen_le_pow
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  -- Погрешность неотрицательна и ≤ 1/2 по определению сценария.
  have hε0 := sc.2.hε0
  have hε1 := sc.2.hε1
  -- Для верхней оценки через `1/(n+2)` переписываем ε через shrinkage-сертификат.
  have heq := scenarioFromAC0_epsilon_eq
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hεInv := ThirdPartyFacts.certificate_from_AC0_eps_bound
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hεInv' : sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    have hrewrite :
        sc.2.atlas.epsilon =
          (ThirdPartyFacts.certificate_from_AC0 params F hF hSmall).ε := by
      exact heq
    have hgoal := Eq.subst
      (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
      (Eq.symm hrewrite) hεInv
    exact hgoal
  refine And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv')))
  · -- Вставляем объявленный параметр `bound`.
    change sc.1 ≤ bound
    exact hk
  · change Counting.dictLen sc.2.atlas.dict ≤ bound
    exact hdict

/--
  Полная сводка для сильной глубинной оценки.  Все численные ограничения
  идентичны слабой версии, кроме того, что `bound` теперь строится
  из `ac0DepthBound_strong`.
-/
lemma scenarioFromAC0_completeBounds_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params)
    let sc := scenarioFromAC0 params F hF hSmall
    sc.1 ≤ bound ∧
      Counting.dictLen sc.2.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.2.atlas.epsilon ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  intro bound sc
  -- Границы на `k` и словарь теперь берутся из сильных версий.
  have hk := scenarioFromAC0_k_le_pow_strong
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hdict := scenarioFromAC0_dictLen_le_pow_strong
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  -- Эпсилон остаётся тем же.
  have hε0 := sc.2.hε0
  have hε1 := sc.2.hε1
  have heq := scenarioFromAC0_epsilon_eq
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hεInv := ThirdPartyFacts.certificate_from_AC0_eps_bound
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hεInv' : sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    have hrewrite :
        sc.2.atlas.epsilon =
          (ThirdPartyFacts.certificate_from_AC0 params F hF hSmall).ε := by
      exact heq
    have hgoal := Eq.subst
      (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
      (Eq.symm hrewrite) hεInv
    exact hgoal
  refine And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv')))
  · change sc.1 ≤ bound
    exact hk
  · change Counting.dictLen sc.2.atlas.dict ≤ bound
    exact hdict

lemma scenarioFromAC0_with_bound_completeBounds_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params)
    let sc := scenarioFromAC0_with_bound params F hF hBound
    sc.1 ≤ bound ∧
      Counting.dictLen sc.2.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.2.atlas.epsilon ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  intro bound sc
  have hk := scenarioFromAC0_with_bound_k_le_pow_strong
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hdict := scenarioFromAC0_with_bound_dictLen_le_pow_strong
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hε0 := sc.2.hε0
  have hε1 := sc.2.hε1
  have heq := scenarioFromAC0_with_bound_epsilon_eq
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hεInv := ThirdPartyFacts.certificate_from_AC0_with_bound_eps_bound
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hεInv' : sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    have hrewrite :
        sc.2.atlas.epsilon =
          (ThirdPartyFacts.certificate_from_AC0_with_bound params F hF hBound).ε := by
      exact heq
    have hgoal := Eq.subst
      (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
      (Eq.symm hrewrite) hεInv
    exact hgoal
  refine And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv')))
  · change sc.1 ≤ bound
    exact hk
  · change Counting.dictLen sc.2.atlas.dict ≤ bound
    exact hdict

/--
  Сводное существование ограниченного атласа из AC⁰-свидетельства.  Мы упаковываем
  конструкцию `scenarioFromAC0` в экзистенциальную форму: существует `k` и сценарий
  с семейством `F`, где все численные границы совпадают с теми, что требуются для шага B.
-/
theorem exists_boundedAtlas_from_AC0
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    ∃ (k : Nat) (sc : BoundedAtlasScenario params.n),
      sc.family = F ∧
      k ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) ∧
      Counting.dictLen sc.atlas.dict
        ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params) ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let sc := scenarioFromAC0 params F hF hSmall
  have hfamily : sc.2.family = F := by
    dsimp [sc]
    exact scenarioFromAC0_family_eq
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have h_bounds :=
    scenarioFromAC0_completeBounds
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  dsimp [sc] at h_bounds
  rcases h_bounds with ⟨hk, hrest⟩
  rcases hrest with ⟨hdict, hrest⟩
  rcases hrest with ⟨hε0, hrest⟩
  rcases hrest with ⟨hε1, hεInv⟩
  refine ⟨sc.1, sc.2, ?_⟩
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv))))
  · exact hfamily
  · exact hk
  · exact hdict

/--
  Усиленная экзистенциальная формулировка: все границы выражены через
  `ac0DepthBound_strong`.  Сценарий тот же, мы лишь переключаем числовую цель.
-/
theorem exists_boundedAtlas_from_AC0_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    ∃ (k : Nat) (sc : BoundedAtlasScenario params.n),
      sc.family = F ∧
      k ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params) ∧
      Counting.dictLen sc.atlas.dict
        ≤ Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params) ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let sc := scenarioFromAC0 params F hF hSmall
  have hfamily : sc.2.family = F := by
    dsimp [sc]
    exact scenarioFromAC0_family_eq
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have h_bounds :=
    scenarioFromAC0_completeBounds_strong
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  dsimp [sc] at h_bounds
  rcases h_bounds with ⟨hk, hrest⟩
  rcases hrest with ⟨hdict, hrest⟩
  rcases hrest with ⟨hε0, hrest⟩
  rcases hrest with ⟨hε1, hεInv⟩
  refine ⟨sc.1, sc.2, ?_⟩
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv))))
  · exact hfamily
  · exact hk
  · exact hdict

/--
  Локальные схемы дают аналогичную границу: `k ≤ 2^{ℓ · (log₂(M+2) + depth + 1)}`.
-/
lemma scenarioFromLocalCircuit_k_le_pow
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    (scenarioFromLocalCircuit params F hF).1
      ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
  classical
  unfold scenarioFromLocalCircuit
  set witness := ThirdPartyFacts.localCircuitWitness params F hF
  set S := witness.shrinkage
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := witness.epsilon_nonneg
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
      params.n (ε := S.ε) witness.epsilon_le_inv
  have hcommon_nonneg : (0 : Core.Q) ≤ S.commonPDT.epsilon := by
    change (0 : Core.Q) ≤ S.ε
    exact hε_nonneg
  have hcommon_half : S.commonPDT.epsilon ≤ (1 : Core.Q) / 2 := by
    change S.ε ≤ (1 : Core.Q) / 2
    exact hε_half
  set base :=
    scenarioFromCommonPDT
      (n := params.n) (F := S.F) (C := S.commonPDT)
      (hε0 := hcommon_nonneg) (hε1 := hcommon_half)
  have hk_base :=
    scenarioFromCommonPDT_k_le_pow
      (n := params.n) (F := S.F)
      (C := S.commonPDT)
      (hε0 := hcommon_nonneg) (hε1 := hcommon_half)
  have hpow_bound :
      base.1 ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
    have hdepth_bound : base.1 ≤ Nat.pow 2 S.commonPDT.depthBound := hk_base
    have hrewrite : Nat.pow 2 S.commonPDT.depthBound = Nat.pow 2 S.t := by
      simp [Core.Shrinkage.commonPDT_depthBound]
    have htarget : base.1 ≤ Nat.pow 2 S.t := by
      exact Eq.subst (motive := fun x => base.1 ≤ x) hrewrite.symm hdepth_bound
    have hbound_pow :
        Nat.pow 2 S.t ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
      have hdepth := witness.depth_le
      exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepth
    exact htarget.trans hbound_pow
  have hsc : (scenarioFromLocalCircuit params F hF).1 = base.1 := by
    simp [scenarioFromLocalCircuit, witness, S, base]
  exact Eq.subst (motive := fun x => x ≤ _) (Eq.symm hsc) hpow_bound

/--
  И для длины словаря в локальных схемах действует та же оценка.
-/
lemma scenarioFromLocalCircuit_dictLen_le_pow
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    Counting.dictLen (scenarioFromLocalCircuit params F hF).2.atlas.dict
      ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
  classical
  unfold scenarioFromLocalCircuit
  set witness := ThirdPartyFacts.localCircuitWitness params F hF
  set S := witness.shrinkage
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := witness.epsilon_nonneg
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
      params.n (ε := S.ε) witness.epsilon_le_inv
  have hcommon_nonneg : (0 : Core.Q) ≤ S.commonPDT.epsilon := by
    change (0 : Core.Q) ≤ S.ε
    exact hε_nonneg
  have hcommon_half : S.commonPDT.epsilon ≤ (1 : Core.Q) / 2 := by
    change S.ε ≤ (1 : Core.Q) / 2
    exact hε_half
  set base :=
    scenarioFromCommonPDT
      (n := params.n) (F := S.F) (C := S.commonPDT)
      (hε0 := hcommon_nonneg) (hε1 := hcommon_half)
  have hdict_base :=
    scenarioFromCommonPDT_dictLen_le_pow
      (n := params.n) (F := S.F)
      (C := S.commonPDT)
      (hε0 := hcommon_nonneg) (hε1 := hcommon_half)
  have hpow_bound :
      Counting.dictLen base.2.atlas.dict
        ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
    have hlen := hdict_base
    have hrewrite : Nat.pow 2 S.commonPDT.depthBound = Nat.pow 2 S.t := by
      simp [Core.Shrinkage.commonPDT_depthBound]
    have htarget :
        Counting.dictLen base.2.atlas.dict ≤ Nat.pow 2 S.t := by
      exact Eq.subst (motive := fun x => Counting.dictLen base.2.atlas.dict ≤ x)
        hrewrite.symm hlen
    have hbound_pow :
        Nat.pow 2 S.t ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) := by
      have hdepth := witness.depth_le
      exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepth
    exact htarget.trans hbound_pow
  have hsc :
      Counting.dictLen (scenarioFromLocalCircuit params F hF).2.atlas.dict
        = Counting.dictLen base.2.atlas.dict := by
    simp [scenarioFromLocalCircuit, witness, S, base]
  exact Eq.subst (motive := fun x => x ≤ _) hsc hpow_bound

@[simp]
lemma scenarioFromLocalCircuit_epsilon_eq
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    (scenarioFromLocalCircuit params F hF).2.atlas.epsilon
      = (ThirdPartyFacts.localCircuitWitness params F hF).shrinkage.ε := by
  classical
  unfold scenarioFromLocalCircuit
  set witness := ThirdPartyFacts.localCircuitWitness params F hF
  set S := witness.shrinkage
  have hε_nonneg : (0 : Core.Q) ≤ S.ε := witness.epsilon_nonneg
  have hε_half : S.ε ≤ (1 : Core.Q) / 2 :=
    ThirdPartyFacts.eps_le_half_of_eps_le_inv_nplus2
      params.n (ε := S.ε) witness.epsilon_le_inv
  set base :=
    scenarioFromCommonPDT
      (n := params.n) (F := S.F) (C := S.commonPDT)
      (hε0 := hε_nonneg)
      (hε1 := hε_half)
  have hbase : base.2.atlas.epsilon = S.commonPDT.epsilon := by
    dsimp [base]
    exact scenarioFromCommonPDT_epsilon
      (C := S.commonPDT)
      (hε0 := hε_nonneg)
      (hε1 := hε_half)
  have hcommon : S.commonPDT.epsilon = S.ε := rfl
  have hrewrite :
      (scenarioFromLocalCircuit (params := params) (F := F) (hF := hF)).2.atlas.epsilon
        = base.2.atlas.epsilon := by
    simp [scenarioFromLocalCircuit, witness, S, base]
  have hresult := Eq.trans hbase hcommon
  exact Eq.trans hrewrite hresult

/--
  Поле `k` в `scenarioFromLocalCircuit` совпадает с первой компонентой пары.
  Это повторяет довод для AC⁰ и позволяет напрямую ограничивать число
  селекторов в сценарии локальных схем.
-/
@[simp]
lemma scenarioFromLocalCircuit_k_eq
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    (scenarioFromLocalCircuit params F hF).2.k =
      (scenarioFromLocalCircuit params F hF).1 := by
  classical
  unfold scenarioFromLocalCircuit
  set witness := ThirdPartyFacts.localCircuitWitness params F hF
  set S := witness.shrinkage
  simp [scenarioFromCommonPDT_k_eq]

lemma scenarioFromLocalCircuit_completeBounds
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    let bound := Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2)
      + params.depth + 1))
    let sc := scenarioFromLocalCircuit params F hF
    sc.1 ≤ bound ∧
      Counting.dictLen sc.2.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.2.atlas.epsilon ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  intro bound sc
  have hk := scenarioFromLocalCircuit_k_le_pow
    (params := params) (F := F) (hF := hF)
  have hdict := scenarioFromLocalCircuit_dictLen_le_pow
    (params := params) (F := F) (hF := hF)
  have hε0 := sc.2.hε0
  have hε1 := sc.2.hε1
  have heq := scenarioFromLocalCircuit_epsilon_eq
    (params := params) (F := F) (hF := hF)
  let witness := ThirdPartyFacts.localCircuitWitness params F hF
  let S := witness.shrinkage
  have hεBound := witness.epsilon_le_inv
  have hεInv : sc.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    have hrewrite : sc.2.atlas.epsilon = S.ε := heq
    have htarget : S.ε ≤ (1 : Core.Q) / (params.n + 2) := hεBound
    exact hrewrite ▸ htarget
  refine And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv)))
  · change sc.1 ≤ bound
    exact hk
  · change Counting.dictLen sc.2.atlas.dict ≤ bound
    exact hdict

/--
  Экзистенциальная форма ограниченного атласа для локальных схем.  Аналогично
  AC⁰-случаю, получаем конкретный сценарий и численные границы напрямую из
  `scenarioFromLocalCircuit`.
-/
theorem exists_boundedAtlas_from_localCircuit
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    ∃ (k : Nat) (sc : BoundedAtlasScenario params.n),
      sc.family = F ∧
      k ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) ∧
      Counting.dictLen sc.atlas.dict
        ≤ Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)) ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let sc := scenarioFromLocalCircuit params F hF
  have hfamily : sc.2.family = F := by
    dsimp [sc]
    exact scenarioFromLocalCircuit_family_eq (params := params) (F := F) (hF := hF)
  have h_bounds :=
    scenarioFromLocalCircuit_completeBounds (params := params) (F := F) (hF := hF)
  dsimp [sc] at h_bounds
  rcases h_bounds with ⟨hk, hrest⟩
  rcases hrest with ⟨hdict, hrest⟩
  rcases hrest with ⟨hε0, hrest⟩
  rcases hrest with ⟨hε1, hεInv⟩
  refine ⟨sc.1, sc.2, ?_⟩
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro hε0 (And.intro hε1 hεInv))))
  · exact hfamily
  · exact hk
  · exact hdict

/--
  Сводное описание сценария, полученного из AC⁰ shrinkage: все численные
  границы из шага A совмещаются с оценкой мощности семейства из шага B.
-/
lemma scenarioFromAC0_stepAB_summary
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    let pack := scenarioFromAC0 params F hF hSmall
    let sc := pack.2
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound params)
    sc.family = F ∧
      sc.k ≤ bound ∧
      Counting.dictLen sc.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) ∧
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k
          (Nat.pow 2 params.n) sc.atlas.epsilon sc.hε0 sc.hε1 :=
  by
    classical
    intro pack sc bound
    have hfamily := scenarioFromAC0_family_eq
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    have hbounds_raw := scenarioFromAC0_completeBounds
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    have hbounds :
        pack.1 ≤ bound ∧
          Counting.dictLen pack.2.atlas.dict ≤ bound ∧
          (0 : Core.Q) ≤ pack.2.atlas.epsilon ∧
          pack.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
          pack.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
      simpa [pack, bound] using hbounds_raw
    have hfamily' : sc.family = F := by
      simpa [pack, sc] using hfamily
    rcases hbounds with ⟨hk_base, hrest⟩
    rcases hrest with ⟨hdict_base, hrest⟩
    rcases hrest with ⟨hε0_base, hrest⟩
    rcases hrest with ⟨hε1_base, hεInv_base⟩
    have hkEq := scenarioFromAC0_k_eq
      (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    have hkEq' : pack.2.k = pack.1 := by
      simpa [pack] using hkEq
    have hk' : sc.k ≤ bound := by
      simpa [pack, sc, hkEq'] using hk_base
    have hdict' : Counting.dictLen sc.atlas.dict ≤ bound := by
      simpa [pack, sc, bound] using hdict_base
    have hε0' : (0 : Core.Q) ≤ sc.atlas.epsilon := by
      simpa [pack, sc] using hε0_base
    have hε1' : sc.atlas.epsilon ≤ (1 : Core.Q) / 2 := by
      simpa [pack, sc] using hε1_base
    have hεInv' : sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
      simpa [pack, sc] using hεInv_base
    have hcap := family_card_le_capacity (sc := sc)
    refine And.intro hfamily' (And.intro hk' (And.intro hdict'
      (And.intro hε0' (And.intro hε1' (And.intro hεInv' ?_)))))
    exact hcap

/--
  Усиленная версия шага A+B: всё аналогично `scenarioFromAC0_stepAB_summary`,
  но численные границы выражены через `ac0DepthBound_strong`.
-/
lemma scenarioFromAC0_stepAB_summary_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    let pack := scenarioFromAC0 params F hF hSmall
    let sc := pack.2
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params)
    sc.family = F ∧
      sc.k ≤ bound ∧
      Counting.dictLen sc.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) ∧
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k
          (Nat.pow 2 params.n) sc.atlas.epsilon sc.hε0 sc.hε1 := by
  classical
  intro pack sc bound
  have hfamily := scenarioFromAC0_family_eq
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hbounds_raw := scenarioFromAC0_completeBounds_strong
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hbounds :
      pack.1 ≤ bound ∧
        Counting.dictLen pack.2.atlas.dict ≤ bound ∧
        (0 : Core.Q) ≤ pack.2.atlas.epsilon ∧
        pack.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
        pack.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    simpa [pack, bound] using hbounds_raw
  have hfamily' : sc.family = F := by
    simpa [pack, sc] using hfamily
  rcases hbounds with ⟨hk_base, hrest⟩
  rcases hrest with ⟨hdict_base, hrest⟩
  rcases hrest with ⟨hε0_base, hrest⟩
  rcases hrest with ⟨hε1_base, hεInv_base⟩
  have hkEq := scenarioFromAC0_k_eq
    (params := params) (F := F) (hF := hF) (hSmall := hSmall)
  have hkEq' : pack.2.k = pack.1 := by
    simpa [pack] using hkEq
  have hk' : sc.k ≤ bound := by
    simpa [pack, sc, hkEq'] using hk_base
  have hdict' : Counting.dictLen sc.atlas.dict ≤ bound := by
    simpa [pack, sc, bound] using hdict_base
  have hε0' : (0 : Core.Q) ≤ sc.atlas.epsilon := by
    simpa [pack, sc] using hε0_base
  have hε1' : sc.atlas.epsilon ≤ (1 : Core.Q) / 2 := by
    simpa [pack, sc] using hε1_base
  have hεInv' : sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    simpa [pack, sc] using hεInv_base
  have hcap := family_card_le_capacity (sc := sc)
  refine And.intro hfamily' (And.intro hk' (And.intro hdict'
    (And.intro hε0' (And.intro hε1' (And.intro hεInv' ?_)))))
  exact hcap

lemma scenarioFromAC0_with_bound_stepAB_summary_strong
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hBound : ThirdPartyFacts.AC0DepthBoundWitness params F hF) :
    let pack := scenarioFromAC0_with_bound params F hF hBound
    let sc := pack.2
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params)
    sc.family = F ∧
      sc.k ≤ bound ∧
      Counting.dictLen sc.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) ∧
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k
          (Nat.pow 2 params.n) sc.atlas.epsilon sc.hε0 sc.hε1 := by
  classical
  intro pack sc bound
  have hfamily := scenarioFromAC0_with_bound_family_eq
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hbounds_raw := scenarioFromAC0_with_bound_completeBounds_strong
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hbounds :
      pack.1 ≤ bound ∧
        Counting.dictLen pack.2.atlas.dict ≤ bound ∧
        (0 : Core.Q) ≤ pack.2.atlas.epsilon ∧
        pack.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
        pack.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    simpa [pack, bound] using hbounds_raw
  have hfamily' : sc.family = F := by
    simpa [pack, sc] using hfamily
  rcases hbounds with ⟨hk_base, hrest⟩
  rcases hrest with ⟨hdict_base, hrest⟩
  rcases hrest with ⟨hε0_base, hrest⟩
  rcases hrest with ⟨hε1_base, hεInv_base⟩
  have hkEq := scenarioFromAC0_with_bound_k_eq
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  have hkEq' : pack.2.k = pack.1 := by
    simpa [pack] using hkEq
  have hk' : sc.k ≤ bound := by
    simpa [pack, sc, hkEq'] using hk_base
  have hdict' : Counting.dictLen sc.atlas.dict ≤ bound := by
    simpa [pack, sc, bound] using hdict_base
  have hε0' : (0 : Core.Q) ≤ sc.atlas.epsilon := by
    simpa [pack, sc] using hε0_base
  have hε1' : sc.atlas.epsilon ≤ (1 : Core.Q) / 2 := by
    simpa [pack, sc] using hε1_base
  have hεInv' : sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    simpa [pack, sc] using hεInv_base
  have hcap := family_card_le_capacity (sc := sc)
  refine And.intro hfamily' (And.intro hk' (And.intro hdict'
    (And.intro hε0' (And.intro hε1' (And.intro hεInv' ?_)))))
  exact hcap

/--
  Локальные схемы обладают той же структурой: сценарий шага A автоматически
  удовлетворяет ёмкостной границе из шага B.
-/
lemma scenarioFromLocalCircuit_stepAB_summary
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    let pack := scenarioFromLocalCircuit params F hF
    let sc := pack.2
    let bound := Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2)
      + params.depth + 1))
    sc.family = F ∧
      sc.k ≤ bound ∧
      Counting.dictLen sc.atlas.dict ≤ bound ∧
      (0 : Core.Q) ≤ sc.atlas.epsilon ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
      sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) ∧
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k
          (Nat.pow 2 params.n) sc.atlas.epsilon sc.hε0 sc.hε1 :=
  by
    classical
    intro pack sc bound
    have hfamily := scenarioFromLocalCircuit_family_eq
      (params := params) (F := F) (hF := hF)
    have hbounds_raw := scenarioFromLocalCircuit_completeBounds
      (params := params) (F := F) (hF := hF)
    have hbounds :
        pack.1 ≤ bound ∧
          Counting.dictLen pack.2.atlas.dict ≤ bound ∧
          (0 : Core.Q) ≤ pack.2.atlas.epsilon ∧
          pack.2.atlas.epsilon ≤ (1 : Core.Q) / 2 ∧
          pack.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
      simpa [pack, bound] using hbounds_raw
    have hfamily' : sc.family = F := by
      simpa [pack, sc] using hfamily
    rcases hbounds with ⟨hk_base, hrest⟩
    rcases hrest with ⟨hdict_base, hrest⟩
    rcases hrest with ⟨hε0_base, hrest⟩
    rcases hrest with ⟨hε1_base, hεInv_base⟩
    have hkEq := scenarioFromLocalCircuit_k_eq
      (params := params) (F := F) (hF := hF)
    have hkEq' : pack.2.k = pack.1 := by
      simpa [pack] using hkEq
    have hk' : sc.k ≤ bound := by
      simpa [pack, sc, hkEq'] using hk_base
    have hdict' : Counting.dictLen sc.atlas.dict ≤ bound := by
      simpa [pack, sc, bound] using hdict_base
    have hε0' : (0 : Core.Q) ≤ sc.atlas.epsilon := by
      simpa [pack, sc] using hε0_base
    have hε1' : sc.atlas.epsilon ≤ (1 : Core.Q) / 2 := by
      simpa [pack, sc] using hε1_base
    have hεInv' : sc.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
      simpa [pack, sc] using hεInv_base
    have hcap := family_card_le_capacity (sc := sc)
    refine And.intro hfamily' (And.intro hk' (And.intro hdict'
      (And.intro hε0' (And.intro hε1' (And.intro hεInv' ?_)))))
    exact hcap

/--
  Удобная структура, упаковывающая численные параметры сценария SAL.
  Поле `budget` фиксирует универсальную границу на число листьев, а
  вспомогательные поля собирают совпадение семейства и оценку ошибки.
-/
structure ScenarioBudget (n : Nat) (F : Core.Family n) : Type where
  /-- Универсальная граница на число селекторов и длину словаря. -/
  budget : Nat
  /-- Ограниченный сценарий SAL для семейства `F`. -/
  scenario : BoundedAtlasScenario n
  /-- Совпадение семейства внутри сценария с исходным списком. -/
  family_eq : scenario.family = F
  /-- Число селекторов не превосходит `budget`. -/
  k_le_budget : scenario.k ≤ budget
  /-- Длина словаря также ограничена `budget`. -/
  dict_le_budget : Counting.dictLen scenario.atlas.dict ≤ budget
  /-- Дополнительная граница на погрешность `ε ≤ 1/(n+2)`. -/
  epsilon_le_inv : scenario.atlas.epsilon ≤ (1 : Core.Q) / (n + 2)

namespace ScenarioBudget

variable {n : Nat} {F : Core.Family n}

/-- Неотрицательность ошибки следует из самого ограниченного сценария. -/
lemma epsilon_nonneg (pack : ScenarioBudget n F) :
    (0 : Core.Q) ≤ pack.scenario.atlas.epsilon :=
  pack.scenario.hε0

/-- Условие `ε ≤ 1/2` также доступно напрямую из сценария. -/
lemma epsilon_le_half (pack : ScenarioBudget n F) :
    pack.scenario.atlas.epsilon ≤ (1 : Core.Q) / 2 :=
  pack.scenario.hε1

/-- Атлас, упакованный в паспорте сценария. -/
def atlas (pack : ScenarioBudget n F) : Core.Atlas n :=
  pack.scenario.atlas

end ScenarioBudget

/--
  Построение паспорта для сценария, полученного из AC⁰ shrinkage.
  Бюджет `2^{(\log_2(M+2))^{d+1}}` повторяет параметры multi-switching лемм.
-/
noncomputable def scenarioBudgetFromAC0
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsAC0 params F)
    (hSmall : ThirdPartyFacts.AC0SmallEnough params) :
    ScenarioBudget params.n F :=
  by
    classical
    let packData := scenarioFromAC0 params F hF hSmall
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong params)
    have summaryPack :=
      scenarioFromAC0_stepAB_summary_strong
        (params := params) (F := F) (hF := hF) (hSmall := hSmall)
    have hfamily_raw := summaryPack.1
    have hrest₁ := summaryPack.2
    have hk_raw := hrest₁.1
    have hrest₂ := hrest₁.2
    have hdict_raw := hrest₂.1
    have hrest₃ := hrest₂.2
    have _hε0_raw := hrest₃.1
    have hrest₄ := hrest₃.2
    have _hε_half_raw := hrest₄.1
    have hrest₅ := hrest₄.2
    have hε_inv_raw := hrest₅.1
    have hfamily' := hfamily_raw
    change packData.2.family = F at hfamily'
    have hk_pack := hk_raw
    change packData.2.k ≤ bound at hk_pack
    have hdict_pack := hdict_raw
    change Counting.dictLen packData.2.atlas.dict ≤ bound at hdict_pack
    have hε_inv := hε_inv_raw
    change packData.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) at hε_inv
    refine
      { budget := bound
        scenario := packData.2
        family_eq := hfamily'
        k_le_budget := hk_pack
        dict_le_budget := ?_
        epsilon_le_inv := ?_ }
    · exact hdict_pack
    · exact hε_inv

/--
  Паспортизованный сценарий для локальных схем: бюджет равен
  $2^{\ell (\log_2(M+2) + \text{depth} + 1)}$.
-/
noncomputable def scenarioBudgetFromLocal
    (params : ThirdPartyFacts.LocalCircuitParameters)
    (F : Core.Family params.n)
    (hF : ThirdPartyFacts.FamilyIsLocalCircuit params F) :
    ScenarioBudget params.n F :=
  by
    classical
    let packData := scenarioFromLocalCircuit params F hF
    let bound := Nat.pow 2 (params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1))
    have summaryPack :=
      scenarioFromLocalCircuit_stepAB_summary (params := params) (F := F) (hF := hF)
    have hfamily_raw := summaryPack.1
    have hrest₁ := summaryPack.2
    have hk_raw := hrest₁.1
    have hrest₂ := hrest₁.2
    have hdict_raw := hrest₂.1
    have hrest₃ := hrest₂.2
    have _hε0_raw := hrest₃.1
    have hrest₄ := hrest₃.2
    have _hε_half_raw := hrest₄.1
    have hrest₅ := hrest₄.2
    have hε_inv_raw := hrest₅.1
    have hfamily' := hfamily_raw
    change packData.2.family = F at hfamily'
    have hk_pack := hk_raw
    change packData.2.k ≤ bound at hk_pack
    have hdict_pack := hdict_raw
    change Counting.dictLen packData.2.atlas.dict ≤ bound at hdict_pack
    have hε_inv := hε_inv_raw
    change packData.2.atlas.epsilon ≤ (1 : Core.Q) / (params.n + 2) at hε_inv
    refine
      { budget := bound
        scenario := packData.2
        family_eq := hfamily'
        k_le_budget := hk_pack
        dict_le_budget := ?_
        epsilon_le_inv := ?_ }
    · exact hdict_pack
    · exact hε_inv

end LowerBounds
end Pnp3
