import Core.BooleanBasics
import Core.SAL_Core
import LowerBounds.LB_Formulas
import ThirdPartyFacts.LeafBudget

/-!
  pnp3/Tests/LB_Smoke_Scenario.lean

  Небольшая дымовая проверка: строим игрушечный объект `Shrinkage` и
  убеждаемся, что `scenarioFromShrinkage` корректно извлекает сценарий
  ограниченного атласа (вместе с числом `k`).  Тест не пытается оценивать
  конкретные параметры, его цель — убедиться, что модули "склеиваются"
  между собой.
-/

namespace Pnp3
namespace Tests

open Core
open LowerBounds
open ThirdPartyFacts

noncomputable section

/-- Подкуб, содержащий весь {0,1}¹. -/
def βAll : Subcube 1 := fun _ => none

/-- Тривиальное PDT: один лист, покрывающий весь куб. -/
def trivialTree : PDT 1 := PDT.leaf βAll

/-- Константная функция `false` на одном бите. -/
def f₀ : Core.BitVec 1 → Bool := fun _ => false

/-- Shrinkage с единственным листом и нулевой ошибкой. -/
def trivialShrinkage : Shrinkage 1 :=
by
  classical
  refine
    { F := [f₀]
      t := 0
      ε := 0
      tree := trivialTree
      depth_le := by
        -- Глубина листа равна нулю, потому условие выполнено автоматически.
        simp [trivialTree, PDT.depth]
      Rsel := fun _ => []
      Rsel_sub := by
        intro f β hf hβ
        -- Пустой список листьев: предположение `β ∈ []` невозможно.
        simpa using hβ
      err_le := ?err } <;> intro f hf
  · -- В семействе лишь функция `f₀`, для неё ошибка равна нулю.
    have hf' : f = f₀ := by
      simpa using hf
    subst hf'
    have hzero : Core.errU f₀ ([] : List (Subcube 1)) = 0 := by
      change Core.errU (fun _ : Core.BitVec 1 => false) [] = 0
      simpa using (Core.errU_false_nil (n := 1))
    simpa [hzero]

/-- Общий PDT, полученный из тривиального shrinkage. -/
def trivialCommonPDT : Core.CommonPDT 1 [f₀] :=
  Core.shrinkage_to_commonPDT trivialShrinkage

@[simp] lemma trivialCommonPDT_selectors_f₀ :
    trivialCommonPDT.selectors f₀ = [] := by
  classical
  change trivialShrinkage.Rsel f₀ = []
  simp [trivialShrinkage]

private lemma trivialCommonPDT_hlen
    (f : Core.BitVec 1 → Bool) (hf : f ∈ [f₀]) :
    ((trivialCommonPDT.selectors f).dedup).length ≤ 0 :=
by
  classical
  have hf' : f = f₀ := by simpa using hf
  subst hf'
  simpa [trivialCommonPDT_selectors_f₀] using (Nat.zero_le 0)

@[simp] lemma trivialCommonPDT_epsilon :
    trivialCommonPDT.epsilon = (0 : Core.Q) := by
  classical
  change trivialShrinkage.ε = 0
  simp [trivialShrinkage]

private lemma trivialCommonPDT_epsilon_nonneg :
    (0 : Core.Q) ≤ trivialCommonPDT.epsilon :=
by
  have : (0 : Core.Q) ≤ 0 := by norm_num
  simpa [trivialCommonPDT_epsilon] using this

private lemma trivialCommonPDT_epsilon_le_half :
    trivialCommonPDT.epsilon ≤ (1 : Core.Q) / 2 :=
by
  have : (0 : Core.Q) ≤ (1 : Core.Q) / 2 := by norm_num
  simpa [trivialCommonPDT_epsilon] using this

/-- Готовый сценарий, полученный из тривиального общего PDT. -/
def trivialScenarioCommon : BoundedAtlasScenario 1 :=
  LowerBounds.BoundedAtlasScenario.ofCommonPDT
    (n := 1)
    (F := [f₀])
    (C := trivialCommonPDT)
    0
    (by
      intro f hf
      exact trivialCommonPDT_hlen f hf)
    trivialCommonPDT_epsilon_nonneg
    trivialCommonPDT_epsilon_le_half

/--
  Дымовая проверка: убеждаемся, что автоматический переход
  `scenarioFromShrinkage` не теряет информацию об исходном семействе
  и корректно фиксирует параметры атласа.  Для игрушечного shrinkage
  мы явно строим свидетельство «пустой список листьев».
-/
theorem scenarioFromShrinkage_smoke :
    (LowerBounds.scenarioFromShrinkage
      (S := trivialShrinkage)
      (by simp [trivialShrinkage])
      (by simp [trivialShrinkage])).2.family = [f₀] ∧
    (LowerBounds.scenarioFromShrinkage
      (S := trivialShrinkage)
      (by simp [trivialShrinkage])
      (by simp [trivialShrinkage])).2.atlas.epsilon = 0 ∧
    ∃ S : List (Subcube 1),
      S = [] ∧
      S.length ≤ (LowerBounds.scenarioFromShrinkage
        (S := trivialShrinkage)
        (by simp [trivialShrinkage])
        (by simp [trivialShrinkage])).1 ∧
      Core.listSubset S (LowerBounds.scenarioFromShrinkage
        (S := trivialShrinkage)
        (by simp [trivialShrinkage])
        (by simp [trivialShrinkage])).2.atlas.dict ∧
      Core.errU f₀ S = 0 :=
by
  classical
  set result :=
    LowerBounds.scenarioFromShrinkage
      (S := trivialShrinkage)
      (by simp [trivialShrinkage])
      (by simp [trivialShrinkage])
  have hFamily : result.2.family = [f₀] := by
    simpa [result]
      using
        (LowerBounds.scenarioFromShrinkage_family_eq
          (S := trivialShrinkage)
          (hε0 := by simp [trivialShrinkage])
          (hε1 := by simp [trivialShrinkage]))
  have hEps : result.2.atlas.epsilon = 0 := by
    simpa [result, trivialShrinkage]
      using
        (LowerBounds.scenarioFromShrinkage_epsilon_eq
          (S := trivialShrinkage)
          (hε0 := by simp [trivialShrinkage])
          (hε1 := by simp [trivialShrinkage]))
  have hWitness :
      ∃ S : List (Subcube 1),
        S = [] ∧
        S.length ≤ result.1 ∧
        Core.listSubset S result.2.atlas.dict ∧
        Core.errU f₀ S = 0 := by
    refine ⟨[], rfl, ?_, ?_, ?_⟩
    ·
      have hnonneg : 0 ≤ result.1 := Nat.zero_le _
      simpa [result]
        using hnonneg
    ·
      simpa [result]
        using (Core.listSubset_nil (ys := result.2.atlas.dict))
    ·
      change Core.errU (fun _ : Core.BitVec 1 => false) [] = 0
      simpa using (Core.errU_false_nil (n := 1))
  exact And.intro hFamily (And.intro hEps hWitness)

/--
  Та же проверка, но через новый интерфейс `ofCommonPDT`: стартуем с общего
  PDT, извлечённого из shrinkage, и убеждаемся, что построенный сценарий
  совпадает с ожидаемыми параметрами.
-/
lemma scenarioFromCommonPDT_smoke :
    let sc := trivialScenarioCommon
    sc.family = [f₀] ∧ sc.atlas.epsilon = 0 ∧ sc.k = 0 ∧
      ∃ S : List (Subcube 1),
        S = [] ∧
        Core.listSubset S sc.atlas.dict ∧
        Core.errU f₀ S = 0 :=
by
  classical
  set sc := trivialScenarioCommon
  have hfam : sc.family = [f₀] := by
    -- Конструкция `trivialScenarioCommon` фиксирует семейство `[f₀]`.
    simp [sc, trivialScenarioCommon, LowerBounds.BoundedAtlasScenario.ofCommonPDT]
  have heps : sc.atlas.epsilon = 0 := by
    -- Ошибка равна ε исходного shrinkage, то есть нулю.
    simp [sc, trivialScenarioCommon, LowerBounds.BoundedAtlasScenario.ofCommonPDT,
      Core.CommonPDT.toAtlas, Core.Atlas.ofPDT, trivialCommonPDT_epsilon]
  have hk : sc.k = 0 := by
    -- При построении сценария мы явно указали `k = 0`.
    simp [sc, trivialScenarioCommon, LowerBounds.BoundedAtlasScenario.ofCommonPDT]
  have hsubset : Core.listSubset ([] : List (Subcube 1)) sc.atlas.dict := by
    -- Пустой набор листьев всегда является подсписком.
    simp [sc, trivialScenarioCommon, Core.listSubset_nil,
      LowerBounds.BoundedAtlasScenario.ofCommonPDT]
  have herr : Core.errU f₀ ([] : List (Subcube 1)) = 0 := by
    -- При отсутствии выбранных листьев ошибка обнуляется.
    change Core.errU (fun _ : Core.BitVec 1 => false) [] = 0
    simpa using (Core.errU_false_nil (n := 1))
  exact And.intro hfam (And.intro heps (And.intro hk ⟨[], rfl, hsubset, herr⟩))

/--
  Новая лемма `scenarioFromCommonPDT_k_le_pow` даёт ожидаемую границу на `k`
  для тривиального примера: значение `k = 0` не превосходит `2^0`.
-/
lemma scenarioFromCommonPDT_k_le_pow_smoke :
    (LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := trivialCommonPDT)
        (hε0 := trivialCommonPDT_epsilon_nonneg)
        (hε1 := trivialCommonPDT_epsilon_le_half)).1
      ≤ Nat.pow 2 trivialCommonPDT.depthBound :=
by
  classical
  simpa [trivialCommonPDT, trivialShrinkage, Core.Shrinkage.commonPDT_depthBound]
    using
      LowerBounds.scenarioFromCommonPDT_k_le_pow
        (n := 1) (F := [f₀]) (C := trivialCommonPDT)
        (hε0 := trivialCommonPDT_epsilon_nonneg)
        (hε1 := trivialCommonPDT_epsilon_le_half)

/--
  Проверка новой конструкции `scenarioFromCommonPDT`: получаем сценарий из
  тривиального общего PDT и убеждаемся, что семейство и ошибка совпадают с
  ожидаемыми значениями.  Возвращённый параметр `k` (в данном примере равный 1)
  допустим: пустой список листьев удовлетворяет требуемым ограничениям.
-/
lemma scenarioFromCommonPDT_sigma_smoke :
    (LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := trivialCommonPDT)
        (hε0 := trivialCommonPDT_epsilon_nonneg)
        (hε1 := trivialCommonPDT_epsilon_le_half)).2.family = [f₀] ∧
    (LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := trivialCommonPDT)
        (hε0 := trivialCommonPDT_epsilon_nonneg)
        (hε1 := trivialCommonPDT_epsilon_le_half)).2.atlas.epsilon = 0 ∧
    ∃ S : List (Subcube 1),
      S = [] ∧
      S.length ≤ (LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := trivialCommonPDT)
        (hε0 := trivialCommonPDT_epsilon_nonneg)
        (hε1 := trivialCommonPDT_epsilon_le_half)).1 ∧
      Core.listSubset S (LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := trivialCommonPDT)
        (hε0 := trivialCommonPDT_epsilon_nonneg)
        (hε1 := trivialCommonPDT_epsilon_le_half)).2.atlas.dict ∧
      Core.errU f₀ S = 0 :=
by
  classical
  set result :=
    LowerBounds.scenarioFromCommonPDT
      (n := 1) (F := [f₀]) (C := trivialCommonPDT)
      (hε0 := trivialCommonPDT_epsilon_nonneg)
      (hε1 := trivialCommonPDT_epsilon_le_half)
    with hresult
  have hfam : result.2.family = [f₀] := by
    simpa [hresult]
      using
        (LowerBounds.scenarioFromCommonPDT_family
          (n := 1) (F := [f₀]) (C := trivialCommonPDT)
          (hε0 := trivialCommonPDT_epsilon_nonneg)
          (hε1 := trivialCommonPDT_epsilon_le_half))
  have heps : result.2.atlas.epsilon = 0 := by
    simpa [hresult, trivialCommonPDT_epsilon]
      using
        (LowerBounds.scenarioFromCommonPDT_epsilon
          (n := 1) (F := [f₀]) (C := trivialCommonPDT)
          (hε0 := trivialCommonPDT_epsilon_nonneg)
          (hε1 := trivialCommonPDT_epsilon_le_half))
  refine And.intro ?hfam' (And.intro ?heps' ?hwit)
  · simpa [hresult] using hfam
  · simpa [hresult] using heps
  · refine ⟨[], rfl, ?hlen, ?hsubset, ?herr⟩
    ·
      have hnonneg : 0 ≤ result.1 := Nat.zero_le _
      simpa [hresult] using hnonneg
    ·
      simpa [hresult, Core.listSubset_nil]
    · change Core.errU (fun _ : Core.BitVec 1 => false) [] = 0
      simpa using (Core.errU_false_nil (n := 1))

end

end Tests
end Pnp3
