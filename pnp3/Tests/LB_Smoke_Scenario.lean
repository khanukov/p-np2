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
  let result :=
    LowerBounds.scenarioFromShrinkage
      (S := trivialShrinkage)
      (by simp [trivialShrinkage])
      (by simp [trivialShrinkage])
  have hFamily : result.2.family = [f₀] := by
    unfold result
    simp [LowerBounds.scenarioFromShrinkage,
      LowerBounds.BoundedAtlasScenario.ofShrinkage, trivialShrinkage,
      Core.Atlas.fromShrinkage, Core.Atlas.ofPDT]
  have hEps : result.2.atlas.epsilon = 0 := by
    unfold result
    simp [LowerBounds.scenarioFromShrinkage,
      LowerBounds.BoundedAtlasScenario.ofShrinkage, trivialShrinkage,
      Core.Atlas.fromShrinkage, Core.Atlas.ofPDT]
  have hWitness :
      ∃ S : List (Subcube 1),
        S = [] ∧
        S.length ≤ result.1 ∧
        Core.listSubset S result.2.atlas.dict ∧
        Core.errU f₀ S = 0 := by
    refine ⟨[], rfl, ?_, ?_, ?_⟩
    · simp
    · simp [Core.listSubset_nil]
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
    let C := Core.shrinkage_to_commonPDT trivialShrinkage
    let sc :=
      LowerBounds.BoundedAtlasScenario.ofCommonPDT
        (n := 1)
        (F := [f₀])
        (C := C)
        0
        (by
          intro f hf
          have hf' : f = f₀ := by simpa using hf
          subst hf'
          simp [C, trivialShrinkage])
        (by
          simpa [C, trivialShrinkage])
        (by
          simpa [C, trivialShrinkage] using
            (show (0 : Core.Q) ≤ (1 : Core.Q) / 2 by norm_num))
    sc.family = [f₀] ∧ sc.atlas.epsilon = 0 ∧ sc.k = 0 ∧
      ∃ S : List (Subcube 1),
        S = [] ∧
        Core.listSubset S sc.atlas.dict ∧
        Core.errU f₀ S = 0 :=
by
  classical
  intro C sc
  refine And.intro ?hfam (And.intro ?heps (And.intro ?hk ?hwit))
  · simp [sc]
  · simp [sc, C, trivialShrinkage]
  · simp [sc]
  · refine ⟨[], rfl, ?_, ?_⟩
    · simp [sc, Core.listSubset_nil]
    ·
      change Core.errU (fun _ : Core.BitVec 1 => false) [] = 0
      simpa using (Core.errU_false_nil (n := 1))

/--
  Новая лемма `scenarioFromCommonPDT_k_le_pow` даёт ожидаемую границу на `k`
  для тривиального примера: значение `k = 0` не превосходит `2^0`.
-/
lemma scenarioFromCommonPDT_k_le_pow_smoke :
    let C := Core.shrinkage_to_commonPDT trivialShrinkage
    (LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := C)
        (hε0 := by
          simpa [C, trivialShrinkage])
        (hε1 := by
          simpa [C, trivialShrinkage] using
            (show (0 : Core.Q) ≤ (1 : Core.Q) / 2 by norm_num))).1
      ≤ Nat.pow 2 C.depthBound :=
by
  classical
  intro C
  simpa [C, trivialShrinkage]
    using
      LowerBounds.scenarioFromCommonPDT_k_le_pow
        (n := 1) (F := [f₀]) (C := C)
        (hε0 := by
          simpa [C, trivialShrinkage])
        (hε1 := by
          simpa [C, trivialShrinkage] using
            (show (0 : Core.Q) ≤ (1 : Core.Q) / 2 by norm_num))

/--
  Проверка новой конструкции `scenarioFromCommonPDT`: получаем сценарий из
  тривиального общего PDT и убеждаемся, что семейство и ошибка совпадают с
  ожидаемыми значениями.  Возвращённый параметр `k` (в данном примере равный 1)
  допустим: пустой список листьев удовлетворяет требуемым ограничениям.
-/
lemma scenarioFromCommonPDT_sigma_smoke :
    let C := Core.shrinkage_to_commonPDT trivialShrinkage
    let result :=
      LowerBounds.scenarioFromCommonPDT
        (n := 1) (F := [f₀]) (C := C)
        (hε0 := by
          simpa [C, trivialShrinkage])
        (hε1 := by
          simpa [C, trivialShrinkage] using
            (show (0 : Core.Q) ≤ (1 : Core.Q) / 2 by norm_num))
    result.2.family = [f₀] ∧ result.2.atlas.epsilon = 0 ∧
      ∃ S : List (Subcube 1),
        S = [] ∧
        S.length ≤ result.1 ∧
        Core.listSubset S result.2.atlas.dict ∧
        Core.errU f₀ S = 0 :=
by
  classical
  intro C result
  obtain ⟨k, sc⟩ := result
  refine And.intro ?hfam (And.intro ?heps ?hwit)
  · simp [result, C, trivialShrinkage]
  · simp [result, C, trivialShrinkage]
  · refine ⟨[], rfl, ?hlen, ?hsubset, ?herr⟩
    ·
      have hk : 0 ≤ k := Nat.zero_le _
      simpa [List.length_nil] using hk
    · simp [result, C, trivialShrinkage, Core.listSubset_nil]
    · change Core.errU (fun _ : Core.BitVec 1 => false) [] = 0
      simpa using (Core.errU_false_nil (n := 1))

end

end Tests
end Pnp3
