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
      Rsel_sub := ?subset
      err_le := ?err } <;> intro f hf
  · -- Пустой список всегда является подсписком словаря.
    simp [Core.listSubset_nil, trivialTree, PDT.leaves]
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

end

end Tests
end Pnp3
