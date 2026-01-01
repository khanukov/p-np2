import LowerBounds.AntiChecker_Partial
import LowerBounds.LB_Formulas
import Models.Model_PartialMCSP

/-!
  pnp3/LowerBounds/LB_Formulas_Core_Partial.lean

  Каркас нижней оценки для формул AC⁰ над Partial MCSP.

  Это partial‑версия файла `LB_Formulas_Core.lean`: мы используем
  античекер из `AntiChecker_Partial.lean`, но остальная логика
  (SAL + Covering‑Power) совпадает с legacy‑аргументом.
-/
namespace Pnp3
namespace LowerBounds

open Classical
open Models

/--
  Основное ядро шага C (Partial MCSP):
  если существует малый AC⁰‑решатель Partial MCSP,
  античекер предоставляет семейство `Y`, которое слишком велико
  для SAL‑сценария. Это противоречит Covering‑Power.
-/
theorem LB_Formulas_core_partial
  {p : Models.GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  (hF_all : ThirdPartyFacts.FamilyIsAC0 solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  classical
  obtain ⟨F, Y, T, hWitness⟩ :=
    antiChecker_exists_testset_partial (solver := solver) hF_all
  classical
  -- Раскрываем обозначения, возвращённые античекером.
  dsimp only at hWitness
  set Fsolver : Core.Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
  obtain ⟨hF, hrest⟩ := hWitness
  set scWitness :=
    (scenarioFromAC0
        (params := solver.params.ac0) (F := Fsolver) (hF := hF)).2
  set Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  set Tsolver : Finset (Core.BitVec solver.params.ac0.n) :=
    solver.params.same_n.symm ▸ T
  rcases hrest with
    ⟨hYsubset, _hScenarioLarge, _hTBound, hApprox, hTestLarge⟩
  -- Используем тестовую версию критерия: атлас не может покрыть большое семейство.
  refine
    no_bounded_atlas_on_testset_of_large_family
      (sc := scWitness) (T := Tsolver) (Y := Ysolver)
      ?subset ?approx ?large
  · -- Подмножество напрямую приходит из античекера.
    exact hYsubset
  · -- Каждая функция из `Y` согласуется с объединением словаря вне `T`.
    exact hApprox
  · -- Мощность `Y` превосходит тестовую ёмкость, поэтому покрытие невозможно.
    exact hTestLarge

end LowerBounds
end Pnp3
