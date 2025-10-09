import LowerBounds.AntiChecker
import LowerBounds.LB_Formulas
import Models.Model_GapMCSP

/-!
  pnp3/LowerBounds/LB_Formulas_Core.lean

  Каркас нижней оценки для формул AC⁰ над GapMCSP.  Мы используем
  античекер (шаг C) вместе с универсальными оценками (шаг B) и
  «клеем» SAL (шаг A), чтобы получить противоречие из гипотезы
  о существовании малого решателя.
-/
namespace Pnp3
namespace LowerBounds

open Classical
open Models

/--
  Основное ядро шага C: если существует малый AC⁰-решатель GapMCSP,
  то античекер предоставляет семейство `Y`, которое слишком велико для
  полученного SAL-сценария.  Это противоречит Covering-Power, значит,
  малый решатель невозможен.
-/
theorem LB_Formulas_core
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) : False := by
  classical
  obtain ⟨F, Y, T, hWitness⟩ := antiChecker_exists_testset (p := p) solver
  classical
  -- Раскрываем обозначения, возвращённые античекером.
  dsimp only at hWitness
  set Fsolver : Core.Family solver.ac0.n := solver.same_n.symm ▸ F
  set scWitness := (scenarioFromAC0 (params := solver.ac0) Fsolver).2
  set Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
    solver.same_n.symm ▸ Y
  set Tsolver : Finset (Core.BitVec solver.ac0.n) :=
    solver.same_n.symm ▸ T
  rcases hWitness with
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
