import LowerBounds.AntiChecker
import LowerBounds.LB_Formulas
import Models.Model_GapMCSP

/-!
  pnp3/LowerBounds/LB_LocalCircuits.lean

  Аналог ядра нижней оценки для локальных схем.  Мы повторяем аргумент из
  `LB_Formulas_Core`: античекер предоставляет большое конечное семейство,
  которое невозможно обслужить ограниченным SAL-сценарием.  Все внешние
  тонкости (конкретные параметры локальности, построение античекера)
  скрываются за интерфейсом `SmallLocalCircuitSolver` и
  `antiChecker_exists_large_Y_local`.
-/

namespace Pnp3
namespace LowerBounds

open Classical
open Models

/--
  Противоречие для локальных схем: гипотеза о существовании малого решателя
  GapMCSP приводит к семье `Y`, превосходящей ёмкость предоставленного
  SAL-сценария.  Значит, такой решатель не может существовать.
-/
theorem LB_LocalCircuits_core
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) : False := by
  classical
  obtain ⟨F, Y, hWitness⟩ := antiChecker_exists_large_Y_local (p := p) solver
  classical
  dsimp only at hWitness
  set Fsolver : Core.Family solver.params.n := solver.same_n.symm ▸ F
  set scWitness := (scenarioFromLocalCircuit (params := solver.params) Fsolver).2
  set Ysolver : Finset (Core.BitVec solver.params.n → Bool) :=
    solver.same_n.symm ▸ Y
  rcases hWitness with ⟨hYsubset, hYlarge⟩
  refine
    no_bounded_atlas_of_large_family (sc := scWitness) (Y := Ysolver)
      ?_ ?_
  ·
    simpa [Ysolver, scWitness] using hYsubset
  ·
    simpa [Ysolver, scWitness] using hYlarge

end LowerBounds
end Pnp3

