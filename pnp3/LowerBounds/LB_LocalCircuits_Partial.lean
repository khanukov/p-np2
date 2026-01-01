import LowerBounds.AntiChecker_Partial
import LowerBounds.LB_Formulas
import Models.Model_PartialMCSP

/-!
  pnp3/LowerBounds/LB_LocalCircuits_Partial.lean

  Partial‑версия ядра нижней оценки для локальных схем.
-/

namespace Pnp3
namespace LowerBounds

open Classical
open Models

theorem LB_LocalCircuits_core_partial
  {p : Models.GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
  (hF_all : ThirdPartyFacts.FamilyIsLocalCircuit solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) : False := by
  classical
  obtain ⟨F, Y, T, hWitness⟩ :=
    antiChecker_exists_testset_local_partial (p := p) solver hF_all
  classical
  dsimp only at hWitness
  set Fsolver : Core.Family solver.params.params.n := solver.params.same_n.symm ▸ F
  obtain ⟨hF, hrest⟩ := hWitness
  set scWitness :=
    (scenarioFromLocalCircuit (params := solver.params.params) (F := Fsolver) (hF := hF)).2
  set Ysolver : Finset (Core.BitVec solver.params.params.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  set Tsolver : Finset (Core.BitVec solver.params.params.n) :=
    solver.params.same_n.symm ▸ T
  rcases hrest with
    ⟨hYsubset, _hScenarioLarge, _hTBound, hApprox, hTestLarge⟩
  refine
    no_bounded_atlas_on_testset_of_large_family
      (sc := scWitness) (T := Tsolver) (Y := Ysolver)
      ?subset ?approx ?large
  · exact hYsubset
  · exact hApprox
  · exact hTestLarge

end LowerBounds
end Pnp3
