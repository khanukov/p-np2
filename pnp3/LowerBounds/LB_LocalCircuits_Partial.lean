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
  rcases antiChecker_largeY_certificate_local_partial (solver := solver) hF_all with
    ⟨sc, Y, hYsubset, hYlarge⟩
  exact no_bounded_atlas_of_large_family (sc := sc) (Y := Y) hYsubset hYlarge

/--
  Witness-first local-circuits core theorem.
-/
theorem LB_LocalCircuits_core_partial_witness
  {p : Models.GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
  (wF_all : ThirdPartyFacts.LocalCircuitWitness solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) : False := by
  exact noSmallLocalCircuitSolver_partial_witness (solver := solver) wF_all

/--
  Realized variant of `LB_LocalCircuits_core_partial`.
  The contradiction still follows from the existing anti-checker core, while
  carrying an explicit circuit implementation in the solver wrapper.
-/
theorem LB_LocalCircuits_core_partial_realized
  {p : Models.GapPartialMCSPParams} (solver : RealizedSmallLocalCircuitSolver_Partial p)
  (wF_all : ThirdPartyFacts.LocalCircuitWitness solver.base.params.params
    (Counting.allFunctionsFamily solver.base.params.params.n)) : False := by
  exact LB_LocalCircuits_core_partial_witness (p := p) (solver := solver.base) wF_all

end LowerBounds
end Pnp3
