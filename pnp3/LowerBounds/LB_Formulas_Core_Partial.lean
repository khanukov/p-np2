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
  rcases antiChecker_largeY_certificate_partial (solver := solver) hF_all with
    ⟨sc, Y, hYsubset, hYlarge⟩
  exact no_bounded_atlas_of_large_family (sc := sc) (Y := Y) hYsubset hYlarge

end LowerBounds
end Pnp3
