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
  получаем прямое противоречие через SAL/Covering-Power оценку
  (`noSmallAC0Solver_partial`).

  Исторически в этом месте использовался промежуточный anti-checker слой
  с экзистенциальными свидетелями (`F, Y, T`), выводимыми из `False.elim`.
  Такой путь логически корректен, но неконструктивен и плохо отражает
  математику: из уже доказанного противоречия извлекались «свидетели»,
  которые затем снова сводились к противоречию.

  Поэтому в активном ядре шага C мы используем прямое доказательство
  противоречия без промежуточных экзистенциальных обёрток.
-/
theorem LB_Formulas_core_partial
  {p : Models.GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  (hF_all : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  exact noSmallAC0Solver_partial (solver := solver) (hF := hF_all)

/--
Constructive variant of the core AC0 lower-bound step:
an explicit multi-switching witness for the all-functions family is sufficient.
-/
theorem LB_Formulas_core_partial_of_multiSwitching
  {p : Models.GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  (hMS :
    ThirdPartyFacts.AC0MultiSwitchingWitness solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  exact LB_Formulas_core_partial (solver := solver) (hF_all := ⟨hMS.base⟩)

/-- Typeclass-driven constructive core step via multi-switching provider. -/
theorem LB_Formulas_core_partial_of_multiSwitching_provider
  {p : Models.GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  [hMS :
    ThirdPartyFacts.AC0MultiSwitchingWitnessProvider
      solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n)] : False := by
  exact LB_Formulas_core_partial_of_multiSwitching (solver := solver) hMS.witness

/-- Default constructive core step via all-functions multi-switching package. -/
theorem LB_Formulas_core_partial_of_default_multiSwitching
  {p : Models.GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  [hMS : AllFunctionsAC0MultiSwitchingWitness solver.params.ac0] : False := by
  exact LB_Formulas_core_partial_of_multiSwitching (solver := solver) hMS.witness

end LowerBounds
end Pnp3
