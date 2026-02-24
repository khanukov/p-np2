import LowerBounds.AntiChecker_Partial
import LowerBounds.LB_Formulas
import Models.Model_PartialMCSP

/-!
  pnp3/LowerBounds/LB_Formulas_Core_Partial.lean

  Каркас нижней оценки для формул AC⁰ над Partial MCSP.

  Это partial‑версия файла `LB_Formulas_Core.lean`: мы используем
  античекер из `AntiChecker_Partial.lean`, а основной маршрут шага C
  остаётся SAL + Covering‑Power.
-/
namespace Pnp3
namespace LowerBounds

open Classical
open Models

/-!
  Semantic (non-vacuous) Step-C contract:
  the contradiction premise is attached to each concrete solver via an
  explicit easy-family package (family + AC0 witness + cardinal lower bound).
-/

/-- Semantic core hypothesis for Partial Step-C. -/
def StepCCoreSemanticHypothesisPartial (p : Models.GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p, AC0EasyFamilyDataPartial solver.params.ac0 → False

/--
Semantic core theorem: direct elimination from the semantic Step-C hypothesis.
-/
theorem LB_Formulas_core_partial_semantic
  {p : Models.GapPartialMCSPParams}
  (hCore : StepCCoreSemanticHypothesisPartial p)
  (solver : SmallAC0Solver_Partial p)
  (easy : AC0EasyFamilyDataPartial solver.params.ac0) : False := by
  exact hCore solver easy

/--
Counting-core Step-C statement over an explicit "easy family" package.
-/
theorem LB_Formulas_core_partial_of_easyFamilyData
  {p : Models.GapPartialMCSPParams}
  (solver : SmallAC0Solver_Partial p)
  (easy : AC0EasyFamilyDataPartial solver.params.ac0) : False := by
  exact noSmallAC0Solver_partial_of_easyFamilyData (solver := solver) easy

/--
Constructive Step-C core over solver packages that already contain
family-level easy-data witnesses.
-/
theorem LB_Formulas_core_partial_constructive
  {p : Models.GapPartialMCSPParams}
  (solver : ConstructiveSmallAC0Solver_Partial p) : False := by
  exact noConstructiveSmallAC0Solver_partial (solver := solver)

/-- Core contradiction from direct syntactic easy-family hypotheses. -/
theorem LB_Formulas_core_partial_of_syntacticEasy
  {p : Models.GapPartialMCSPParams}
  (solver : SmallAC0Solver_Partial p)
  (hEasy :
    ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
      (AC0EasyFamily solver.params.ac0))
  (hComp : AC0CompressionHypothesis p) : False := by
  exact noSmallAC0Solver_partial_of_syntacticEasy
    (solver := solver) hEasy hComp

/--
  Основное ядро шага C (Partial MCSP):
  если существует малый AC⁰‑решатель Partial MCSP,
  получаем прямое противоречие через SAL/Covering-Power оценку
  (`noSmallAC0Solver_partial`).

  Ранее в этом месте использовался промежуточный anti-checker слой
  с экзистенциальными обёртками, что делало маршрут менее прозрачным.
  В текущем активном ядре этот слой убран: мы сразу работаем с прямым
  конструктивным противоречием.

  Поэтому в активном ядре шага C используется прямое доказательство
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
