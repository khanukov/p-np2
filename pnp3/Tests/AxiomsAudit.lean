import Magnification.FinalResult
import Tests.BridgeLocalityRegression
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/Tests/AxiomsAudit.lean

  Тест-аудит: выводим список аксиом, от которых зависят ключевые теоремы.
  Этот файл компилируется вместе с проектом, чтобы случайные зависимости
  (например, от неожиданных внешних аксиом) были заметны сразу.
-/

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification

-- Итоговые утверждения (формульная сепарация).
#print axioms NP_not_subset_PpolyFormula_final
#print axioms NP_not_subset_PpolyFormula_final_of_formulaCertificate
#print axioms NP_not_subset_PpolyFormula_final_of_default_formulaCertificate
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas_default

-- Мост от нижних оценок к `NP ⊄ PpolyFormula`.
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas_with_formulaizer
#print axioms NP_not_subset_PpolyReal_from_partial_formulas
#print axioms NP_not_subset_PpolyReal_from_partial_formulas_trivial
#print axioms OPS_trigger_formulas_partial_of_provider
#print axioms OPS_trigger_formulas_partial_of_provider_formula_separation_strict
#print axioms NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer
#print axioms P_ne_NP_final_of_formulaCertificate
#print axioms P_ne_NP_final_of_default_formulaCertificate

-- Regression checks for I-1 / I-3 readiness.
#print axioms Tests.i1_trivial_realization_available
#print axioms Tests.i1_trivial_ppolyreal_route_no_manual_embed
#print axioms Tests.i3_certificate_auto_no_manual_hCardHalf
#print axioms Tests.i4_final_wiring_of_formulaCertificate
#print axioms Tests.i4_final_wiring_of_default_formulaCertificate

-- Проверяем, что ключевые shrinkage-леммы не тянут лишних аксиом.
-- Это именно те утверждения, которые в TODO помечены для перепроверки.
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.shrinkage_for_localCircuit

-- Проверяем новый constructive I-4 трек через явный multi-switching witness.
#print axioms LowerBounds.noSmallAC0Solver_partial_of_multiSwitching
#print axioms LowerBounds.noSmallAC0Solver_partial_of_multiSwitching_provider
#print axioms LowerBounds.LB_Formulas_core_partial_of_multiSwitching
#print axioms LowerBounds.LB_Formulas_core_partial_of_multiSwitching_provider
#print axioms LowerBounds.noSmallLocalCircuitSolver_partial_constructive
#print axioms LowerBounds.antiChecker_exists_testset_local_partial_constructive
