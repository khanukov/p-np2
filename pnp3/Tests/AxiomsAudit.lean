import Magnification.FinalResult
import Magnification.Bridge_to_Magnification_Partial
import Complexity.Interfaces
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
#print axioms NP_not_subset_PpolyFormula_final_with_provider
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas_default

-- Мост от нижних оценок к `NP ⊄ PpolyFormula`.
#print axioms NP_not_subset_PpolyFormula_from_partial_formulas_with_formulaizer
#print axioms OPS_trigger_formulas_partial_of_provider
#print axioms NP_not_subset_PpolyReal_from_partial_formulas_with_formulaizer

-- Проверяем, что ключевые shrinkage-леммы не тянут лишних аксиом.
-- Это именно те утверждения, которые в TODO помечены для перепроверки.
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.shrinkage_for_localCircuit
