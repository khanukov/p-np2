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

-- Итоговые утверждения.
#print axioms P_ne_NP_final
#print axioms P_ne_NP_final_with_provider
#print axioms P_ne_NP_from_partial_formulas
#print axioms P_ne_NP_from_partial_formulas_default

-- Мост от нижних оценок к `NP ⊄ P/poly`.
#print axioms NP_not_subset_Ppoly_from_partial_formulas
#print axioms OPS_trigger_formulas_partial_of_structured_contra

-- Базовая логическая связка `NP ⊄ P/poly` + `P ⊆ P/poly` ⇒ `P ≠ NP`.
#print axioms P_ne_NP_of_nonuniform_separation

-- Проверяем, что ключевые shrinkage-леммы не тянут лишних аксиом.
-- Это именно те утверждения, которые в TODO помечены для перепроверки.
#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0
#print axioms ThirdPartyFacts.shrinkage_for_localCircuit
