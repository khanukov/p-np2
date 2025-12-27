import Magnification.FinalResult
import Magnification.Bridge_to_Magnification
import Complexity.Interfaces

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
#print axioms P_ne_NP_final_general

-- Мост от нижних оценок к `NP ⊄ P/poly`.
#print axioms bridge_from_general_statement

-- Базовая логическая связка `NP ⊄ P/poly` + `P ⊆ P/poly` ⇒ `P ≠ NP`.
#print axioms P_ne_NP_of_nonuniform_separation
