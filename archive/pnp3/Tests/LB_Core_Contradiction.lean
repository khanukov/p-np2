import LowerBounds.LB_Formulas_Core
import LowerBounds.LB_LocalCircuits
import Models.Model_GapMCSP

/-!
  pnp3/Tests/LB_Core_Contradiction.lean

  Небольшой дымовой тест, проверяющий, что ядра нижних оценок действительно
  устраняют гипотезу о существовании малого решателя.  Используем теоремы
  `LB_Formulas_core` и `LB_LocalCircuits_core`, чтобы показать, что соответствующие
  типы «малых решателей» пусты.  Это аккуратно фиксирует основной сценарий:
  любое конкретное предположение о существовании решателя приводит к `False`.
-/

namespace Pnp3
namespace Tests

open Pnp3 LowerBounds Models

/--
  Античекер и конвейер SAL ⇒ Covering-Power гарантируют, что не существует
  AC⁰-решателя заданных параметров.  Формулируем это как пустоту соответствующей
  структуры данных.
-/
theorem noSmallAC0Solver (p : GapMCSPParams) :
    IsEmpty (LowerBounds.SmallAC0Solver p) := by
  classical
  refine ⟨?_⟩
  intro solver
  exact (LowerBounds.LB_Formulas_core (p := p) solver).elim

/--
  Аналогичное утверждение для локальных схем: тип `SmallLocalCircuitSolver`
  пуст, поскольку ядро нижней оценки немедленно даёт противоречие.
-/
theorem noSmallLocalCircuitSolver (p : GapMCSPParams) :
    IsEmpty (LowerBounds.SmallLocalCircuitSolver p) := by
  classical
  refine ⟨?_⟩
  intro solver
  exact (LowerBounds.LB_LocalCircuits_core (p := p) solver).elim

end Tests
end Pnp3
