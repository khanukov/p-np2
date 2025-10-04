import Magnification.Bridge_to_Magnification
import Magnification.FinalResult
import Models.Model_GapMCSP
import Complexity.Interfaces

/-!
  pnp3/Tests/Magnification_Core_Contradiction.lean

  Дымовой тест для шага D: демонстрируем, что триггеры магнификации
  действительно устраняют гипотезы о малых решателях.  В отличие от
  тестов шага C, здесь мы подставляем любое положительное значение `δ`
  (или `κ`) и убеждаемся, что мост из `Bridge_to_Magnification` сразу
  даёт следствие `P ≠ NP`.
-/

namespace Pnp3
namespace Tests

open Magnification
open Models
open ComplexityInterfaces

/--
  Положительное `δ` влечёт `P ≠ NP` благодаря мосту из шага D.
-/
theorem formulas_trigger_forces_separation
  (p : GapMCSPParams) {δ : Rat} (hδ : (0 : Rat) < δ) :
  P_ne_NP :=
  P_ne_NP_from_formulas_bridge (p := p) (δ := δ) hδ

/--
  Общая гипотеза OPS также мгновенно даёт разделение `P` и `NP`.
-/
theorem general_trigger_forces_separation
  (p : GapMCSPParams) {ε : Rat} {statement : Prop}
  (h : Magnification.GeneralLowerBoundHypothesis p ε statement) :
  P_ne_NP :=
  P_ne_NP_from_general_bridge (p := p) (ε := ε) (statement := statement) h

/--
  Аналогичное утверждение для локальных схем с параметром `κ`.
-/
theorem local_trigger_forces_separation
  (p : GapMCSPParams) {κ : Nat} (hκ : 0 < κ) :
  P_ne_NP :=
  P_ne_NP_from_local_bridge (p := p) (κ := κ) hκ

/--
  Финальный sanity-check: готовый модуль `FinalResult` действительно выводит
  целевое утверждение `P ≠ NP`.
-/
theorem final_result_confirms_separation :
  P_ne_NP :=
  Magnification.P_ne_NP_final

end Tests
end Pnp3
