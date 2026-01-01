import Magnification.Bridge_to_Magnification_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces
import ThirdPartyFacts.Hirahara2022

/-!
  # pnp3/Magnification/FinalResult.lean

  Финальный шаг текущего конвейера: фиксируем конкретные параметры для
  задачи `PartialMCSP` и выводим заявленное разделение классов `P` и `NP`.

  На предыдущих этапах были построены:

  * мост `P_ne_NP_from_partial_formulas`, который из любого положительного
    параметра `δ` немедленно даёт `P ≠ NP` (опираясь на partial-античекер и
    Covering-Power);
  * внешние факты `shrinkage_for_AC0`, `leaf_budget_from_shrinkage` и
    доказанная внутри проекта теорема `antiChecker_exists_large_Y`
    (а также `antiChecker_exists_testset`), обеспечивающие отсутствие малых AC⁰
    решателей для фиксированного набора параметров.

  Здесь мы выбираем конкретный набор параметров (для определённости
  берём минимальные нетривиальные значения) и подставляем `δ = 1`.
  Такой выбор полностью устраивает аксиомы шага C и триггер шага D,
  а значит финальный вывод `P ≠ NP` получается одной строкой.

  Замечание: античекер и shrinkage-факты уже оформлены как теоремы, но их
  гипотезы требуют явных свидетельств (`FamilyIsAC0`/`FamilyIsLocalCircuit`).
  Это делает вывод формально корректным, однако «полностью автономный» вариант
  появится после конструктивного построения этих свидетельств.  При этом
  финальная строка не изменится: изменится лишь источник входных данных.
-/

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/--
  Конкретный набор параметров `PartialMCSP`, который удовлетворяет условию
  `sYES + 1 ≤ sNO` и базовому требованию `8 ≤ n`.  Для определённости
  фиксируем `n = 8`, порог малых схем `sYES = 1` и порог больших схем
  `sNO = 3`.
-/
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8
  sYES := 1
  sNO := 3
  gap_ok := by decide
  n_large := by decide

/-!
  Финальный вывод текущей цепочки: из наличия положительного `δ`
  (конкретно `δ = 1`) и построенного ранее моста следует `P ≠ NP`.

  Этот результат служит sanity-check для конвейера A → B → C → D:
  как только античекер и shrinkage будут формально доказаны, строка ниже
  мгновенно превратится в полноценное разделение `P` и `NP`.
-/
/--
  В финальном файле явно фиксируем внешнюю аксиому NP-трудности Partial MCSP.
  Это обновляет «выходной слой» проекта до новой частичной версии задачи и
  даёт явную точку ссылки для дальнейшей интеграции в магнификационный
  конвейер.
-/
theorem partial_mcsp_np_hard_witness :
    ∃ p : GapPartialMCSPParams,
      Complexity.Is_NP_Hard (gapPartialMCSP_Language p) :=
  ThirdPartyFacts.PartialMCSP_is_NP_Hard

/--
  Финальный вывод для Partial MCSP: используем формульный мост для
  фиксированного набора partial‑параметров.
-/
theorem P_ne_NP_final
    (hF_all : ∀ loc : LowerBounds.SmallLocalCircuitSolver_Partial
      canonicalPartialParams,
      ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
        (Counting.allFunctionsFamily loc.params.params.n)) : P_ne_NP := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    P_ne_NP_from_partial_formulas
      (p := canonicalPartialParams) (δ := (1 : Rat)) hδ hF_all

end Magnification
end Pnp3
