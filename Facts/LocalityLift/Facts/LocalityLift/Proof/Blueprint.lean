import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.TestSetExtraction
import Facts.LocalityLift.Proof.Summary

/-!
# Конструктор свидетеля локализации

В модуле фиксируется промежуточное понятие *чертежа* (`LocalityBlueprint`).
Его удобно использовать при сборке конструктивного доказательства locality lift:
сначала формируем численные параметры и тест-набор, затем автоматически
получаем структуру `LocalityWitness`, которую требует интерфейс пакета.

Такое разбиение позволяет подключать более сложные источники данных
(например, настоящие shrinkage-свидетели) и поэтапно проверять отдельные
ограничения без копирования кода по упаковке параметров.
-/

namespace Facts
namespace LocalityLift

open scoped Classical
open Finset

/--
`LocalityWitness general` аккумулирует результат конструкции locality lift для
заданного общего решателя `general`.  В нём собраны тест-набор, параметры
локального решателя и четыре ключевые оценки, необходимые пайплайну
магнификации.
-/
structure LocalityWitness
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) : Type where
  /-- Coordinates that remain observable after the locality reduction. -/
  alive : Finset (Fin (inputLen p))
  /-- Polylogarithmic bound on `alive`. -/
  alive_card_le : alive.card ≤ polylogBudget (inputLen p)
  /-- Test set `T ⊆ {0,1}^n` extracted from the alive coordinates. -/
  testSet : Finset (BitVec (inputLen p))
  /-- The test set is literally `testSetOfAlive alive`. -/
  testSet_eq : testSet = testSetOfAlive alive
  /-- Cardinality bound `|T| ≤ polylogBudget`. -/
  testSet_card_le : testSet.card ≤ polylogBudget (inputLen p)
  /-- Parameters of the local solver specialised to `T`. -/
  localParams : LocalCircuitParameters
  /-- The local solver sees the same truth-table length. -/
  same_n : localParams.n = inputLen p
  /-- Size blow-up is at most linear in `|T| + 1`. -/
  size_le : localParams.M ≤ general.params.size * ((Finset.card testSet).succ)
  /-- Locality agrees with the number of alive coordinates. -/
  locality_eq_alive : localParams.ℓ = alive.card
  /-- Locality is bounded by the polylogarithmic budget. -/
  locality_le : localParams.ℓ ≤ polylogBudget (inputLen p)
  /-- The depth of the local solver does not exceed that of the general solver. -/
  depth_le : localParams.depth ≤ general.params.depth

namespace LocalityWitness

/-- Преобразуем свидетель в оболочку локального решателя. -/
def toLocalSolver
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : LocalityWitness general) : SmallLocalCircuitSolver p :=
  { params := w.localParams
    same_n := w.same_n }

@[simp] lemma toLocalSolver_params
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : LocalityWitness general) :
    (w.toLocalSolver).params = w.localParams := rfl

end LocalityWitness

/--
`LocalityBlueprint general` хранит весь численный атрибут локального решателя,
необходимый для построения `LocalityWitness general`.  Отдельные поля
соответствуют требованиям интерфейса locality lift: размер тест-набора,
границы на размер, локальность и глубину.
-/
structure LocalityBlueprint
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) : Type where
  /-- Coordinates kept alive by the shrinkage witness. -/
  alive             : Finset (Fin (inputLen p))
  /-- Polylogarithmic bound on `alive`. -/
  alive_card_le     : alive.card ≤ polylogBudget (inputLen p)
  /-- Финитный тест-набор входов. -/
  testSet           : Finset (BitVec (inputLen p))
  /-- Тест-набор действительно построен из `alive`. -/
  testSet_eq        : testSet = testSetOfAlive alive
  /-- Ограничение на мощность тест-набора. -/
  card_le_polylog   : testSet.card ≤ polylogBudget (inputLen p)
  /-- Размер локального решателя (с потенциальной "надбавкой"). -/
  localSize         : Nat
  /-- Связь размера локального решателя с размером исходного. -/
  size_le           : localSize ≤ general.params.size * (testSet.card.succ)
  /-- Локальность (число наблюдаемых координат). -/
  locality          : Nat
  /-- Локальность совпадает с числом живых координат. -/
  locality_eq_alive : locality = alive.card
  /-- Ограничение локальности тем же бюджетом, что и мощность `T`. -/
  locality_le       : locality ≤ polylogBudget (inputLen p)
  /-- Глубина локального решателя. -/
  depth             : Nat
  /-- Глубина не превосходит глубину исходного решателя. -/
  depth_le          : depth ≤ general.params.depth

namespace ShrinkageSummary

/--
Преобразуем сводку shrinkage-параметров в «чертёж» локального решателя.
Числовые ограничения автоматически транслируются в соответствующие поля
`LocalityBlueprint`.  Этот конструктор будет использоваться и в текущем
консервативном свидетеле, и в будущей реализации, опирающейся на реальный
shrinkage.
-/
def toBlueprint
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    LocalityBlueprint general := by
  classical
  refine
    { alive := summary.alive
      , alive_card_le := summary.alive_card_le
      , testSet := summary.testSet
      , testSet_eq := summary.testSet_eq
      , card_le_polylog := summary.testSet_card_le
      , localSize := general.params.size * summary.sizeMultiplier
      , size_le := ?_
      , locality := summary.locality
      , locality_eq_alive := by
          simpa using summary.locality_eq
      , locality_le := summary.locality_le
      , depth := summary.depth
      , depth_le := summary.depth_le }
  -- Монотонность по второму множителю даёт нужную оценку размера.
  exact (Nat.mul_le_mul_left _ summary.sizeMultiplier_le)

@[simp] lemma toBlueprint_testSet
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    (summary.toBlueprint).testSet = summary.testSet := rfl

@[simp] lemma toBlueprint_localSize
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    (summary.toBlueprint).localSize = general.params.size * summary.sizeMultiplier := rfl

@[simp] lemma toBlueprint_locality
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    (summary.toBlueprint).locality = summary.locality := rfl

@[simp] lemma toBlueprint_depth
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    (summary.toBlueprint).depth = summary.depth := rfl

end ShrinkageSummary

def LocalityBlueprint.toWitness
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (blueprint : LocalityBlueprint general) :
    LocalityWitness general := by
  classical
  refine
    { alive := blueprint.alive
      , alive_card_le := blueprint.alive_card_le
      , testSet := blueprint.testSet
      , testSet_eq := blueprint.testSet_eq
      , testSet_card_le := blueprint.card_le_polylog
      , localParams :=
          { n := inputLen p
            , M := blueprint.localSize
            , ℓ := blueprint.locality
            , depth := blueprint.depth }
      , same_n := rfl
      , size_le := by
          simpa using blueprint.size_le
      , locality_eq_alive := by
          simpa using blueprint.locality_eq_alive
      , locality_le := by
          simpa using blueprint.locality_le
      , depth_le := by
          simpa using blueprint.depth_le }

/--
Консервативный чертёж, основанный на одноточечном тест-наборе, строится через
`ShrinkageSummary`.  Это позволяет легко заменить реализацию на более сложную,
когда появится настоящий shrinkage-свидетель.
-/
def canonicalBlueprint
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    LocalityBlueprint general :=
  (canonicalSummary (p := p) general).toBlueprint

end LocalityLift
end Facts
