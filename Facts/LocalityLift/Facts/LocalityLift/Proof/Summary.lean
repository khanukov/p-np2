import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.TestSet
import Facts.LocalityLift.Proof.TestSetExtraction

/-!
# Сжатое резюме параметров, получаемых из shrinkage

Чтобы постепенно приблизиться к настоящему доказательству locality lift,
удобно отделить «сырой» набор численных данных, извлечённых из будущего
shrinkage-свидетеля, от финальной упаковки в структуру `LocalityBlueprint`.

В этом модуле вводится структура `ShrinkageSummary`, которая фиксирует
полезные параметры (тест-набор, множитель размера, локальность, глубину) и
содержит ровно те неравенства, которые в итоге понадобятся для сборки
`LocalityBlueprint`.  Такой слой абстракции позволит в дальнейшем заменить
консервативный конструктор на реальную обработку shrinkage-сертификата без
переписывания кода в `Proof/Blueprint.lean` и `Proof/Witness.lean`.
-/

namespace Facts
namespace LocalityLift

open scoped Classical
open Finset

/--
`ShrinkageSummary general` описывает численные параметры, которые должны быть
получены из shrinkage-анализа для общего решателя `general`.  Здесь пока
собраны только те поля, которые непосредственно участвуют в проверке
локализационных ограничений (мощность тест-набора, множитель размера,
локальность, глубина).  Семантические гарантии (например, корректность
локального решателя) будут добавлены позднее, когда появятся определения
самих схем.
-/
structure ShrinkageSummary
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) : Type where
  /-- Набор живых координат, возвращаемых shrinkage-свидетелем. -/
  alive : Finset (Fin (inputLen p))
  /-- Полилогарифмическая граница на мощность `alive`. -/
  alive_card_le : alive.card ≤ polylogBudget (inputLen p)
  /-- Конечный тест-набор входов, соответствующий `alive`. -/
  testSet : Finset (BitVec (inputLen p))
  /-- Тест-набор действительно построен из живых координат. -/
  testSet_eq : testSet = testSetOfAlive alive
  /-- Полилогарифмическая граница на мощность тест-набора. -/
  testSet_card_le : testSet.card ≤ polylogBudget (inputLen p)
  /-- Множитель, контролирующий рост размера схемы. -/
  sizeMultiplier : Nat
  /-- Условие `sizeMultiplier ≤ |T| + 1`, достаточное для оценки размера. -/
  sizeMultiplier_le : sizeMultiplier ≤ testSet.card.succ
  /-- Локальность будущего решателя. -/
  locality : Nat
  /-- Локальность совпадает с мощностью `alive`. -/
  locality_eq : locality = alive.card
  /-- Ограничение локальности тем же бюджетом, что и у тест-набора. -/
  locality_le : locality ≤ polylogBudget (inputLen p)
  /-- Глубина локального решателя. -/
  depth : Nat
  /-- Глубина не превосходит глубину исходной схемы. -/
  depth_le : depth ≤ general.params.depth
  /--
  Численное условие "малости" для локального решателя, получаемого из
  данной сводки.  Это требование обеспечивает корректность применения
  локального античекера в основной цепочке доказательств.
  -/
  smallEnough :
    LocalCircuitSmallEnough
      { n := inputLen p
        , M := general.params.size * sizeMultiplier
        , ℓ := locality
        , depth := depth }

lemma sizeMultiplier_le_alive_card_succ
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    summary.sizeMultiplier ≤ summary.alive.card.succ := by
  classical
  have h := summary.sizeMultiplier_le
  -- Переписываем мощность тест-набора через `alive`.
  have hcard : summary.testSet.card = summary.alive.card := by
    simp [summary.testSet_eq]
  simpa [hcard] using h

@[simp] lemma testSet_card_le'
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    summary.testSet.card ≤ polylogBudget (inputLen p) :=
  summary.testSet_card_le

@[simp] lemma alive_card_le'
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    summary.alive.card ≤ polylogBudget (inputLen p) :=
  summary.alive_card_le

/--
Возвращает сводку shrinkage-параметров, построенную из конечного множества
живых координат.  Тест-набор формируется через `testSetOfAlive`, размерный
множитель фиксируется равным `alive.card.succ`, а локальность отождествляется
с мощностью `alive`.
-/
def summaryOfAlive
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p)))
    (alive_card_le : alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    ShrinkageSummary general := by
  classical
  refine
    { alive := alive
      , alive_card_le := alive_card_le
      , testSet := testSetOfAlive alive
      , testSet_eq := rfl
      , testSet_card_le := ?_
      , sizeMultiplier := alive.card.succ
      , sizeMultiplier_le := by
          simp [card_testSetOfAlive alive]
      , locality := alive.card
      , locality_eq := rfl
      , locality_le := alive_card_le
      , depth := general.params.depth
      , depth_le := le_rfl
      , smallEnough := by
          simpa using smallEnough }
  -- Через лемму `card_testSetOfAlive` мощность тест-набора совпадает с `alive.card`.
  simpa [card_testSetOfAlive alive] using alive_card_le

@[simp] lemma summaryOfAlive_sizeMultiplier
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p))) (hle : alive.card ≤ polylogBudget (inputLen p))
    (hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    (summaryOfAlive (p := p) general alive hle hsmall).sizeMultiplier = alive.card.succ := rfl

@[simp] lemma summaryOfAlive_testSet
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p))) (hle : alive.card ≤ polylogBudget (inputLen p))
    (hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    (summaryOfAlive (p := p) general alive hle hsmall).testSet = testSetOfAlive alive := rfl

@[simp] lemma summaryOfAlive_testSet_eq
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p))) (hle : alive.card ≤ polylogBudget (inputLen p))
    (hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    (summaryOfAlive (p := p) general alive hle hsmall).testSet_eq = rfl := rfl

@[simp] lemma summaryOfAlive_alive
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p))) (hle : alive.card ≤ polylogBudget (inputLen p))
    (hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    (summaryOfAlive (p := p) general alive hle hsmall).alive = alive := rfl

@[simp] lemma summaryOfAlive_locality
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p))) (hle : alive.card ≤ polylogBudget (inputLen p))
    (hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    (summaryOfAlive (p := p) general alive hle hsmall).locality = alive.card := rfl

@[simp] lemma summaryOfAlive_locality_eq
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (alive : Finset (Fin (inputLen p))) (hle : alive.card ≤ polylogBudget (inputLen p))
    (hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * alive.card.succ
          , ℓ := alive.card
          , depth := general.params.depth }) :
    (summaryOfAlive (p := p) general alive hle hsmall).locality_eq = rfl := rfl

/--
Консервативное резюме, построенное из пустого набора живых координат.
Пока у нас нет настоящего shrinkage-свидетеля, этого достаточно, чтобы
поддерживать конструктивный свидетель и проверять численные неравенства.
-/
def canonicalSummary
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    ShrinkageSummary general := by
  classical
  have hcard : (canonicalAlive p).card ≤ polylogBudget (inputLen p) := by
    have : (canonicalAlive p).card = 0 := card_canonicalAlive p
    -- Из `0 = card` достаточно получить `0 ≤ polylogBudget`.
    simp [this]
  have hsmall :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * (canonicalAlive p).card.succ
          , ℓ := (canonicalAlive p).card
          , depth := general.params.depth } := by
    -- Локальность равна нулю, поэтому условие "малости" тривиально.
    have hℓ : (canonicalAlive p).card = 0 := card_canonicalAlive p
    simpa [hℓ] using
      (localSmallEnough_of_zero
        { n := inputLen p
          , M := general.params.size * (canonicalAlive p).card.succ
          , ℓ := (canonicalAlive p).card
          , depth := general.params.depth } hℓ)
  exact summaryOfAlive (p := p) general (canonicalAlive p) hcard hsmall

@[simp] lemma canonicalSummary_testSet
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).testSet =
        testSetOfAlive (canonicalAlive p) := rfl

@[simp] lemma canonicalSummary_testSet_eq
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).testSet_eq = rfl := rfl

@[simp] lemma canonicalSummary_alive
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).alive = canonicalAlive p := rfl

@[simp] lemma canonicalSummary_sizeMultiplier
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).sizeMultiplier =
        (canonicalAlive p).card.succ := rfl

@[simp] lemma canonicalSummary_locality
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).locality = (canonicalAlive p).card := rfl

@[simp] lemma canonicalSummary_locality_eq
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).locality_eq = rfl := rfl

@[simp] lemma canonicalSummary_depth
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (canonicalSummary (p := p) general).depth = general.params.depth := rfl

end LocalityLift
end Facts
