import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.Arithmetic
import Facts.LocalityLift.Proof.Summary
import Facts.LocalityLift.Proof.TestSet
import Facts.LocalityLift.Proof.TestSetExtraction
import Facts.LocalityLift.Proof.Restriction
import Facts.LocalityLift.Proof.Localization
import Facts.LocalityLift.Proof.Blueprint
import Facts.LocalityLift.Proof.Builder

/-!
# Интерфейс shrinkage-свидетелей

Этот модуль формализует слой, связывающий будущие результаты о shrinkage с
числовыми структурами пакета.  Здесь мы фиксируем структуру `ShrinkageWitness`,
которая расширяет `ShrinkageSummary` дополнительными данными (набор живых
координат) и обеспечивает удобные преобразования к `LocalityBlueprint` и далее к
`LocalityWitness`.

Пока реального shrinkage-доказательства нет, мы предоставляем канонический
свидетель, построенный из одноточечного тест-набора.  Все определения
снабжены подробными комментариями, чтобы дальнейшая замена на содержательный
сертификат прошла безболезненно.
-/

namespace Facts
namespace LocalityLift

open scoped Classical
open Finset

/--
Шринкаж-свидетель хранит как числовую сводку (поля `ShrinkageSummary`), так и
конкретный набор живых координат.  В дальнейшем сюда добавятся семантические
условия (например, корректность частичного решающего дерева), однако уже сейчас
мы фиксируем связь локальности с мощностью `alive`.
-/
structure ShrinkageWitness
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    : Type extends ShrinkageSummary general where
  /-- Частичное назначение входных битов, делящее пространство на живые и замороженные
      координаты.  В классическом shrinkage-доказательстве такой объект получается
      из удачной рестрикции случайно выбранного подкуба. -/
  restriction : Restriction (inputLen p)
  /-- Рестрикция должна оставлять в точности те координаты, что перечислены в поле
      `alive` числового резюме.  Это связывает «семантические» данные с числовыми. -/
  restriction_alive : restriction.alive = alive

namespace ShrinkageWitness

/-- Сбрасываем дополнительные поля и получаем исходную сводку. -/
def summary
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) : ShrinkageSummary general :=
  w.toShrinkageSummary

@[simp] lemma summary_eq
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    w.summary = w.toShrinkageSummary := rfl

@[simp] lemma summary_testSet
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    (w.summary).testSet = w.testSet := rfl

@[simp] lemma summary_alive
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    (w.summary).alive = w.alive := rfl

@[simp] lemma summary_locality
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    (w.summary).locality = w.locality := rfl

/-!
## Строительство свидетеля из рестрикции

В полноценном shrinkage-доказательстве основным объектом является удачная
рестрикция входов.  По ней мы хотим автоматически сформировать числовую
сводку `ShrinkageSummary`, а затем соединить её с самой рестрикцией, чтобы
получить `ShrinkageWitness`.  Следующее определение фиксирует ровно эту
логику: если мы знаем, что `alive` у рестрикции мало и что будущий локальный
решатель удовлетворяет условию `SmallEnough`, то можем собрать свидетель
без дополнительных заглушек.
-/

/-- Построение `ShrinkageWitness` из явной рестрикции и числовых оценок. -/
def ofRestriction
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (restriction : Restriction (inputLen p))
    (alive_card_le : restriction.alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * restriction.alive.card.succ
          , ℓ := restriction.alive.card
          , depth := general.params.depth }) :
    ShrinkageWitness general := by
  classical
  refine
    { toShrinkageSummary :=
        summaryOfAlive (p := p) general restriction.alive alive_card_le ?_
      , restriction := restriction
      , restriction_alive := rfl }
  simpa using smallEnough

/-- В построении `ofRestriction` поле `restriction` совпадает с исходной рестрикцией. -/
@[simp] lemma ofRestriction_restriction
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (restriction : Restriction (inputLen p))
    (alive_card_le : restriction.alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * restriction.alive.card.succ
          , ℓ := restriction.alive.card
          , depth := general.params.depth }) :
    (ofRestriction (p := p) general restriction alive_card_le smallEnough).restriction =
      restriction := by
  rfl

/-- В построении `ofRestriction` поле `alive` совпадает с `restriction.alive`. -/
@[simp] lemma ofRestriction_alive
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (restriction : Restriction (inputLen p))
    (alive_card_le : restriction.alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * restriction.alive.card.succ
          , ℓ := restriction.alive.card
          , depth := general.params.depth }) :
    (ofRestriction (p := p) general restriction alive_card_le smallEnough).alive =
      restriction.alive := by
  classical
  simp [ofRestriction, summaryOfAlive]

/-- Тест-набор, собранный из рестрикции, совпадает с `testSetOfAlive`. -/
@[simp] lemma ofRestriction_testSet
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (restriction : Restriction (inputLen p))
    (alive_card_le : restriction.alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * restriction.alive.card.succ
          , ℓ := restriction.alive.card
          , depth := general.params.depth }) :
    (ofRestriction (p := p) general restriction alive_card_le smallEnough).testSet =
      testSetOfAlive restriction.alive := by
  classical
  simp [ofRestriction, summaryOfAlive]

@[simp] lemma summary_testSet_eq_restriction
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    w.summary.testSet = w.restriction.testSet := by
  classical
  -- Обе части совпадают с `testSetOfAlive w.alive`.
  have hleft : w.summary.testSet = testSetOfAlive w.alive := by
    simpa [w.summary_alive] using w.summary.testSet_eq
  have hright : w.restriction.testSet = testSetOfAlive w.alive := by
    simp [Restriction.testSet, w.restriction_alive]
  exact hleft.trans hright.symm

@[simp] lemma restriction_testSet_eq
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    w.restriction.testSet = w.testSet := by
  classical
  -- Используем уже доказанное равенство тест-набора с тест-набором сводки.
  -- Это полезно, когда shrinkage-свидетель поставляет конкретную рестрикцию,
  -- а в дальнейшем нужен тест-набор `T`.
  have h := summary_testSet_eq_restriction (w := w)
  -- По определению `ShrinkageWitness` тест-набор сводки совпадает с `w.testSet`.
  simpa using h.symm

/-- Тест-набор shrinkage-свидетеля всегда равен `testSetOfAlive w.alive`. -/
@[simp] lemma testSet_eq_testSetOfAlive
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    w.testSet = testSetOfAlive w.alive := by
  classical
  -- `testSet_eq` есть у сводки, а `summary_testSet` связывает её с `w.testSet`.
  have hsummary : w.summary.testSet = testSetOfAlive w.alive := by
    simpa [w.summary_alive] using w.summary.testSet_eq
  simpa [summary_testSet] using hsummary

/-- Мощность тест-набора, извлечённого из рестрикции shrinkage-свидетеля,
    ограничена тем же полилогарифмическим бюджетом. -/
lemma restriction_testSet_card_le
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    w.restriction.testSet.card ≤ polylogBudget (inputLen p) := by
  classical
  -- Переводим утверждение к тест-набору из числовой сводки.
  have hsummary : w.testSet.card ≤ polylogBudget (inputLen p) := by
    exact w.summary.testSet_card_le
  -- Поля `testSet` сводки и рестрикции совпадают.
  calc
    w.restriction.testSet.card = w.testSet.card := by
      simpa using congrArg Finset.card (restriction_testSet_eq (w := w))
    _ ≤ polylogBudget (inputLen p) := hsummary

/-- Переводим шринкаж-свидетель в чертёж локального решателя. -/
def toBlueprint
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    LocalityBlueprint general := w.summary.toBlueprint

@[simp] lemma toBlueprint_testSet
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    (w.toBlueprint).testSet = w.testSet := rfl

@[simp] lemma toBlueprint_locality
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    (w.toBlueprint).locality = w.locality := rfl

/-- И, наконец, получаем сам локальный решатель. -/
def toWitness
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    LocalityWitness general := w.toBlueprint.toWitness

/--
Дополнительные числовые данные, которые нам понадобятся для управления ростом
схемы при построении локального решателя: каждому шринкаж-свидетелю соответствует
линейный бюджет мультиплексоров.
-/
@[simp] def multiplexerBudget
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) : MultiplexerBudget :=
  w.summary.multiplexerBudget

/--
  Канонический свидетель, используемый до появления настоящего shrinkage-
  анализа.  Он согласуется с пустым тест-набором и хранит пустой набор
  живых координат.  Это упрощает численные оценки и гарантирует "малость"
  локального решателя по определению.
-/
def canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    ShrinkageWitness general := by
  classical
  refine
    { toShrinkageSummary := canonicalSummary (p := p) general
      , restriction :=
          Restriction.ofVector (canonicalAlive p)
            (zeroVector (inputLen p))
      , restriction_alive := by
          -- `summary.alive` сводки равняется `canonicalAlive`, поэтому условие тривиально.
          simp [canonicalSummary_alive] }

lemma canonical_multiplexerBudget_linear
    {params : GapMCSPParams} (general : SmallGeneralCircuitSolver params) :
    (canonical general).multiplexerBudget =
        MultiplexerBudget.linear ((canonicalAlive params).card) := by
  classical
  simpa using canonicalSummary_budget_eq_linear (general := general)

/-!
## Механизм подстановки shrinkage-свидетеля

Пока полноценный анализ не готов, мы используем канонический свидетель.
Однако важно оставить точку расширения: как только появится реальный
shrinkage-сертификат, мы сможем предоставить другой источник свидетелей,
не меняя интерфейс locality lift.  Для этого вводится типкласс `Provider`.
-/

/-- Типкласс, предоставляющий shrinkage-свидетель для конкретного решателя. -/
class Provider
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) : Type where
  /-- Свидетель shrinkage, связанный с данным решателем. -/
  witness : ShrinkageWitness general

/-- Текущий shrinkage-свидетель, выбранный через `Provider`. -/
def provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [Provider (p := p) general] : ShrinkageWitness general :=
  Provider.witness

/- No default global provider is installed; callers must supply an explicit
   `Provider` instance. -/

/-!
## Certificates with semantic data

Для полноценного доказательства locality lift недостаточно численных оценок:
нужно знать, что общая схема действительно не реагирует на изменение замороженных
координат.  Это свойство фиксируется в `ShrinkageCertificate`.  Сертификат
расширяет свидетель `ShrinkageWitness`, добавляя функцию, вычисляемую схемой,
и доказательство её стабильности относительно указанной рестрикции.
-/

/-- Полноценный шринкаж-сертификат хранит не только численные поля, но и
    информацию о стабилизации вычисления общего решателя. -/
structure ShrinkageCertificate
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool) : Type extends ShrinkageWitness general where
  /-- Применение рестрикции не меняет значение функции общего решателя. -/
  stable : ∀ x, generalEval (restriction.apply x) = generalEval x
  /-- Усиленный кардинальный контракт: живых координат не больше четверти входа. -/
  half_input_bound : restriction.alive.card ≤ inputLen p / 4

namespace ShrinkageCertificate

/-- Построение shrinkage-сертификата из рестрикции и доказательства стабильности. -/
def ofRestriction
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool)
    (restriction : Restriction (inputLen p))
    (alive_card_le : restriction.alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * restriction.alive.card.succ
          , ℓ := restriction.alive.card
          , depth := general.params.depth })
    (half_input_bound : restriction.alive.card ≤ inputLen p / 4)
    (stable : ∀ x, generalEval (restriction.apply x) = generalEval x) :
    ShrinkageCertificate (p := p) general generalEval := by
  classical
  let w := ShrinkageWitness.ofRestriction (p := p) general restriction alive_card_le smallEnough
  refine
    { toShrinkageSummary := w.toShrinkageSummary
      , restriction := restriction
      , restriction_alive := rfl
      , half_input_bound := half_input_bound
      , stable := stable }

/-- Поле `restriction` в `ofRestriction` совпадает с переданным объектом. -/
@[simp] lemma ofRestriction_restriction
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool)
    (restriction : Restriction (inputLen p))
    (alive_card_le : restriction.alive.card ≤ polylogBudget (inputLen p))
    (smallEnough :
      LocalCircuitSmallEnough
        { n := inputLen p
          , M := general.params.size * restriction.alive.card.succ
          , ℓ := restriction.alive.card
          , depth := general.params.depth })
    (half_input_bound : restriction.alive.card ≤ inputLen p / 4)
    (stable : ∀ x, generalEval (restriction.apply x) = generalEval x) :
    (ofRestriction (p := p) general generalEval restriction
        alive_card_le smallEnough half_input_bound stable).restriction = restriction := by
  rfl

/-- Любой шринкаж-сертификат даёт локализационный сертификат: значение функции
    зависит только от координат `alive`. -/
def toLocalityCertificate
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageCertificate (p := p) general generalEval) :
    LocalityCertificate (p := p) general generalEval := by
  classical
  refine
    { summary := certificate.summary
      , localized := ?_ }
  -- Стабильность относительно рестрикции непосредственно даёт локализацию.
  have hloc :=
    Restriction.localizedOn_of_stable (N := inputLen p) certificate.restriction
      certificate.stable
  -- Переписываем множество живых координат через сводку.
  simpa [certificate.restriction_alive] using hloc

@[simp] lemma toLocalityCertificate_summary
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageCertificate (p := p) general generalEval) :
    (certificate.toLocalityCertificate.summary) = certificate.summary := rfl

@[simp] lemma summary_testSet_eq_restriction'
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageCertificate (p := p) general generalEval) :
    certificate.summary.testSet = certificate.restriction.testSet :=
  summary_testSet_eq_restriction (w := certificate.toShrinkageWitness)

/-- Канонический сертификат: функция общего решателя берётся константной,
    что делает условие стабильности тривиальным.  Такой объект используется до
    тех пор, пока не появится настоящее shrinkage-доказательство. -/
def canonicalCertificate
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    ShrinkageCertificate (p := p) general (fun _ => false) := by
  classical
  -- Используем числовые данные и рестрикцию из канонического свидетеля.
  let w := canonical (p := p) general
  refine
    { toShrinkageSummary := w.toShrinkageSummary
      , restriction := w.restriction
      , restriction_alive := w.restriction_alive
      , half_input_bound := by
          simpa [w, canonical, card_canonicalAlive] using (Nat.zero_le (inputLen p / 4))
      , stable := ?_ }
  intro x
  simp

/-!
## Механизм подстановки shrinkage-сертификата

В отличие от численного `ShrinkageWitness`, полноценный сертификат зависит
от выбранной семантики `generalEval`.  Чтобы оставить точку расширения для
будущих подключений, вводим отдельный типкласс-провайдер.
-/

/-- Типкласс, предоставляющий shrinkage-сертификат для заданного `generalEval`. -/
class Provider
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool) : Type where
  /-- Сертификат shrinkage, связанный с данным решателем и оценкой. -/
  certificate : ShrinkageCertificate (p := p) general generalEval

/-- Текущий shrinkage-сертификат, выбранный через `Provider`. -/
def provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool)
    [Provider (p := p) general generalEval] :
    ShrinkageCertificate (p := p) general generalEval :=
  Provider.certificate

/--
Канонический источник сертификата для тривиальной оценки `fun _ => false`.
Этот инстанс полезен для примеров и тестов: он демонстрирует, как
использовать `Provider`, не требуя реального shrinkage-доказательства.
-/
instance (priority := 100) canonicalProvider
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    Provider (p := p) general (fun _ => false) :=
  ⟨canonicalCertificate (p := p) general⟩

end ShrinkageCertificate

end ShrinkageWitness

end LocalityLift
end Facts
