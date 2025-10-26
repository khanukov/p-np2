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

@[simp] lemma summary_testSet_eq_restriction
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (w : ShrinkageWitness general) :
    w.summary.testSet = w.restriction.testSet := by
  classical
  -- Обе части совпадают с `testSetOfAlive w.alive`.
  have hleft : w.summary.testSet = testSetOfAlive w.alive := by
    simpa [w.summary_alive] using w.summary.testSet_eq
  have hright : w.restriction.testSet = testSetOfAlive w.alive := by
    simpa [Restriction.testSet, w.restriction_alive]
  exact hleft.trans hright.symm

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
  анализа.  Он согласуется с одноточечным тест-набором и хранит одиночную живую
  координату `0`.
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
          simpa [canonicalSummary_alive] }

lemma canonical_multiplexerBudget_linear
    {params : GapMCSPParams} (general : SmallGeneralCircuitSolver params) :
    (canonical general).multiplexerBudget =
        MultiplexerBudget.linear ((canonicalAlive params).card) := by
  classical
  simpa using canonicalSummary_budget_eq_linear (general := general)

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

namespace ShrinkageCertificate

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
      , stable := ?_ }
  intro x
  simp

end ShrinkageCertificate

end ShrinkageWitness

end LocalityLift
end Facts
