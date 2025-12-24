import Facts.LocalityLift.Proof.Localization
import Facts.LocalityLift.Proof.ShrinkageWitness

/-!
## Полезные свойства консервативного свидетеля

Поскольку в текущей версии пакета мы всё ещё опираемся на канонический
шринкаж-сертификат (пустой тест-набор), разработчикам удобно иметь
"факты по умолчанию" о полученном свидетеле.  В частности, далее часто
возникает необходимость понять, какие именно координаты помечены как живые
и какой тест-набор экспортируется наружу.  Чтобы не раскручивать определения
каждый раз заново, мы собираем компактные леммы, позволяющие в два шага
получить нужные равенства.

Когда полноценное shrinkage-доказательство будет готово, эти вспомогательные
факты останутся полезными: они проверяют соответствие живых координат,
тест-набора и локального решателя, так что любые альтернативные сертификаты
обязаны удовлетворять тем же соотношениям.
-/

/-!
# Locality-lift witnesses

Этот модуль использует абстракцию `LocalityBlueprint`, объявленную в
`Proof/Blueprint.lean`, чтобы построить фактический свидетель локализации,
экспортируемый интерфейсом.  В текущей версии используется канонический
пустой чертёж; позже он будет заменён результатами шринкаж-анализа.
-/

namespace Facts
namespace LocalityLift

/--
Свидетель локализации, полученный из полноценного shrinkage-сертификата.
Как только будет доказано настоящее утверждение о shrinkage, этот конструктор
станет основным способом получить `LocalityWitness` без каких-либо заглушек.
-/
def localityWitnessOfCertificate
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    LocalityWitness general :=
  certificate.toLocalityCertificate.toWitness

/--
Консервативный свидетель локальности получается из канонического
shrinkage-сертификата с константной функцией.  Как только появится
содержательный результат, достаточно будет заменить этот вызов на реальный
сертификат, не меняя остальной код.
-/
def localityWitness
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    LocalityWitness general :=
  localityWitnessOfCertificate (generalEval := fun _ => false)
    (ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general)

/--
Для произвольного shrinkage-сертификата живые координаты в итоговом свидетеле
совпадают с теми, что перечислены в числовой сводке.  Это прямое следствие
того, что конструктор `LocalityWitness` просто перепаковывает поля чертежа.
-/
lemma localityWitnessOfCertificate_alive
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    (localityWitnessOfCertificate (p := p) (general := general)
        (generalEval := generalEval) certificate).alive
      = certificate.summary.alive := by
  classical
  unfold localityWitnessOfCertificate
  simp [LocalityCertificate.toWitness, LocalityCertificate.toBlueprint,
    LocalityBlueprint.toWitness, ShrinkageSummary.toBlueprint]

/--
Аналогичное утверждение для тест-набора: он именно тот, что присутствует в
сводке.  Лемма избавляет от необходимости вручную раскрывать определения
`testSet_eq` при анализе свидетеля.
-/
lemma localityWitnessOfCertificate_testSet
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    (localityWitnessOfCertificate (p := p) (general := general)
        (generalEval := generalEval) certificate).testSet
      = certificate.summary.testSet := by
  classical
  unfold localityWitnessOfCertificate
  simp [LocalityCertificate.toWitness, LocalityCertificate.toBlueprint,
    LocalityBlueprint.toWitness, ShrinkageSummary.toBlueprint]

/--
Из предыдущих лемм немедленно следует, что итоговый тест-набор совпадает
с «каноническим» набором, построенным из живых координат рестрикции.
-/
lemma localityWitnessOfCertificate_testSetOfAlive
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    (localityWitnessOfCertificate (p := p) (general := general)
        (generalEval := generalEval) certificate).testSet
      = certificate.restriction.testSet := by
  classical
  have h := localityWitnessOfCertificate_testSet
    (certificate := certificate) (general := general)
    (generalEval := generalEval)
  -- Переписываем числовую сводку через рестрикцию.
  have hsummary :=
    ShrinkageWitness.ShrinkageCertificate.summary_testSet_eq_restriction'
      (certificate := certificate)
  exact h.trans hsummary

/--
Размер локального решателя определяется множителем `sizeMultiplier` из
числовой сводки.  Конструкция `LocalityBlueprint` просто домножает исходный
размер на этот множитель, поэтому равенство получается сразу из определения.
-/
lemma localityWitnessOfCertificate_size
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    (localityWitnessOfCertificate (p := p) (general := general)
        (generalEval := generalEval) certificate).localParams.M
      = general.params.size * certificate.summary.sizeMultiplier := by
  classical
  unfold localityWitnessOfCertificate
  simp [LocalityCertificate.toWitness, LocalityCertificate.toBlueprint,
    LocalityBlueprint.toWitness, ShrinkageSummary.toBlueprint]

/--
Локальность итогового решателя буквально копирует соответствующее поле из
`ShrinkageSummary`.
-/
lemma localityWitnessOfCertificate_locality
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    (localityWitnessOfCertificate (p := p) (general := general)
        (generalEval := generalEval) certificate).localParams.ℓ
      = certificate.summary.locality := by
  classical
  unfold localityWitnessOfCertificate
  simp [LocalityCertificate.toWitness, LocalityCertificate.toBlueprint,
    LocalityBlueprint.toWitness, ShrinkageSummary.toBlueprint]

/--
Глубина локального решателя также совпадает с числовой глубиной из сводки.
-/
lemma localityWitnessOfCertificate_depth
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : ShrinkageWitness.ShrinkageCertificate general generalEval) :
    (localityWitnessOfCertificate (p := p) (general := general)
        (generalEval := generalEval) certificate).localParams.depth
      = certificate.summary.depth := by
  classical
  unfold localityWitnessOfCertificate
  simp [LocalityCertificate.toWitness, LocalityCertificate.toBlueprint,
    LocalityBlueprint.toWitness, ShrinkageSummary.toBlueprint]

/--
В консервативной реализации множество живых координат совпадает с
`canonicalAlive`.  Мы выделяем эту лемму отдельно, чтобы не приходилось каждый
раз раскрывать определения канонического сертификата и чертежа.
-/
lemma localityWitness_alive_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitness (p := p) general).alive = canonicalAlive p := by
  classical
  -- Переформулируем утверждение через универсальную лемму и канонический сертификат.
  have hsummary :
      (ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general).summary =
        canonicalSummary (p := p) general := rfl
  have h :=
    localityWitnessOfCertificate_alive
      (certificate := ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general)
      (general := general) (generalEval := fun _ => false)
  simpa [localityWitness, localityWitnessOfCertificate, hsummary]
    using h

/--
Тест-набор, возвращаемый консервативным свидетелем, совпадает с
`testSetOfAlive (canonicalAlive p)`.  Лемма облегчает проверку численных
границ, поскольку мощность тест-набора немедленно переписывается в `0`.
-/
lemma localityWitness_testSet_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitness (p := p) general).testSet =
      testSetOfAlive (canonicalAlive p) := by
  classical
  have hsummary :
      (ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general).summary =
        canonicalSummary (p := p) general := rfl
  have h :=
    localityWitnessOfCertificate_testSet
      (certificate := ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general)
      (general := general) (generalEval := fun _ => false)
  simpa [localityWitness, localityWitnessOfCertificate, hsummary]
    using h

/--
Размер локального решателя в каноническом свидетеле равен размеру исходного
решателя, умноженному на `|T| + 1`.  В нашем консервативном варианте
`|T| = 0`, поэтому множитель равен `1`.
-/
lemma localityWitness_size_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitness (p := p) general).localParams.M =
        general.params.size *
          (ShrinkageWitness.ShrinkageCertificate.canonicalCertificate
            (p := p) general).sizeMultiplier := by
  classical
  have h :=
    localityWitnessOfCertificate_size
      (certificate := ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general)
      (general := general) (generalEval := fun _ => false)
  simpa [localityWitness, localityWitnessOfCertificate] using h

/--
Локальность канонического свидетеля действительно равна `0`, поскольку живых
координат нет.  Это прямое следствие предыдущей леммы про `alive`.
-/
lemma localityWitness_locality_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitness (p := p) general).localParams.ℓ = 0 := by
  classical
  have hsummary :
      (ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general).summary =
        canonicalSummary (p := p) general := rfl
  have h :=
    localityWitnessOfCertificate_locality
      (certificate := ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general)
      (general := general) (generalEval := fun _ => false)
  simpa [localityWitness, localityWitnessOfCertificate, hsummary, card_canonicalAlive]
    using h

/--
Глубина локального решателя в базовом свидетельстве совпадает с глубиной
исходного решателя.  Это гарантирует, что текущая реализация не ухудшает
параметры, и служит ориентиром при сравнении с будущим shrinkage-доказательством.
-/
lemma localityWitness_depth_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitness (p := p) general).localParams.depth =
      general.params.depth := by
  classical
  have hsummary :
      (ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general).summary =
        canonicalSummary (p := p) general := rfl
  have h :=
    localityWitnessOfCertificate_depth
      (certificate := ShrinkageWitness.ShrinkageCertificate.canonicalCertificate (p := p) general)
      (general := general) (generalEval := fun _ => false)
  simpa [localityWitness, localityWitnessOfCertificate, hsummary]
    using h

end LocalityLift
end Facts
