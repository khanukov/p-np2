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
Локализационный сертификат, извлекаемый через `ShrinkageCertificate.Provider`.
Эта вспомогательная функция пригодится, когда понадобятся не только численные
оценки, но и семантическое свойство локализованности функции `generalEval`.
-/
def localityCertificateOfProvidedCertificate
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    [ShrinkageWitness.ShrinkageCertificate.Provider
      (p := p) general generalEval] :
    LocalityCertificate (p := p) general generalEval :=
  let providedCertificate :=
    -- Извлекаем shrinkage-сертификат из typeclass-инстанса `Provider`.
    -- Это удобно для подключения будущих доказательных сертификатов без
    -- изменения интерфейса вызова.
    ShrinkageWitness.ShrinkageCertificate.provided
      (p := p) (general := general) (generalEval := generalEval)
  -- Переводим shrinkage-сертификат в локализационный, сохраняя семантическое
  -- утверждение о локализованности `generalEval`.
  providedCertificate.toLocalityCertificate

/--
Свидетель локализации, извлекаемый из shrinkage-сертификата через типкласс
`ShrinkageCertificate.Provider`.  Функция предназначена для будущих подключений
реальных сертификатов без изменения интерфейса.
По умолчанию инстанс доступен только для константной функции `fun _ => false`;
в реальных сценариях его следует заменить содержательным `Provider`.
-/
def localityWitnessOfProvidedCertificate
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    [ShrinkageWitness.ShrinkageCertificate.Provider
      (p := p) general generalEval] :
    LocalityWitness general :=
  localityWitnessOfCertificate
    (certificate :=
      ShrinkageWitness.ShrinkageCertificate.provided
        (p := p) (general := general) (generalEval := generalEval))

/--
Упаковка численного shrinkage-свидетеля в итоговый `LocalityWitness`.
Эта функция полезна, когда мы уже имеем `ShrinkageWitness` (например, из
рестрикции) и хотим быстро получить локальный решатель, не раскрывая
структуру `LocalityBlueprint`.
-/
def localityWitnessOfShrinkage
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (witness : ShrinkageWitness general) : LocalityWitness general :=
  witness.toWitness

/--
Текущий свидетель locality lift извлекается из shrinkage-свидетеля,
предоставленного через типкласс `ShrinkageWitness.Provider`.  По умолчанию
используется канонический свидетель, но его можно заменить, не меняя
интерфейса `locality_lift`.
-/
def localityWitness
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    LocalityWitness general :=
  localityWitnessOfShrinkage
    (ShrinkageWitness.provided (p := p) general)

/-!
## Леммы о witness, построенном из `ShrinkageWitness`

В отличие от варианта через `ShrinkageCertificate`, здесь мы работаем только
с числовой частью shrinkage-данных.  Эти леммы фиксируют, что конструктор
`localityWitnessOfShrinkage` буквально переупаковывает поля сводки.
-/

lemma localityWitnessOfShrinkage_alive
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (witness : ShrinkageWitness general) :
    (localityWitnessOfShrinkage (p := p) (general := general) witness).alive
      = witness.alive := by
  classical
  unfold localityWitnessOfShrinkage
  simp [ShrinkageWitness.toWitness, ShrinkageWitness.toBlueprint,
    ShrinkageSummary.toBlueprint, LocalityBlueprint.toWitness]

lemma localityWitnessOfShrinkage_testSet
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (witness : ShrinkageWitness general) :
    (localityWitnessOfShrinkage (p := p) (general := general) witness).testSet
      = witness.testSet := by
  classical
  unfold localityWitnessOfShrinkage
  simp [ShrinkageWitness.toWitness, ShrinkageWitness.toBlueprint,
    ShrinkageSummary.toBlueprint, LocalityBlueprint.toWitness]

lemma localityWitnessOfShrinkage_size
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (witness : ShrinkageWitness general) :
    (localityWitnessOfShrinkage (p := p) (general := general) witness).localParams.M
      = general.params.size * witness.summary.sizeMultiplier := by
  classical
  unfold localityWitnessOfShrinkage
  simp [ShrinkageWitness.toWitness, ShrinkageWitness.toBlueprint,
    ShrinkageSummary.toBlueprint, LocalityBlueprint.toWitness]

lemma localityWitnessOfShrinkage_locality
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (witness : ShrinkageWitness general) :
    (localityWitnessOfShrinkage (p := p) (general := general) witness).localParams.ℓ
      = witness.summary.locality := by
  classical
  unfold localityWitnessOfShrinkage
  simp [ShrinkageWitness.toWitness, ShrinkageWitness.toBlueprint,
    ShrinkageSummary.toBlueprint, LocalityBlueprint.toWitness]

lemma localityWitnessOfShrinkage_depth
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (witness : ShrinkageWitness general) :
    (localityWitnessOfShrinkage (p := p) (general := general) witness).localParams.depth
      = witness.summary.depth := by
  classical
  unfold localityWitnessOfShrinkage
  simp [ShrinkageWitness.toWitness, ShrinkageWitness.toBlueprint,
    ShrinkageSummary.toBlueprint, LocalityBlueprint.toWitness]

/-!
## Леммы о witness, выбранном через `Provider`

Эти утверждения удобны в дальнейшем: они позволяют использовать свойства
`ShrinkageWitness` напрямую, не раскрывая определение `localityWitness`.
-/

lemma localityWitness_alive_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).alive =
      (ShrinkageWitness.provided (p := p) general).alive := by
  classical
  simpa [localityWitness] using
    (localityWitnessOfShrinkage_alive
      (p := p) (general := general)
      (witness := ShrinkageWitness.provided (p := p) general))

lemma localityWitness_testSet_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).testSet =
      (ShrinkageWitness.provided (p := p) general).testSet := by
  classical
  simpa [localityWitness] using
    (localityWitnessOfShrinkage_testSet
      (p := p) (general := general)
      (witness := ShrinkageWitness.provided (p := p) general))

/-- Тест-набор locality-witness из `Provider` совпадает с `testSetOfAlive`. -/
lemma localityWitness_testSet_eq_testSetOfAlive_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).testSet
      = testSetOfAlive (ShrinkageWitness.provided (p := p) general).alive := by
  classical
  have htest :=
    localityWitness_testSet_provided (p := p) (general := general)
  have hcanon :=
    ShrinkageWitness.testSet_eq_testSetOfAlive
      (w := ShrinkageWitness.provided (p := p) general)
  simpa [htest] using hcanon

/-- Удобная оболочка: тест-набор `localityWitness` удовлетворяет polylog-границе. -/
lemma localityWitness_testSet_card_le_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).testSet.card
      ≤ polylogBudget (inputLen p) := by
  -- Поле `testSet_card_le` у `LocalityWitness` уже хранит нужную оценку.
  exact (localityWitness (p := p) general).testSet_card_le

lemma localityWitness_size_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).localParams.M =
      general.params.size *
        (ShrinkageWitness.provided (p := p) general).summary.sizeMultiplier := by
  classical
  simpa [localityWitness] using
    (localityWitnessOfShrinkage_size
      (p := p) (general := general)
      (witness := ShrinkageWitness.provided (p := p) general))

lemma localityWitness_locality_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).localParams.ℓ =
      (ShrinkageWitness.provided (p := p) general).summary.locality := by
  classical
  simpa [localityWitness] using
    (localityWitnessOfShrinkage_locality
      (p := p) (general := general)
      (witness := ShrinkageWitness.provided (p := p) general))

lemma localityWitness_depth_provided
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    [ShrinkageWitness.Provider (p := p) general] :
    (localityWitness (p := p) general).localParams.depth =
      (ShrinkageWitness.provided (p := p) general).summary.depth := by
  classical
  simpa [localityWitness] using
    (localityWitnessOfShrinkage_depth
      (p := p) (general := general)
      (witness := ShrinkageWitness.provided (p := p) general))

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
    (localityWitnessOfShrinkage (p := p)
        (ShrinkageWitness.canonical (p := p) general)).alive =
      canonicalAlive p := by
  classical
  -- Переформулируем утверждение через лемму о shrinkage-свидетеле.
  have h :=
    localityWitnessOfShrinkage_alive
      (p := p) (general := general)
      (witness := ShrinkageWitness.canonical (p := p) general)
  simpa [ShrinkageWitness.canonical, canonicalSummary_alive] using h

/--
Тест-набор, возвращаемый консервативным свидетелем, совпадает с
`testSetOfAlive (canonicalAlive p)`.  Лемма облегчает проверку численных
границ, поскольку мощность тест-набора немедленно переписывается в `0`.
-/
lemma localityWitness_testSet_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitnessOfShrinkage (p := p)
        (ShrinkageWitness.canonical (p := p) general)).testSet =
      testSetOfAlive (canonicalAlive p) := by
  classical
  have h :=
    localityWitnessOfShrinkage_testSet
      (p := p) (general := general)
      (witness := ShrinkageWitness.canonical (p := p) general)
  simpa [ShrinkageWitness.canonical, canonicalSummary_testSet] using h

/--
Размер локального решателя в каноническом свидетеле равен размеру исходного
решателя, умноженному на `|T| + 1`.  В нашем консервативном варианте
`|T| = 0`, поэтому множитель равен `1`.
-/
lemma localityWitness_size_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitnessOfShrinkage (p := p)
        (ShrinkageWitness.canonical (p := p) general)).localParams.M =
        general.params.size *
          (ShrinkageWitness.canonical (p := p) general).sizeMultiplier := by
  classical
  have h :=
    localityWitnessOfShrinkage_size
      (p := p) (general := general)
      (witness := ShrinkageWitness.canonical (p := p) general)
  simpa using h

/--
Локальность канонического свидетеля действительно равна `0`, поскольку живых
координат нет.  Это прямое следствие предыдущей леммы про `alive`.
-/
lemma localityWitness_locality_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitnessOfShrinkage (p := p)
        (ShrinkageWitness.canonical (p := p) general)).localParams.ℓ = 0 := by
  classical
  have h :=
    localityWitnessOfShrinkage_locality
      (p := p) (general := general)
      (witness := ShrinkageWitness.canonical (p := p) general)
  simpa [ShrinkageWitness.canonical, canonicalSummary_locality, card_canonicalAlive] using h

/--
Глубина локального решателя в базовом свидетельстве совпадает с глубиной
исходного решателя.  Это гарантирует, что текущая реализация не ухудшает
параметры, и служит ориентиром при сравнении с будущим shrinkage-доказательством.
-/
lemma localityWitness_depth_canonical
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p) :
    (localityWitnessOfShrinkage (p := p)
        (ShrinkageWitness.canonical (p := p) general)).localParams.depth =
      general.params.depth := by
  classical
  have h :=
    localityWitnessOfShrinkage_depth
      (p := p) (general := general)
      (witness := ShrinkageWitness.canonical (p := p) general)
  simpa [ShrinkageWitness.canonical, canonicalSummary_depth] using h

end LocalityLift
end Facts
