import Mathlib.Data.Nat.Basic
import Facts.LocalityLift.Proof.Localization
import Facts.LocalityLift.Proof.Summary

/-!
# Итеративные слои мультиплексоров и оценка размеров

Файл вводит вспомогательную структуру `MultiplexerBudget`, которая абстрактно
описвает, насколько сильно растёт размер схемы при последовательном добавлении
`k` управляющих битов (каждый реализуется в виде слоя ITE/мультиплексоров).

Пока мы ещё не построили собственно локальный решатель, но подготовили все
числовые границы.  Эти определения позволят в будущем чётко отделить «чистую»
арифметику от работы с конкретным графом схемы: как только будет реализован
модуль `Proof/Builder.lean`, отвечающий за трансформацию ДАГа, текущие леммы
станут непосредственными помощниками при доказательстве границ `M_loc` и
`depth_loc`.

Основная идея проста: если мы последовательно навешиваем на схему `k`
управляющих битов (каждый «делит» вычисление на два случая), то размер схемы
может вырасти не более чем линейно в `k+1`.  Именно это и отражено в полях
`MultiplexerBudget`.
-/

namespace Facts
namespace LocalityLift

/--
`MultiplexerBudget` фиксирует числовые ограничения, которые мы хотим получить
от слоя мультиплексоров: число управляющих битов `controls`, множитель размера
`sizeMultiplier` и доказательство, что этот множитель не превосходит `controls+1`.
В дальнейшем сюда можно добавить и ограничение на глубину (как только появится
конструктивное доказательство, что ITE в AC⁰ добавляет всего два слоя).
-/
structure MultiplexerBudget where
  /-- Число управляющих битов (будущая локальность). -/
  controls : Nat
  /-- Множитель, на который возрастает размер схемы. -/
  sizeMultiplier : Nat
  /-- Линейная оценка роста: `sizeMultiplier ≤ controls + 1`. -/
  size_le : sizeMultiplier ≤ controls.succ
deriving Repr

@[ext] lemma MultiplexerBudget.ext
    {A B : MultiplexerBudget}
    (hcontrols : A.controls = B.controls)
    (hsize : A.sizeMultiplier = B.sizeMultiplier) :
    A = B := by
  cases A
  cases B
  cases hcontrols
  cases hsize
  rfl

namespace MultiplexerBudget

/--
Линейный бюджет: рост размера не превышает `k + 1`.  Глубинный штраф пока не
учитывается, поскольку он потребует дополнительного анализа конструкции
схемы.  Тем не менее, большинство шагов proof-sketch опирается именно на это
линейное ограничение.
-/
@[simp] def linear (controls : Nat) : MultiplexerBudget :=
  { controls := controls
    , sizeMultiplier := controls.succ
    , size_le := by simp }

@[simp] lemma linear_controls (k : Nat) : (linear k).controls = k := rfl

@[simp] lemma linear_sizeMultiplier (k : Nat) :
    (linear k).sizeMultiplier = k.succ := rfl

lemma linear_size_le (k : Nat) :
    (linear k).sizeMultiplier ≤ k.succ := by
  exact (linear k).size_le

end MultiplexerBudget

/--
Любая сводка shrinkage-параметров автоматически задаёт линейный бюджет по
мультиплексорам: число управляющих битов равно `alive.card`, а множитель размера
ограничен не хуже, чем `alive.card + 1`.
-/
def ShrinkageSummary.multiplexerBudget
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) : MultiplexerBudget :=
  { controls := summary.alive.card
    , sizeMultiplier := summary.sizeMultiplier
    , size_le := sizeMultiplier_le_alive_card_succ summary }

@[simp] lemma multiplexerBudget_controls
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    (summary.multiplexerBudget).controls = summary.alive.card := rfl

@[simp] lemma multiplexerBudget_sizeMultiplier
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    (summary.multiplexerBudget).sizeMultiplier = summary.sizeMultiplier := rfl

lemma multiplexerBudget_linear_bound
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general) :
    summary.sizeMultiplier ≤ summary.alive.card.succ := by
  simpa using summary.multiplexerBudget.size_le

/-- В каноническом случае множитель размера совпадает с линейным бюджетом. -/
lemma canonicalSummary_budget_eq_linear
    {params : GapMCSPParams} (general : SmallGeneralCircuitSolver params) :
    (canonicalSummary general).multiplexerBudget =
        MultiplexerBudget.linear ((canonicalAlive params).card) := by
  classical
  refine MultiplexerBudget.ext ?_ ?_
  · simp [ShrinkageSummary.multiplexerBudget, MultiplexerBudget.linear]
  · simp [ShrinkageSummary.multiplexerBudget, MultiplexerBudget.linear]

/--
`LocalCircuitSkeleton` — промежуточная структура, соединяющая числовые данные
shrinkage-сводки с явным локальным эмулятором общего решателя.  Её удобно
использовать в дальнейших построениях: из одного объекта можно получить и
`LocalityCertificate`, и `LocalityWitness`, не раскрывая определения.
-/
structure LocalCircuitSkeleton
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool) : Type extends
        ShrinkageSummary general where
  /-- Локальный эмулятор, зависящий только от координат `alive`. -/
  evaluator : ({i // i ∈ alive} → Bool) → Bool
  /-- Локальный эмулятор согласуется с исходным решателем на любых входах. -/
  evaluator_agrees : ∀ x,
      evaluator (restrictToAlive alive x) = generalEval x

namespace LocalCircuitSkeleton

/-- Переводим скелет напрямую в `LocalityCertificate`: локализованность
возникает из равенства эмулятора и исходного решателя на всех входах. -/
def toCertificate
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (skeleton : LocalCircuitSkeleton (p := p) general generalEval) :
    LocalityCertificate (p := p) general generalEval := by
  classical
  refine
    { summary := skeleton.toShrinkageSummary
      , localized := ?_ }
  intro x y hxy
  have hx := skeleton.evaluator_agrees x
  have hy := skeleton.evaluator_agrees y
  have hrestrict :
      restrictToAlive skeleton.alive x = restrictToAlive skeleton.alive y := by
    funext i
    rcases i with ⟨i, hi⟩
    simpa [restrictToAlive] using hxy i hi
  have := congrArg skeleton.evaluator hrestrict
  simpa [hx, hy] using this

/-- Любой скелет напрямую порождает «чертёж» локального решателя. -/
@[simp] def toBlueprint
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (skeleton : LocalCircuitSkeleton (p := p) general generalEval) :
    LocalityBlueprint general := skeleton.toShrinkageSummary.toBlueprint

/-- И, наконец, получаем свидетель locality lift. -/
@[simp] def toWitness
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (skeleton : LocalCircuitSkeleton (p := p) general generalEval) :
    LocalityWitness general := skeleton.toBlueprint.toWitness

lemma toCertificate_toWitness
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (skeleton : LocalCircuitSkeleton (p := p) general generalEval) :
    (skeleton.toCertificate).toWitness = skeleton.toWitness := rfl

end LocalCircuitSkeleton

namespace LocalityCertificate

/-- Любой сертификат локализации автоматически задаёт `LocalCircuitSkeleton`.
Все численные поля копируются из сводки, а эмулятор — это уже построенная
функция `localEvaluator`. -/
def toSkeleton
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval) :
    LocalCircuitSkeleton (p := p) general generalEval :=
  { toShrinkageSummary := certificate.summary
    , evaluator := certificate.localEvaluator
    , evaluator_agrees := by
        intro x
        simpa using
          LocalityCertificate.localEvaluator_agrees
            (certificate := certificate) (x := x) }

lemma toSkeleton_toCertificate
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval) :
    certificate.toSkeleton.toCertificate = certificate := by
  classical
  -- Все поля совпадают по построению.
  cases certificate
  rfl

lemma toSkeleton_toWitness
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval) :
    certificate.toSkeleton.toWitness = certificate.toWitness := rfl

end LocalityCertificate

end LocalityLift
end Facts
