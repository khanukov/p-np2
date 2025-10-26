import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.Summary
import Facts.LocalityLift.Proof.Blueprint

/-!
# Семантическое понятие локализации

Чтобы полностью снять аксиому locality lift, необходимо связать численные
параметры (`ShrinkageSummary`) с семантическим утверждением «решатель зависит
только от координат из тест-набора».  В этом файле фиксируются соответствующие
определения и простые леммы.  Они используются как договорённость: будущий
шринкаж-свидетель должен предоставить `alive` и доказать, что функция решателя
не отличает входы, совпадающие на `alive`.

Пока у нас нет конкретных определений схем, мы работаем с абстрактными
булевыми функциями `BitVec N → Bool`.  Этого достаточно, чтобы формализовать
локализационное условие и интегрировать его в цепочку `ShrinkageSummary →
LocalityBlueprint → LocalityWitness`.
-/

namespace Facts
namespace LocalityLift

open scoped Classical
open Finset

/--
Функция `f` *локализована* на множестве координат `alive`, если изменение битов
вне `alive` не влияет на результат.  Эквивалентно, `f` зависит только от битов
с индексами из `alive`.
-/
@[simp] def localizedOn {N : Nat} (alive : Finset (Fin N))
    (f : BitVec N → Bool) : Prop :=
  ∀ x y, (∀ i ∈ alive, x i = y i) → f x = f y

/-!
### Ограничение и расширение по множеству живых координат

Следующие определения и леммы удобны для явной работы с локализованными
функциями.  Мы кодируем «сжатие» входа до живых координат и обратное
расширение с заполнением прочих битов значением `false`.  Это позволяет
формально говорить о том, что локализованная функция вычисляется только по
значениям на `alive`.
-/

/-- Ограничение битового вектора на подмножество `alive`. -/
def restrictToAlive {N : Nat} (alive : Finset (Fin N))
    (x : BitVec N) : {i // i ∈ alive} → Bool :=
  fun i => x i

/-- Расширение частичного назначения на всё пространство `BitVec N`. -/
def extendFromAlive {N : Nat} (alive : Finset (Fin N))
    (assignment : {i // i ∈ alive} → Bool) : BitVec N :=
  fun i => if hi : i ∈ alive then assignment ⟨i, hi⟩ else false

@[simp] lemma extendFromAlive_alive {N : Nat}
    (alive : Finset (Fin N))
    (assignment : {i // i ∈ alive} → Bool)
    {i : Fin N} (hi : i ∈ alive) :
    extendFromAlive alive assignment i = assignment ⟨i, hi⟩ := by
  classical
  simp [extendFromAlive, hi]

@[simp] lemma restrictToAlive_extend {N : Nat}
    (alive : Finset (Fin N))
    (assignment : {i // i ∈ alive} → Bool) :
    restrictToAlive alive (extendFromAlive alive assignment) = assignment := by
  classical
  funext i
  simp [restrictToAlive, extendFromAlive, i.property]

lemma extendFromAlive_restrict_eq {N : Nat}
    (alive : Finset (Fin N))
    (x : BitVec N) {i : Fin N} (hi : i ∈ alive) :
    extendFromAlive alive (restrictToAlive alive x) i = x i := by
  classical
  simp [extendFromAlive, restrictToAlive, hi]

lemma localizedOn_extend_restrict {N : Nat} {alive : Finset (Fin N)}
    {f : BitVec N → Bool}
    (h : localizedOn alive f) (x : BitVec N) :
    f (extendFromAlive alive (restrictToAlive alive x)) = f x := by
  classical
  have hx : ∀ i ∈ alive,
      extendFromAlive alive (restrictToAlive alive x) i = x i := by
    intro i hi
    exact extendFromAlive_restrict_eq alive x hi
  exact h (extendFromAlive alive (restrictToAlive alive x)) x (by
    intro i hi; exact (hx i hi))

lemma localizedOn_exists_factor {N : Nat} {alive : Finset (Fin N)}
    {f : BitVec N → Bool}
    (h : localizedOn alive f) :
    ∃ g : ({i // i ∈ alive} → Bool) → Bool,
      ∀ x, f x = g (restrictToAlive alive x) := by
  classical
  refine ⟨fun assignment => f (extendFromAlive alive assignment), ?_⟩
  intro x
  have := localizedOn_extend_restrict (alive := alive) (f := f) h x
  simpa using this.symm

lemma localizedOn.mono {N : Nat} {alive₁ alive₂ : Finset (Fin N)}
    {f : BitVec N → Bool} (hsub : alive₂ ⊆ alive₁)
    (h : localizedOn alive₂ f) : localizedOn alive₁ f := by
  intro x y hx
  apply h
  intro i hi
  exact hx i (hsub hi)

lemma localizedOn_of_eq_on {N : Nat} {alive : Finset (Fin N)}
    {f g : BitVec N → Bool}
    (hf : localizedOn alive f) (hfg : ∀ x, f x = g x) : localizedOn alive g := by
  intro x y hx
  have := hf x y hx
  simpa [hfg] using this

lemma localizedOn_const {N : Nat} (alive : Finset (Fin N))
    (b : Bool) : localizedOn alive (fun _ => b) := by
  intro x y hx; rfl

/--
Локализационное условие, прикреплённое к `ShrinkageSummary`.  Оно выражает
ожидание, что будущий шринкаж-свидетель докажет локализацию общего решателя на
живых координатах.
-/
@[simp] def summaryLocalized
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    (summary : ShrinkageSummary general)
    (f : BitVec (inputLen p) → Bool) : Prop :=
  localizedOn summary.alive f

/--
Сертификат локализации содержит числовое резюме и семантическое свойство.
При наличии такого сертификата можно получить `LocalityWitness` без дополнительной
информации.
-/
structure LocalityCertificate
    {p : GapMCSPParams} (general : SmallGeneralCircuitSolver p)
    (generalEval : BitVec (inputLen p) → Bool) : Type where
  /-- Числовая сводка параметров, полученных из shrinkage. -/
  summary    : ShrinkageSummary general
  /-- Доказательство локализации общей функции на живых координатах. -/
  localized  : localizedOn summary.alive generalEval

namespace LocalityCertificate

/-- Числовая часть сертификата сразу даёт «чертёж» локального решателя. -/
@[simp] def toBlueprint
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval) :
    LocalityBlueprint general :=
  certificate.summary.toBlueprint

/-- Сертификат локализации автоматически порождает свидетель locality lift. -/
@[simp] def toWitness
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval) :
    LocalityWitness general :=
  certificate.toBlueprint.toWitness

/--
Локальный «эмулятор» общего решателя, ограниченный на живых координатах.
Функция принимает только значения на `alive` и восстанавливает полный вектор,
подставляя `false` вне `alive`.  Благодаря локализации результат совпадает с
`generalEval` на всех входах.
-/
@[simp] def localEvaluator
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval) :
    ({i // i ∈ certificate.summary.alive} → Bool) → Bool :=
  fun assignment =>
    generalEval (extendFromAlive certificate.summary.alive assignment)

/--
На каждом полном входе локальный эмулятор совпадает с исходным решателем.
-/
lemma localEvaluator_agrees
    {p : GapMCSPParams} {general : SmallGeneralCircuitSolver p}
    {generalEval : BitVec (inputLen p) → Bool}
    (certificate : LocalityCertificate (p := p) general generalEval)
    (x : BitVec (inputLen p)) :
    certificate.localEvaluator
        (restrictToAlive certificate.summary.alive x) = generalEval x := by
  classical
  simp [LocalityCertificate.localEvaluator,
    localizedOn_extend_restrict (alive := certificate.summary.alive)
      (f := generalEval) certificate.localized x]

end LocalityCertificate

end LocalityLift
end Facts
