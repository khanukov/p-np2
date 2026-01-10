import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.Localization

/-!
# Рестрикции и управление «живыми» координатами

В этом модуле описывается удобный язык для работы с рестрикциями (частичными
назначениями входных битов), появляющимися в доказательствах shrinkage.  Идея
следующая: вместо того, чтобы явным образом оперировать подкубами или
частичными деревьями решений, мы фиксируем множество «живых» координат и
функцию, задающую значения на остальных позициях.  Такая структура позволяет
легко формализовать утверждение «функция зависит только от координат из
`alive`» и, при необходимости, переводить рестрикцию в конкретный битовый
вектор.

Пока эта инфраструктура не подключена к настоящему shrinkage-свидетелю, но
все определения и леммы уже готовы: когда появятся реальные сертификаты,
нужно будет лишь доказать, что соответствующая функция не меняется при
применении рестрикции — и сразу можно будет получить локализационное свойство.
-/

namespace Facts
namespace LocalityLift

open scoped Classical
open Finset

/--
`Restriction N` фиксирует множество «живых» координат и значения на всех
остальных позициях.  При применении к битовому вектору такая рестрикция
оставляет живые координаты как есть, а на остальных координатах подставляет
предписанные значения.
-/
structure Restriction (N : Nat) where
  /-- Набор координат, которые остаются «свободными». -/
  alive : Finset (Fin N)
  /-- Табличка со значениями на всех координатах (живых и замороженных). -/
  assignment : Fin N → Bool

namespace Restriction

variable {N : Nat}

/--
Применение рестрикции к битовому вектору: на живых координатах берём исходные
значения, на остальных — значения из `assignment`.
-/
def apply (r : Restriction N) (x : BitVec N) : BitVec N :=
  fun i => if i ∈ r.alive then x i else r.assignment i

@[simp] lemma apply_alive (r : Restriction N) (x : BitVec N)
    {i : Fin N} (hi : i ∈ r.alive) :
    r.apply x i = x i := by
  simp [apply, hi]

@[simp] lemma apply_not_alive (r : Restriction N) (x : BitVec N)
    {i : Fin N} (hi : i ∉ r.alive) :
    r.apply x i = r.assignment i := by
  simp [apply, hi]

/--
Если два вектора совпадают на `alive`, то и результат применения рестрикции к
ним совпадает.
-/
lemma apply_eq_of_eq_on_alive (r : Restriction N)
    {x y : BitVec N}
    (h : ∀ i ∈ r.alive, x i = y i) :
    r.apply x = r.apply y := by
  funext i
  by_cases hi : i ∈ r.alive
  · have := h i hi
    simp [apply, hi, this]
  · simp [apply, hi]

/--
Если функция `f` не меняется после применения рестрикции, то она автоматически
локализована на `alive`: при совпадении входов на `alive` их образы совпадают.
-/
lemma localizedOn_of_stable (r : Restriction N)
    {f : BitVec N → Bool}
    (hstable : ∀ x, f (r.apply x) = f x) :
    localizedOn r.alive f := by
  intro x y hxy
  have hx : f x = f (r.apply x) := (hstable x).symm
  have hy : f y = f (r.apply y) := (hstable y).symm
  have happly : r.apply x = r.apply y := r.apply_eq_of_eq_on_alive hxy
  simp [hx, hy, happly]

/--
Рестрикция, полученная из битового вектора: на свободных координатах значения
берутся из аргумента, на остальных — фиксируются значениями того же вектора.
Такая конструкция понадобится, когда из shrinkage-свидетеля нужно будет
извлечь конкретный тест-набор.
-/
def ofVector (alive : Finset (Fin N)) (v : BitVec N) : Restriction N :=
  { alive := alive
    , assignment := fun i => v i }

@[simp] lemma ofVector_alive (alive : Finset (Fin N)) (v : BitVec N) :
    (ofVector (N := N) alive v).alive = alive := rfl

@[simp] lemma ofVector_assignment (alive : Finset (Fin N)) (v : BitVec N) :
    (ofVector (N := N) alive v).assignment = fun i => v i := rfl

@[simp] lemma apply_ofVector_alive (alive : Finset (Fin N)) (v : BitVec N)
    {i : Fin N} (hi : i ∈ alive) :
    (ofVector (N := N) alive v).apply v i = v i := by
  simp [ofVector, apply, hi]

@[simp] lemma apply_ofVector_not_alive (alive : Finset (Fin N)) (v x : BitVec N)
    {i : Fin N} (hi : i ∉ alive) :
    (ofVector (N := N) alive v).apply x i = v i := by
  simp [ofVector, apply, hi]

/--
  Канонический тест-набор, ассоциированный с рестрикцией.  Мы не вводим новые
  идеи: просто переупаковываем `alive` в семейство единичных векторов.  Такая
  функция повышает читабельность последующих конструкций, где нужно явно
  обращаться к тест-набору, произведённому из shrinkage-свидетеля.
-/
def testSet (r : Restriction N) : Finset (BitVec N) :=
  testSetOfAlive r.alive

@[simp] lemma testSet_eq (r : Restriction N) :
    r.testSet = testSetOfAlive r.alive := rfl

@[simp] lemma card_testSet (r : Restriction N) :
    r.testSet.card = r.alive.card := by
  classical
  simp [Restriction.testSet]

@[simp] lemma testSet_card_le_polylog
    {p : GapMCSPParams} (r : Restriction (inputLen p))
    (hle : r.alive.card ≤ polylogBudget (inputLen p)) :
    r.testSet.card ≤ polylogBudget (inputLen p) := by
  classical
  simpa [Restriction.testSet] using hle

end Restriction

end LocalityLift
end Facts
