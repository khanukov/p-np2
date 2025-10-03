import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Core.BooleanBasics
import Counting.Atlas_to_LB_Core

namespace Pnp3
namespace Tests

open Core Counting

open Classical

/-!
# Sanity-проверки подсчётов атласа

В этом файле мы приводим несколько вычислимых проверок для определения
`UnionClass` и вспомогательных конструкций из
`Counting/Atlas_to_LB_Core.lean`.  Цель — убедиться, что "реальная"
комбинаторика (при переборе маленьких словарей подкубов) согласуется с
теоретическими оценками.

Мы не претендуем на строгие доказательства общих фактов — для этого
предназначены теоремы в основном коде.  Вместо этого мы берём крошечные
примеры (`m = 2`, словарь из нескольких подкубов) и убеждаемся, что

* число уникальных объединений подкубов не превышает биномиальных
  комбинаций `∑_{i ≤ k} C(D, i)`;
* значения расстояния `distU` совпадают с "ручными" ожиданиями;
* построения действительно различают функции, которые должны различаться.
-/

/-- Удобный подкуб, фиксирующий один бит, остальные оставляющий свободными. -/
def fixBit {m : Nat} (i : Fin m) (b : Bool) : Subcube m :=
  fun j => if j = i then some b else none

/-- Перечисление всех объединений ≤ `k` подкубов из словаря `R` в виде списков
значений на полном пространстве `BitVec m`.  Мы кодируем каждую функцию
её таблицей истинности (списком `Bool`), что позволяет сравнивать их на
равенство через `eraseDups`. -/
def unionEvalVectors {m : Nat} (R : List (Subcube m)) (k : Nat) :
    List (List Bool) :=
  let domain := allBitVec m
  let sublists := (List.sublists R).filter fun S => S.length ≤ k
  sublists.map (fun S => domain.map (fun x => coveredB S x))

/-- Число попарно различных объединений ≤ `k` подкубов из словаря `R`. -/
def unionCount {m : Nat} (R : List (Subcube m)) (k : Nat) : Nat :=
  ((unionEvalVectors (m := m) R k).eraseDups).length

/-- Конкретный словарь подкубов на `m = 2`.  Первый элемент фиксирует `x₀ = 1`,
второй — `x₀ = 0`.  Этого достаточно, чтобы проверить поведение объединений. -/
def sampleDict : List (Subcube 2) :=
  [fixBit (m := 2) 0 true, fixBit (m := 2) 0 false]

lemma sampleDict_length : sampleDict.length = 2 := by decide

/-- При ограничении `k = 1` возможны три различные функции:
* пустое объединение (всегда `false`),
* индикатор `x₀ = 1`,
* индикатор `x₀ = 0`.
-/
lemma unionCount_sampleDict_k1 : unionCount sampleDict 1 = 3 := by
  decide

/-- При `k = 2` появляется четвёртая функция — константа `true`, покрывающая
всё пространство. -/
lemma unionCount_sampleDict_k2 : unionCount sampleDict 2 = 4 := by
  decide

/-- Проверяем, что явные значения не превосходят биномиальные суммы. -/
lemma unionCount_sampleDict_k1_le_choose :
    unionCount sampleDict 1 ≤
      Nat.choose sampleDict.length 0 + Nat.choose sampleDict.length 1 := by
  decide

lemma unionCount_sampleDict_k2_le_choose :
    unionCount sampleDict 2 ≤
      Nat.choose sampleDict.length 0 +
        Nat.choose sampleDict.length 1 +
          Nat.choose sampleDict.length 2 := by
  decide

/-- Таблица истинности функции `x ↦ x₀` — удобный эталон для проверки `distU`. -/
def proj₀ : Domain 2 → Bool := fun x => x 0

/-- Постоянно ложная функция. -/
def zeroFunc : Domain 2 → Bool := fun _ => false

/-- Постоянно истинная функция. -/
def oneFunc : Domain 2 → Bool := fun _ => true

/-- Проверяем, что расстояние между `proj₀` и постоянно ложной функцией равно 2
(половина точек из четырёх).
-/
lemma dist_proj₀_zero : distU (m := 2) proj₀ zeroFunc = 2 := by
  decide

/-- Аналогично, расстояние между `proj₀` и константой `true` также равно 2. -/
lemma dist_proj₀_one : distU (m := 2) proj₀ oneFunc = 2 := by
  decide

/-- Для полного совпадения расстояние равно нулю. -/
lemma dist_proj₀_self : distU (m := 2) proj₀ proj₀ = 0 := by
  decide

end Tests
end Pnp3
