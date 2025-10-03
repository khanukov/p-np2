import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Tactic
import Core.BooleanBasics
import Counting.Atlas_to_LB_Core

namespace Pnp3
namespace Tests

open Core Counting
open Classical

/-- Помощник: свёртка списка списков в один список. -/
def flatten {α : Type _} : List (List α) → List α
  | [] => []
  | xs :: rest => xs ++ flatten rest

/-!
  # Поиск контрпримеров к оценке Covering Power

  В этом тесте мы перебираем все подкубы для `m = 2`, все словари размера до 2
  и значения `k ≤ 2`, а также несколько значений `ε`.  Цель — убедиться, что
  реальное число ε-аппроксимируемых функций всегда не превосходит произведения
  «число объединений» × «размер хаммингового шара».  Если где-то возникает
  нарушение, тест выдаст явный контрпример.

  Хотя основная теорема в коде опирается на аксиомы (пока что), подобный перебор
  помогает проверять, что сам способ подсчёта не содержит ошибок.
-/

/-- Удобный тип: таблица истинности функции `Domain m → Bool`. -/
abbrev TruthTable (m : Nat) :=
  { values : List Bool // values.length = Nat.pow 2 m }

namespace TruthTable

/-- Значение функции, закодированной таблицей истинности.  Поиск ведём через
    явной перебор списка `allBitVec m`. -/
def eval {m : Nat} (t : TruthTable m) (x : Domain m) : Bool :=
  let rec go : List (Domain m) → List Bool → Bool
    | [], _ => false
    | _, [] => false
    | y :: ys, b :: bs =>
        if x = y then b else go ys bs
  go (allBitVec m) t.1

/-- Преобразуем таблицу в настоящую функцию. -/
def ofFunction {m : Nat} (f : Domain m → Bool) : TruthTable m :=
  ⟨(allBitVec m).map f, by
    simp [Core.allBitVec]
  ⟩

/-- Хэммингово расстояние между двумя таблицами. -/
def hammingDist {m : Nat} (t₁ t₂ : TruthTable m) : Nat :=
  let pairs := List.zip t₁.1 t₂.1
  pairs.foldl (fun acc p =>
    acc + (if p.1 ≠ p.2 then 1 else 0)) 0

/-- Подсчёт функций внутри хаммингового шара заданного радиуса. -/
def ballCount {m : Nat} (center : TruthTable m) (radius : Nat)
    (tables : List (TruthTable m)) : Nat :=
  (tables.filter fun t => hammingDist (m := m) center t ≤ radius).length

end TruthTable

/-- Выбор всех комбинаций `Option Bool` длины `m` — это все подкубы. -/
abbrev Assignment (m : Nat) :=
  { values : List (Option Bool) // values.length = m }

/-- Перечень всех булевых векторов фиксированной длины в виде списков. -/
noncomputable def allBoolVectors : (n : Nat) → List { values : List Bool // values.length = n }
  | 0 => [⟨[], by simp⟩]
  | Nat.succ n =>
      let tails := allBoolVectors n
      flatten <|
        tails.map fun tail =>
          [⟨false :: tail.1, by simp [tail.2]⟩,
           ⟨true :: tail.1, by simp [tail.2]⟩]

/-- Все возможные списки присваиваний `Option Bool` длины `m`. -/
noncomputable def allAssignments : (m : Nat) → List (Assignment m)
  | 0 => [⟨[], by simp⟩]
  | Nat.succ m =>
      let tails := allAssignments m
      flatten <|
        tails.map fun tail =>
          [⟨(none :: tail.1), by simp [tail.2]⟩,
           ⟨(some false :: tail.1), by simp [tail.2]⟩,
           ⟨(some true :: tail.1), by simp [tail.2]⟩]

/-- Преобразуем присваивание в подкуб. -/
def assignmentToSubcube {m : Nat} (a : Assignment m) : Subcube m :=
  fun i => a.1.getD i.val none

/-- Полный список подкубов для фиксированного `m`. -/
noncomputable def allSubcubes (m : Nat) : List (Subcube m) :=
  (allAssignments m).map assignmentToSubcube

/-- Все таблицы истинности для функций `Domain m → Bool`. -/
noncomputable def allTruthTables (m : Nat) : List (TruthTable m) :=
  (allBoolVectors (Nat.pow 2 m)).map fun v =>
    ⟨v.1, by simpa using v.2⟩

/-- Перебрать все подмножества словаря размера ≤ `maxLen`. -/
noncomputable def dictionariesUpTo
    {m : Nat} (maxLen : Nat) : List (List (Subcube m)) :=
  let base := (allSubcubes m)
  (List.sublists base).filter fun R => R.length ≤ maxLen

/-- Все варианты `k` от 0 до `maxK`. -/
def kValues (maxK : Nat) : List Nat := List.range (maxK.succ)

/-- Финитное множество значений `ε`, которые мы хотим проверить. -/
def epsilons : List Rat := [0, (1 : Rat) / 4, (1 : Rat) / 2]

/-- Порог несовпадений: ⌊ε ⋅ 2^m⌋. -/
def mismatchThreshold (m : Nat) (ε : Rat) : Nat :=
  Int.toNat <| Rat.floor (ε * (Nat.pow 2 m))

/-- Проверка, можно ли аппроксимировать таблицу `f` с параметрами `(R,k,ε)`. -/
def approximable?
    {m : Nat} (tables : List (TruthTable m))
    (R : List (Subcube m)) (k : Nat) (ε : Rat)
    (f : TruthTable m) : Bool :=
  let threshold := mismatchThreshold m ε
  let candidates := (List.sublists R).filter fun S => S.length ≤ k
  candidates.any fun S =>
    let g := TruthTable.ofFunction (m := m) (fun x => coveredB S x)
    TruthTable.hammingDist (m := m) f g ≤ threshold

/-- Реальное число ε-аппроксимируемых функций. -/
def approxCount
    {m : Nat} (tables : List (TruthTable m))
    (R : List (Subcube m)) (k : Nat) (ε : Rat) : Nat :=
  (tables.filter fun f => approximable? (tables := tables) R k ε f).length

/-- Число различных объединений ≤ `k` подкубов. -/
def unionCount {m : Nat} (R : List (Subcube m)) (k : Nat) : Nat :=
  let combos := (List.sublists R).filter fun S => S.length ≤ k
  let tables := combos.map fun S => TruthTable.ofFunction (m := m) (fun x => coveredB S x)
  (tables.eraseDups).length

/-- Максимальный размер хаммингового шара среди всех функций из `UnionClass`. -/
def maxBallSize
    {m : Nat} (tables : List (TruthTable m))
    (R : List (Subcube m)) (k : Nat) (ε : Rat) : Nat :=
  let threshold := mismatchThreshold m ε
  let combos := (List.sublists R).filter fun S => S.length ≤ k
  let centers := combos.map fun S => TruthTable.ofFunction (m := m) (fun x => coveredB S x)
  let counts := centers.map fun g => TruthTable.ballCount (m := m) g threshold tables
  counts.foldl Nat.max 0

/-- Полный перебор параметров. Возвращаем список всех найденных контрпримеров. -/
noncomputable def counterexamples
    (m maxDictSize maxK : Nat) : List (List (Subcube m) × Nat × Rat) :=
  let tables := allTruthTables m
  let dicts := dictionariesUpTo (m := m) maxDictSize
  flatten <|
    dicts.map fun R =>
      flatten <|
        (kValues maxK).map fun k =>
          List.filterMap
            (fun ε =>
              let approx := approxCount (tables := tables) R k ε
              let unions := unionCount (R := R) k
              let balls := maxBallSize (tables := tables) R k ε
              let bound := unions * balls
              if approx > bound then some (R, k, ε) else none)
            epsilons

/-- Булев вариант проверки: `true`, если список контрпримеров пуст. -/
noncomputable def counterexamplesOk (m maxDictSize maxK : Nat) : Bool :=
  (counterexamples (m := m) maxDictSize maxK).isEmpty

/-!
  Для `m = 2` проверяем две конфигурации параметров.  Команда `#eval` вызывает
  явный «паник», если результат оказался ложным, что обеспечивает аварийный
  останов теста при появлении контрпримеров.
-/
#eval
  if counterexamplesOk 2 2 2 then
    ()
  else
    (panic! "Found counterexample for m=2, maxLen=2, k=2" : Unit)

#eval
  if counterexamplesOk 2 3 2 then
    ()
  else
    (panic! "Found counterexample for m=2, maxLen=3, k=2" : Unit)

end Tests
end Pnp3
