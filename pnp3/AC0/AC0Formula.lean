import Core.BooleanBasics

/-!
  pnp3/AC0/AC0Formula.lean

  Минимальное представление AC0‑формул глубины `d` как деревьев.
  Это закрывает пункт Phase 5.1 плана: явный тип `AC0Formula d n`
  и базовые функции `eval` и `size`.

  Конструкция **осознанно простая**:
  - depth = 0: атомарная функция (литерал/константа/любой булевый атом);
  - depth = d+1: AND/OR над списком подформул глубины `d`.

  Такой формат удобен для дальнейшей индукции по глубине (Phase 5.2)
  и не требует DAG‑представления.
-/

namespace Pnp3
namespace AC0

open Core

/-- AC0‑формула глубины `d` над `n` входными битами. -/
inductive AC0Formula (d n : Nat) : Type
  | atom : (BitVec n → Bool) → AC0Formula 0 n
  | and : List (AC0Formula d n) → AC0Formula (Nat.succ d) n
  | or  : List (AC0Formula d n) → AC0Formula (Nat.succ d) n
  deriving Repr

namespace AC0Formula

variable {n d : Nat}

/-- Вычисление значения формулы. -/
def eval : AC0Formula d n → BitVec n → Bool
  | atom f => f
  | and fs =>
      fun x => fs.all (fun g => eval g x)
  | or fs  =>
      fun x => fs.any (fun g => eval g x)

/-- Размер формулы как число узлов дерева. -/
def size : AC0Formula d n → Nat
  | atom _ => 1
  | and fs => 1 + (fs.map size).sum
  | or fs  => 1 + (fs.map size).sum

@[simp] lemma size_atom (f : BitVec n → Bool) :
    size (AC0Formula.atom f) = 1 := by rfl

@[simp] lemma size_and (fs : List (AC0Formula d n)) :
    size (AC0Formula.and fs) = 1 + (fs.map size).sum := by rfl

@[simp] lemma size_or (fs : List (AC0Formula d n)) :
    size (AC0Formula.or fs) = 1 + (fs.map size).sum := by rfl

end AC0Formula
end AC0
end Pnp3
