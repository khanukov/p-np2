/-
  pnp3/Core/PDTExtras.lean

  Дополнительные леммы для работы с частичными решающими деревьями (PDT).
  Эти леммы расширяют базовую функциональность PDT, предоставляя дополнительные
  свойства и упрощая работу с глубиной, листьями и уточнениями.
-/
import Core.PDT
import Core.BooleanBasics

namespace Pnp3
namespace Core

/-! ## Дополнительные свойства depth -/

/-- Глубина листа всегда равна 0 -/
@[simp]
lemma PDT.depth_leaf {n : Nat} (R : Subcube n) :
    PDT.depth (PDT.leaf R) = 0 := rfl

/-- Глубина node всегда как минимум 1 -/
lemma PDT.depth_node_pos {n : Nat} (i : Fin n) (t0 t1 : PDT n) :
    1 ≤ PDT.depth (PDT.node i t0 t1) := by
  simp [PDT.depth]

/-- Глубина левой ветви не превышает глубину узла -/
lemma PDT.depth_left_le {n : Nat} (i : Fin n) (t0 t1 : PDT n) :
    PDT.depth t0 ≤ PDT.depth (PDT.node i t0 t1) := by
  simp [PDT.depth]
  exact Nat.le_succ_of_le (Nat.le_max_left _ _)

/-- Глубина правой ветви не превышает глубину узла -/
lemma PDT.depth_right_le {n : Nat} (i : Fin n) (t0 t1 : PDT n) :
    PDT.depth t1 ≤ PDT.depth (PDT.node i t0 t1) := by
  simp [PDT.depth]
  exact Nat.le_succ_of_le (Nat.le_max_right _ _)

/-! ## Свойства leaves -/

/-- Лист содержит ровно один элемент в списке листьев -/
@[simp]
lemma PDT.leaves_leaf {n : Nat} (R : Subcube n) :
    PDT.leaves (PDT.leaf R) = [R] := rfl

/-- Длина списка листьев node - это сумма длин поддеревьев -/
lemma PDT.leaves_node_length {n : Nat} (i : Fin n) (t0 t1 : PDT n) :
    (PDT.leaves (PDT.node i t0 t1)).length =
      (PDT.leaves t0).length + (PDT.leaves t1).length := by
  simp [PDT.leaves, List.length_append]

/-- Любое дерево имеет хотя бы один лист -/
lemma PDT.leaves_nonempty {n : Nat} (t : PDT n) :
    (PDT.leaves t).length ≥ 1 := by
  induction t with
  | leaf R => simp [PDT.leaves]
  | node i t0 t1 ih0 ih1 =>
    simp [PDT.leaves, List.length_append]
    calc (PDT.leaves t0).length + (PDT.leaves t1).length
        ≥ 1 + (PDT.leaves t1).length := Nat.add_le_add_right ih0 _
      _ ≥ 1 + 1 := Nat.add_le_add_left ih1 _
      _ = 2 := rfl
      _ ≥ 1 := by norm_num

/-- Уточнение листа заменяет его на соответствующий хвост -/
@[simp]
lemma PDT.refine_leaf {n : Nat} (R : Subcube n)
    (tails : ∀ β, β ∈ PDT.leaves (PDT.leaf R) → PDT n) :
    PDT.refine (PDT.leaf R) tails = tails R (by simp [PDT.leaves]) := rfl

end Core
end Pnp3
