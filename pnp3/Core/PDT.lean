/-
  pnp3/Core/PDT.lean

  Частичные решающие деревья (PDT) над {0,1}^n:
  - лист хранит подкуб (регион)
  - узел ветвится по индексу бита (Fin n), имеет две ветви
  Определяем: leaves, depth.
-/
import Mathlib.Data.List.Basic
import Core.BooleanBasics

namespace Pnp3
namespace Core

inductive PDT (n : Nat) where
| leaf (R : Subcube n) : PDT n
| node (i : Fin n) (zeroBranch oneBranch : PDT n) : PDT n
deriving Repr

/-- Глубина PDT (макс. длина пути). -/
def PDT.depth {n : Nat} : PDT n → Nat
| .leaf _           => 0
| .node _ t0 t1     => Nat.succ (Nat.max (PDT.depth t0) (PDT.depth t1))

/-- Список листьев PDT (их подкубы). -/
def PDT.leaves {n : Nat} : PDT n → List (Subcube n)
| .leaf R         => [R]
| .node _ t0 t1   => (PDT.leaves t0) ++ (PDT.leaves t1)

/-- Количество листьев не превосходит `2 ^ depth`.

    Это простое упражнение по индукции: лист даёт один подкуб, а у узла
    все листья делятся между двумя поддеревьями. Максимальная глубина
    узла есть `succ (max d₀ d₁)`, где `d₀`, `d₁` — глубины поддеревьев.
    Индукционное предположение даёт оценки `|leaves t₀| ≤ 2^{d₀}` и
    `|leaves t₁| ≤ 2^{d₁}`. Объединяя их и пользуясь монотонностью
    показательной функции, получаем искомое неравенство. -/
theorem PDT.leaves_length_le_pow_depth {n : Nat} :
    ∀ t : PDT n, (PDT.leaves t).length ≤ Nat.pow 2 (PDT.depth t)
| .leaf _ => by
  -- Лист имеет одну вершину, а глубина равна нулю.
  simp [PDT.leaves, PDT.depth]
| .node _ t0 t1 => by
  -- Индукционные гипотезы для поддеревьев.
  have h0 := PDT.leaves_length_le_pow_depth t0
  have h1 := PDT.leaves_length_le_pow_depth t1
  -- Обозначим глубины и их максимум.
  set d0 := PDT.depth t0 with hd0
  set d1 := PDT.depth t1 with hd1
  have h0' : (PDT.leaves t0).length ≤ Nat.pow 2 d0 := by simpa [hd0] using h0
  have h1' : (PDT.leaves t1).length ≤ Nat.pow 2 d1 := by simpa [hd1] using h1
  have hpow0 : (PDT.leaves t0).length ≤ Nat.pow 2 (Nat.max d0 d1) := by
    -- `d0 ≤ max d0 d1`, значит монотонность степени даёт нужную оценку.
    have hle : d0 ≤ Nat.max d0 d1 := Nat.le_max_left _ _
    exact Nat.le_trans h0'
      (Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hle)
  have hpow1 : (PDT.leaves t1).length ≤ Nat.pow 2 (Nat.max d0 d1) := by
    have hle : d1 ≤ Nat.max d0 d1 := Nat.le_max_right _ _
    exact Nat.le_trans h1'
      (Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hle)
  -- Складываем оценки для двух списков листьев.
  have hadd := Nat.add_le_add hpow0 hpow1
  -- Переписываем длину списка листьев узла и раскрываем степень.
  have hsimp :
      (PDT.leaves t0).length + (PDT.leaves t1).length ≤
          2 ^ (Nat.succ (Nat.max d0 d1)) := by
    have haux :
        (PDT.leaves t0).length + (PDT.leaves t1).length ≤
            2 * Nat.pow 2 (Nat.max d0 d1) := by
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.succ_eq_add_one] using haux
  simpa [PDT.leaves, PDT.depth, hd0, hd1, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, Nat.succ_eq_add_one] using hsimp

/-- Инварианты «хорошего» дерева (пока как булевы проверки/пропозиции, при необходимости усилим):
    1) листья попарно не пересекаются,
    2) объединение листьев покрывает весь рассматриваемый регион.
    На данном шаге держим это как пропозиционное место для будущих лемм. -/
def PDT.WellFormed {n : Nat} (_t : PDT n) : Prop := True  -- placeholder

end Core
end Pnp3
