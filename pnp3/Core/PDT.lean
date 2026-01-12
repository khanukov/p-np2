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

/--
  Операция "уточнения" PDT: каждому листу дерева `t` сопоставляем хвост
  `tails β hβ`, где `hβ` фиксирует принадлежность `β` исходному списку
  листьев.  Функция рекурсивно восстанавливает эти доказательства и
  подставляет хвосты вместо листьев.
-/
def PDT.refine {n : Nat}
    (t : PDT n)
    (tails : ∀ β, β ∈ PDT.leaves t → PDT n) : PDT n :=
  match t with
  | .leaf β =>
      let hmem : β ∈ PDT.leaves (PDT.leaf β) := by
        simp [PDT.leaves]
      tails β hmem
  | .node i t0 t1 =>
      let tails0 : ∀ β, β ∈ PDT.leaves t0 → PDT n :=
        fun β hβ =>
          let hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
            List.mem_append.mpr (Or.inl hβ)
          let hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
            have hdef :
                PDT.leaves (PDT.node i t0 t1) =
                  (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
            exact Eq.subst (motive := fun s => β ∈ s)
              (Eq.symm hdef) hmemAppend
          tails β hmemTree
      let tails1 : ∀ β, β ∈ PDT.leaves t1 → PDT n :=
        fun β hβ =>
          let hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
            List.mem_append.mpr (Or.inr hβ)
          let hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
            have hdef :
                PDT.leaves (PDT.node i t0 t1) =
                  (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
            exact Eq.subst (motive := fun s => β ∈ s)
              (Eq.symm hdef) hmemAppend
      tails β hmemTree
      PDT.node i (PDT.refine t0 tails0) (PDT.refine t1 tails1)

/--
  Глубина уточнённого дерева не превышает глубину исходного плюс верхнюю
  границу на хвосты.  В каждом пути сначала идём по стволу `t`, а затем по
  хвосту глубины `≤ ℓ`.
-/
theorem PDT.depth_refine_le {n : Nat}
    {t : PDT n}
    {tails : ∀ β, β ∈ PDT.leaves t → PDT n}
    {ℓ : Nat}
    (htails : ∀ β hβ, PDT.depth (tails β hβ) ≤ ℓ) :
    PDT.depth (PDT.refine t tails) ≤ PDT.depth t + ℓ :=
  by
    revert tails
    revert ℓ
    induction t with
    | leaf β =>
        intro ℓ tails htails
        have hmem : β ∈ PDT.leaves (PDT.leaf β) := by
          simp [PDT.leaves]
        have hrefine : PDT.refine (PDT.leaf β) tails = tails β hmem := rfl
        have hgoal : PDT.depth (PDT.refine (PDT.leaf β) tails) ≤ ℓ := by
          have hbound := htails β hmem
          have hrewrite := hrefine
          exact Eq.subst (motive := fun s => PDT.depth s ≤ ℓ)
            (Eq.symm hrewrite) hbound
        have hrewriteDepth : PDT.depth (PDT.leaf β) + ℓ = ℓ := by
          simp [PDT.depth]
        exact Eq.subst (motive := fun s =>
            PDT.depth (PDT.refine (PDT.leaf β) tails) ≤ s)
          (Eq.symm hrewriteDepth) hgoal
    | node i t0 t1 ih0 ih1 =>
        intro ℓ tails htails
        let tails0 : ∀ β, β ∈ PDT.leaves t0 → PDT n :=
          fun β hβ =>
            let hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
              List.mem_append.mpr (Or.inl hβ)
            let hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
              have hdef :
                  PDT.leaves (PDT.node i t0 t1) =
                    (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
              exact Eq.subst (motive := fun s => β ∈ s)
                (Eq.symm hdef) hmemAppend
            tails β hmemTree
        let tails1 : ∀ β, β ∈ PDT.leaves t1 → PDT n :=
          fun β hβ =>
            let hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
              List.mem_append.mpr (Or.inr hβ)
            let hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
              have hdef :
                  PDT.leaves (PDT.node i t0 t1) =
                    (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
              exact Eq.subst (motive := fun s => β ∈ s)
                (Eq.symm hdef) hmemAppend
            tails β hmemTree
        have htails0 : ∀ β hβ, PDT.depth (tails0 β hβ) ≤ ℓ := by
          intro β hβ
          have hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
            List.mem_append.mpr (Or.inl hβ)
          have hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
            have hdef :
                PDT.leaves (PDT.node i t0 t1) =
                  (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
            exact Eq.subst (motive := fun s => β ∈ s)
              (Eq.symm hdef) hmemAppend
          exact htails β hmemTree
        have htails1 : ∀ β hβ, PDT.depth (tails1 β hβ) ≤ ℓ := by
          intro β hβ
          have hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
            List.mem_append.mpr (Or.inr hβ)
          have hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
            have hdef :
                PDT.leaves (PDT.node i t0 t1) =
                  (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
            exact Eq.subst (motive := fun s => β ∈ s)
              (Eq.symm hdef) hmemAppend
          exact htails β hmemTree
        have hleft := ih0 (ℓ := ℓ) (tails := tails0) htails0
        have hright := ih1 (ℓ := ℓ) (tails := tails1) htails1
        have hmax_left :
            PDT.depth (PDT.refine t0 tails0) ≤
              Nat.max (PDT.depth t0 + ℓ) (PDT.depth t1 + ℓ) := by
          exact Nat.le_trans hleft (Nat.le_max_left _ _)
        have hmax_right :
            PDT.depth (PDT.refine t1 tails1) ≤
              Nat.max (PDT.depth t0 + ℓ) (PDT.depth t1 + ℓ) := by
          exact Nat.le_trans hright (Nat.le_max_right _ _)
        have hmax_refine :
            Nat.max (PDT.depth (PDT.refine t0 tails0))
              (PDT.depth (PDT.refine t1 tails1)) ≤
                Nat.max (PDT.depth t0 + ℓ) (PDT.depth t1 + ℓ) := by
          exact Nat.max_le.mpr ⟨hmax_left, hmax_right⟩
        have hsucc_refine :
            Nat.succ
              (Nat.max (PDT.depth (PDT.refine t0 tails0))
                (PDT.depth (PDT.refine t1 tails1))) ≤
              Nat.succ (Nat.max (PDT.depth t0 + ℓ)
                (PDT.depth t1 + ℓ)) :=
          Nat.succ_le_succ hmax_refine
        have hmax_shift :
            Nat.max (PDT.depth t0 + ℓ) (PDT.depth t1 + ℓ) ≤
              Nat.max (PDT.depth t0) (PDT.depth t1) + ℓ := by
          have hleftBound : PDT.depth t0 + ℓ ≤
              Nat.max (PDT.depth t0) (PDT.depth t1) + ℓ :=
            Nat.add_le_add_right (Nat.le_max_left _ _) ℓ
          have hrightBound : PDT.depth t1 + ℓ ≤
              Nat.max (PDT.depth t0) (PDT.depth t1) + ℓ :=
            Nat.add_le_add_right (Nat.le_max_right _ _) ℓ
          exact Nat.max_le.mpr ⟨hleftBound, hrightBound⟩
        have hsucc_shift :
            Nat.succ (Nat.max (PDT.depth t0 + ℓ) (PDT.depth t1 + ℓ)) ≤
              Nat.succ (Nat.max (PDT.depth t0) (PDT.depth t1) + ℓ) :=
          Nat.succ_le_succ hmax_shift
        have hstep := Nat.le_trans hsucc_refine hsucc_shift
        have hrewriteSucc :
            Nat.succ (Nat.max (PDT.depth t0) (PDT.depth t1) + ℓ) =
              Nat.succ (Nat.max (PDT.depth t0) (PDT.depth t1)) + ℓ := by
          simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
        have htarget :
            Nat.succ
              (Nat.max (PDT.depth (PDT.refine t0 tails0))
                (PDT.depth (PDT.refine t1 tails1))) ≤
              Nat.succ (Nat.max (PDT.depth t0) (PDT.depth t1)) + ℓ := by
          have htmp := hstep
          have hrewrite := hrewriteSucc
          exact Eq.subst (motive := fun s =>
              Nat.succ
                (Nat.max (PDT.depth (PDT.refine t0 tails0))
                  (PDT.depth (PDT.refine t1 tails1))) ≤ s)
            hrewrite htmp
        have hgoal := htarget
        simpa [PDT.refine, PDT.depth] using hgoal

/-!
  Дополнительная полезная оценка: глубина ствола *не уменьшается* после
  уточнения. Этот факт пригодится при индукции по глубине: когда мы
  «приклеиваем» хвосты к общему стволу, итоговое дерево всегда имеет
  глубину не меньше глубины ствола.
-/
theorem PDT.depth_refine_ge {n : Nat}
    (t : PDT n)
    (tails : ∀ β, β ∈ PDT.leaves t → PDT n) :
    PDT.depth t ≤ PDT.depth (PDT.refine t tails) := by
  induction t with
  | leaf β =>
      -- У листа глубина 0, а уточнение даёт дерево глубины ≥ 0.
      have hmem : β ∈ PDT.leaves (PDT.leaf β) := by
        simp [PDT.leaves]
      have hrefine : PDT.refine (PDT.leaf β) tails = tails β hmem := rfl
      -- После раскрытия глубины в листе остаётся показать неотрицательность.
      simp [PDT.depth, hrefine]
  | node i t0 t1 ih0 ih1 =>
      -- Для узла применяем И.П. к обеим ветвям.
      let tails0 : ∀ β, β ∈ PDT.leaves t0 → PDT n := fun β hβ =>
        let hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
          List.mem_append.mpr (Or.inl hβ)
        let hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
          have hdef :
              PDT.leaves (PDT.node i t0 t1) =
                (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
          exact Eq.subst (motive := fun s => β ∈ s)
            (Eq.symm hdef) hmemAppend
        tails β hmemTree
      let tails1 : ∀ β, β ∈ PDT.leaves t1 → PDT n := fun β hβ =>
        let hmemAppend : β ∈ (PDT.leaves t0) ++ (PDT.leaves t1) :=
          List.mem_append.mpr (Or.inr hβ)
        let hmemTree : β ∈ PDT.leaves (PDT.node i t0 t1) := by
          have hdef :
              PDT.leaves (PDT.node i t0 t1) =
                (PDT.leaves t0) ++ (PDT.leaves t1) := rfl
          exact Eq.subst (motive := fun s => β ∈ s)
            (Eq.symm hdef) hmemAppend
        tails β hmemTree
      have h0 : PDT.depth t0 ≤ PDT.depth (PDT.refine t0 tails0) := ih0 tails0
      have h1 : PDT.depth t1 ≤ PDT.depth (PDT.refine t1 tails1) := ih1 tails1
      have h0' :
          PDT.depth t0 ≤
            Nat.max (PDT.depth (PDT.refine t0 tails0))
              (PDT.depth (PDT.refine t1 tails1)) :=
        Nat.le_trans h0 (Nat.le_max_left _ _)
      have h1' :
          PDT.depth t1 ≤
            Nat.max (PDT.depth (PDT.refine t0 tails0))
              (PDT.depth (PDT.refine t1 tails1)) :=
        Nat.le_trans h1 (Nat.le_max_right _ _)
      have hmax :
          Nat.max (PDT.depth t0) (PDT.depth t1) ≤
            Nat.max (PDT.depth (PDT.refine t0 tails0))
              (PDT.depth (PDT.refine t1 tails1)) := by
        exact (max_le_iff.mpr ⟨h0', h1'⟩)
      have hrefine :
          PDT.refine (PDT.node i t0 t1) tails =
            PDT.node i (PDT.refine t0 tails0) (PDT.refine t1 tails1) := rfl
      -- Раскрываем определение глубины узла.
      simpa [PDT.depth, hrefine] using
        (Nat.succ_le_succ hmax)

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

/--
  Каноническая формулировка оценки на число листьев PDT:
  количество листьев не превосходит `2^depth`.

  Это «публичное» имя для использования во внешних модулях, где удобнее
  явно видеть связь depth ↔ leaves, не раскрывая вспомогательную лемму.
-/
theorem PDT.leaves_le_pow2_depth {n : Nat} (t : PDT n) :
    (PDT.leaves t).length ≤ Nat.pow 2 (PDT.depth t) := by
  simpa using (PDT.leaves_length_le_pow_depth t)

/-- Инварианты «хорошего» дерева (пока как булевы проверки/пропозиции, при необходимости усилим):
    1) листья попарно не пересекаются,
    2) объединение листьев покрывает весь рассматриваемый регион.
    На данном шаге держим это как пропозиционное место для будущих лемм. -/
def PDT.WellFormed {n : Nat} (_t : PDT n) : Prop := True  -- placeholder

end Core
end Pnp3
