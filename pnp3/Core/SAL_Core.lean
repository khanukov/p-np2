/-
  pnp3/Core/SAL_Core.lean

  Ядро Switching-Atlas Lemma (SAL).
  Абстрагируем Shrinkage как наличие общего PDT малой глубины и выбора листьев для каждого f с малой ошибкой.
  Тогда SAL строит общий атлас из листьев PDT и утверждает, что он "работает" для семейства.
-/
import Std.Data.List.Basic
import PnP3.Core.BooleanBasics
import PnP3.Core.PDT
import PnP3.Core.Atlas

namespace PnP3.Core

open PnP3.Core

/-- Семейство функций как список (для удобства перебора). -/
abbrev Family (n : Nat) := List (BitVec n → Bool)

/-- Абстрактная "усадка" (Shrinkage):
    существует ОБЩЕЕ PDT глубины ≤ t и для каждого f ∈ F задан поднабор листьев (Rf),
    дающий ошибку ≤ ε. -/
structure Shrinkage (n : Nat) [DecidableEq (Subcube n)] where
  F        : Family n
  t        : Nat
  ε        : Q
  tree     : PDT n
  depth_le : PDT.depth tree ≤ t
  Rsel     : (BitVec n → Bool) → List (Subcube n)  -- выбор подмножеств листьев для каждого f
  Rsel_sub : ∀ f, f ∈ F → listSubset (Rsel f) (PDT.leaves tree)
  err_le   : ∀ f, f ∈ F → errU f (Rsel f) ≤ ε

/-- SAL: из Shrinkage строим атлас с dict = листья PDT, ε = заданное, который "работает" для F. -/
theorem SAL_from_Shrinkage {n : Nat} [DecidableEq (Subcube n)]
  (S : Shrinkage n) :
  WorksFor (Atlas.ofPDT S.tree S.ε) S.F := by
  intro f hf
  -- Возьмём R_f как предписано shrinkage'ем
  refine ⟨S.Rsel f, ?subset, ?err⟩
  · -- R_f ⊆ leaves(tree)
    exact S.Rsel_sub f hf
  · -- errU f R_f ≤ ε
    exact S.err_le f hf

/-- Удобная оболочка: сам атлас из Shrinkage. -/
def Atlas.fromShrinkage {n : Nat} [DecidableEq (Subcube n)]
  (S : Shrinkage n) : Atlas n :=
  Atlas.ofPDT S.tree S.ε

/-- Параметрический факт о размере словаря:
    число листьев PDT не превосходит `2^{depth}`. -/
theorem leaves_count_bound {n : Nat} (t : PDT n) :
  (PDT.leaves t).length ≤ Nat.pow 2 (PDT.depth t) :=
  PDT.leaves_length_le_pow_depth t

end PnP3.Core
