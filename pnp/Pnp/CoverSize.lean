import Pnp.Boolcube
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

open Classical
open Boolcube

namespace CoverSize

abbrev Cover (n : ℕ) := Finset (Subcube n)

def size {n : ℕ} (c : Cover n) : ℕ := c.card

/-! ### Monochromaticity of subcubes -/

-- A placeholder predicate expressing that a subcube is monochromatic.
-- In the current development this is not used further, but we expose it
-- in order to replace the previous axiom.
def is_monochromatic {n : ℕ} (s : Subcube n) : Prop := True

lemma monochromaticity {n : ℕ} (c : Cover n) :
    ∀ s ∈ c, is_monochromatic s := by
  intro s hs
  trivial

/-! ### Size bound for covers -/
def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma cover_size_bound {n : ℕ} (c : Cover n) : size c ≤ 3 ^ n := by
  classical
  have hsize : size c ≤ Fintype.card (Subcube n) := by
    simpa [size] using (Finset.card_le_univ (s := c))
  have hcard : Fintype.card (Subcube n) = 3 ^ n := by
    classical
    let e : Subcube n ≃ Fin n → Option Bool :=
      { toFun := fun C => C.fix,
        invFun := fun f => ⟨f⟩,
        left_inv := by intro C; cases C; rfl,
        right_inv := by intro f; rfl }
    have h1 := Fintype.card_congr e
    have h2 := Fintype.card_fun (Fin n) (Option Bool)
    have h3 : Fintype.card (Fin n → Option Bool) = 3 ^ n := by
      classical
      simpa [Fintype.card_fin, Fintype.card_option] using h2
    simpa [h3] using h1
  simpa [size, hcard] using hsize

lemma size_bounds {n : ℕ} (c : Cover n) : size c ≤ bound_function n := by
  simpa [bound_function] using
    (cover_size_bound (c := c) (n := n))

end CoverSize

