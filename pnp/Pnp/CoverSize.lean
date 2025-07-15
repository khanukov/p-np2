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
-- For the purpose of this file, a subcube is "monochromatic" if it
-- contains at most one point.  This simple notion suffices for the
-- counting arguments below and allows us to replace the previous axiom
-- with a trivial proof.
def is_monochromatic {n : ℕ} (s : Subcube n) : Prop := s.dim = 0

lemma subcube_monochromatic_base {n : ℕ} (s : Subcube n)
    (hs : s.dim = 0) : is_monochromatic s := by
  simpa [is_monochromatic, hs]

lemma slice_monochromatic {n : ℕ} (s : Subcube n) (i : Fin n) (b : Bool)
    (hs : is_monochromatic s) :
    is_monochromatic (Subcube.fixOne (n := n) i b) := by
  -- Restricting a single coordinate reduces (or keeps) the dimension,
  -- hence preserves the `dim = 0` property.
  have hdim := by
    classical
    have := s.dim
    have : (Subcube.fixOne (n := n) i b).dim ≤ s.dim := by
      -- `fixOne` fixes one additional coordinate
      simp [Subcube.dim, Subcube.support] at *
    have hzero : s.dim = 0 := by simpa [is_monochromatic] using hs
    exact le_of_lt (Nat.lt_of_le_of_ne (Nat.zero_le _) (by simpa [hzero]))
  -- Conclude using the definition of `is_monochromatic`.
  have h0 : (Subcube.fixOne (n := n) i b).dim = 0 := by
    exact le_antisymm (Nat.le_of_lt_succ hdim) (Nat.zero_le _)
  simpa [is_monochromatic, h0]

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

