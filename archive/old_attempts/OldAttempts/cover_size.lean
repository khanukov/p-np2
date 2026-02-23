/-
cover_size.lean
================

Port of the legacy `CoverSize` module to the `OldAttempts` namespace.
This file defines a minimal notion of cover size and proves a
simple cardinality bound using only elementary combinatorial facts.
The results are self‑contained and do not depend on the core
Family Collision–Entropy Lemma.
-/

import OldAttempts.Boolcube
-- The auxiliary lemmas below are self-contained and do not rely on the
-- more sophisticated parts of the development.
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

open Classical
open Boolcube

namespace CoverSize

/-- A cover of dimension `n` is a finite set of subcubes. -/
abbrev Cover (n : ℕ) := Finset (Subcube n)

/-- The size of a cover is simply its cardinality. -/
def size {n : ℕ} (c : Cover n) : ℕ := c.card

/-! ### Monochromaticity of subcubes

We introduce a placeholder predicate `is_monochromatic`.  In this
minimal development a subcube is "monochromatic" if it has dimension
`0`.  This suffices for the counting lemmas below and matches the
behaviour of the historical version. -/

def is_monochromatic {n : ℕ} (s : Subcube n) : Prop :=
  s.dim = 0

lemma subcube_monochromatic_base {n : ℕ} (s : Subcube n)
    (hs : s.dim = 0) : is_monochromatic s := by
  simpa [is_monochromatic, hs]

-- In this toy development we do not prove any meaningful
-- monochromaticity statement beyond the base case above.

@[simp] lemma size_empty {n : ℕ} :
    size (n := n) (∅ : Cover n) = 0 := by
  simp [size]

lemma size_union_le {n : ℕ} (c₁ c₂ : Cover n) :
    size (c₁ ∪ c₂) ≤ size c₁ + size c₂ := by
  simpa [size] using Finset.card_union_le (s := c₁) (t := c₂)

/-! ### Size bound for covers -/

/-- An explicit upper bound function used in the toy estimate. -/
def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

/-- Every cover has size at most `3^n`.  This follows from the fact that
there are exactly `3^n` subcubes of dimension `n`. -/
lemma cover_size_bound {n : ℕ} (c : Cover n) : size c ≤ 3 ^ n := by
  classical
  have hsize : size c ≤ Fintype.card (Subcube n) := by
    simpa [size] using (Finset.card_le_univ (s := c))
  have hcard : Fintype.card (Subcube n) = 3 ^ n := by
    classical
    -- `Subcube n` is isomorphic to the function space `Fin n → Option Bool`
    -- via the `fix` map.
    let e : Subcube n ≃ Fin n → Option Bool :=
      { toFun := fun C => C.fix,
        invFun := fun f => { fix := f },
        left_inv := by intro C; cases C; rfl,
        right_inv := by intro f; rfl }
    have h1 := Fintype.card_congr e
    -- compute the cardinality of the function space directly
    have h2 := Fintype.card_fun (Fin n) (Option Bool)
    have h3 : Fintype.card (Fin n → Option Bool) = 3 ^ n := by
      classical
      simpa [Fintype.card_fin, Fintype.card_option] using h2
    simpa [h3] using h1
  simpa [size, hcard] using hsize

-- The historical development related the bound above to the entropy
-- drop lemma.  We omit this connection here since it plays no role in
-- the simplified port.

end CoverSize

