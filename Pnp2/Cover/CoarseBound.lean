import Pnp2.BoolFunc
import Pnp2.Boolcube
import Pnp2.Cover.Uncovered
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

/-!
### Coarse bound on the number of uncovered pairs

The lemmas in this file provide a very rough estimate on the size of the set
of *uncovered pairs*.  An uncovered pair consists of a Boolean function `f`
from the family and a point `x` of the Boolean cube such that `f x = true` but
no rectangle in the current rectangle set contains `x`.

Ignoring the structure of the rectangles gives an immediate bound: there are at
most `F.card` choices for `f` and `2^n` choices for `x`.  Hence the uncovered
set cannot contain more than `F.card * 2^n` elements.  Even though the estimate
is extremely coarse, it suffices for quick sanity checks and keeps the
combinatorial development in `cover2.lean` uncluttered.
-/

/--
Each uncovered pair `(f, x)` comes from a function `f` in the family and a point
`x` of the cube.  Forgetting that uncovered points satisfy additional
properties, we embed the uncovered set into the simple product `F × 2^n` and use
a cardinality argument to derive the coarse upper bound.
-/
lemma uncovered_card_bound (F : Family n) (Rset : Finset (Subcube n)) :
    (uncovered (n := n) F Rset).toFinset.card ≤ F.card * 2 ^ n := by
  classical
  -- Map every uncovered pair into the sigma-type of a function and a cube point.
  have hsubset : (uncovered (n := n) F Rset).toFinset ⊆
      F.sigma (fun _ => (Finset.univ : Finset (Point n))) := by
    intro p hp
    -- Recover the proof that `p` is uncovered to extract information about its
    -- components.
    have hp' : p ∈ uncovered (n := n) F Rset := by simpa using hp
    rcases hp' with ⟨hf, hx, _⟩
    -- Every point of the cube lies in `Finset.univ`.
    have hx' : p.2 ∈ (Finset.univ : Finset (Point n)) := by simp
    -- Assemble the pair in the sigma-type.
    exact Finset.mem_sigma.mpr ⟨hf, hx'⟩
  -- Cardinalities respect subsets: the uncovered set is at most as large as the
  -- sigma-type it embeds into.
  have hcard := Finset.card_le_card hsubset
  -- For a constant fibre the sigma-type cardinality factorises into a product.
  have hprod : (F.sigma fun _ => (Finset.univ : Finset (Point n))).card =
      F.card * (Finset.univ : Finset (Point n)).card := by
    classical
    simpa [Finset.card_sigma, Finset.sum_const, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc]
  -- The Boolean cube of dimension `n` has exactly `2^n` points.
  have hcube : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
    simpa using (Fintype.card_vector (α := Bool) (n := n))
  -- Putting the pieces together yields the advertised bound.
  simpa [hprod, hcube] using hcard

/--
Specialisation of `uncovered_card_bound` to the initial situation where the
rectangle set is empty.  This lemma merely packages the bound in a convenient
form for callers concerned with the starting configuration of the algorithm.
-/
lemma uncovered_init_coarse_bound (F : Family n) :
    (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤
      F.card * 2 ^ n := by
  simpa using
    (uncovered_card_bound (n := n) (F := F)
      (Rset := (∅ : Finset (Subcube n))))

/--
When the family `F` itself is empty the uncovered set is empty as well.  In this
case any upper bound holds trivially; we record a simple instance with the
ambient dimension `n` for easy reuse in examples and tests.
-/
lemma uncovered_init_bound_empty (F : Family n) (hF : F = (∅ : Family n)) :
    (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤ n := by
  classical
  -- An empty family yields no uncovered pairs, hence the cardinality is zero.
  have hcard :
      (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card = 0 := by
    simpa [uncovered, hF]
  -- Replace the goal with `0 ≤ n` and discharge it using `Nat.zero_le`.
  have hgoal :
      (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤ n := by
    rw [hcard]
    exact Nat.zero_le n
  exact hgoal

end Cover2

