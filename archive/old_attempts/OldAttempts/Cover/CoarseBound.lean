import OldAttempts.BoolFunc
import OldAttempts.Boolcube
import OldAttempts.Cover.Uncovered
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

-- This file is purely technical; silence stylistic linter warnings.
set_option linter.unnecessarySimpa false

namespace Cover2

/-!
### Coarse bound on the number of uncovered pairs

This file isolates a *very* simple counting argument about uncovered points.
Separating the reasoning into its own module keeps the main construction in
`cover2.lean` focused on the combinatorics while still providing an easy-to-use
upper bound on the size of the set of uncovered pairs.

An uncovered pair consists of a Boolean function `f` from the family and a
point `x` of the Boolean cube such that `f x = true` but `x` is missing from all
currently chosen rectangles.  Forgetting all structural information about the
rectangles, we can simply count the possible choices of `f` and `x`.

There are at most `F.card` options for the function and `2^n` options for the
point.  Consequently the uncovered set cannot contain more than `F.card * 2^n`
elements.  While this bound is extremely coarse, it is sufficient for basic
sanity checks and for establishing termination measures in preliminary
experiments.
-/

/-
At the heart of the argument lies the following observation: every element of
the uncovered set determines a function `f ∈ F` together with a point `x` from
the Boolean cube.  Disregarding the additional property that `x` is actually
uncovered, this gives an injection into the simple sigma-type `F × 2^n`.  The
cardinality of the latter factorises into the product `F.card * 2^n`, which
immediately bounds the uncovered set.
-/
lemma uncovered_card_bound (F : Family n) (Rset : Finset (Subcube n)) :
    (uncovered (n := n) F Rset).toFinset.card ≤ F.card * 2 ^ n := by
  classical
  -- We explicitly construct the embedding described above.  Every uncovered
  -- pair maps to its function together with the underlying point of the cube.
  have embed : (uncovered (n := n) F Rset).toFinset ⊆
      F.sigma (fun _ => (Finset.univ : Finset (Point n))) := by
    intro p hp
    -- `hp` certifies that `p` is uncovered.  From this we read off membership of
    -- the function component in `F` and that the point lies in the cube.
    have hp' : p ∈ uncovered (n := n) F Rset := by simpa using hp
    rcases hp' with ⟨hf, hx, _⟩
    -- Every point of the Boolean cube is, tautologically, an element of `univ`.
    have hx' : p.2 ∈ (Finset.univ : Finset (Point n)) := by simp
    -- Package the information in the sigma-type `F × 2^n`.
    exact Finset.mem_sigma.mpr ⟨hf, hx'⟩
  -- Taking cardinalities, the subset relation yields the desired inequality.
  have hcard := Finset.card_le_card embed
  -- For a sigma-type with constant fibre, the cardinality splits into a
  -- product.  This corresponds to the counting argument "choose `f` and then
  -- choose `x`".
  have hprod : (F.sigma fun _ => (Finset.univ : Finset (Point n))).card =
      F.card * (Finset.univ : Finset (Point n)).card := by
    classical
    simpa [Finset.card_sigma, Finset.sum_const, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc]
  -- The n-dimensional Boolean cube has exactly `2^n` points.
  have hcube : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
    simpa using (Fintype.card_vector (α := Bool) (n := n))
  -- Combine the previous facts and rewrite to obtain the final inequality.
  simpa [hprod, hcube] using hcard

/--
Specialisation of `uncovered_card_bound` to the initial situation where the
rectangle set is empty.  This lemma merely packages the bound in a convenient
form for callers concerned with the starting configuration of the algorithm.
-/
lemma uncovered_init_coarse_bound (F : Family n) :
    (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤
      F.card * 2 ^ n := by
  -- This is just `uncovered_card_bound` with `Rset = ∅`.  The additional lemma
  -- exists only for convenience when reasoning about the starting state of the
  -- cover construction.
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
  -- If the family itself is empty, the uncovered set is obviously empty.  The
  -- goal therefore reduces to a simple inequality `0 ≤ n`.
  have hcard :
      (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card = 0 := by
    simpa [uncovered, hF]
  -- Rewriting the goal makes the statement immediate.
  have hgoal :
      (uncovered (n := n) F (∅ : Finset (Subcube n))).toFinset.card ≤ n := by
    rw [hcard]
    exact Nat.zero_le n
  exact hgoal

end Cover2

