import Pnp2.Agreement
import Pnp2.BoolFunc
import Pnp2.BoolFunc.Support
import Pnp2.DecisionTree
import Pnp2.low_sensitivity_cover
-- `collentropy` is not imported to keep the legacy library lightweight

open BoolFunc
open Agreement

namespace Pnp2Tests

/-- The support of a constantly false function is empty. -/
example (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

/-- Modifying an irrelevant coordinate leaves the function unchanged. -/
example (x : Point 2) (b : Bool) :
    (fun y : Point 2 => y 0) x = (fun y : Point 2 => y 0) (Point.update x 1 b) := by
  classical
  have hi : (1 : Fin 2) ∉ support (fun y : Point 2 => y 0) := by
    simp [support]
  exact
    BoolFunc.eval_update_not_support
      (f := fun y : Point 2 => y 0) (i := 1) hi x b

/-- If two points agree on all coordinates of `K`, the second lies in the same subcube. -/
example {n : ℕ} {K : Finset (Fin n)} {x y : Point n}
    (h : ∀ i, i ∈ K → x i = y i) :
    y ∈ₛ Subcube.fromPoint x K := by
  simpa using Agreement.mem_fromPoint_of_agree (K := K) (x := x) (y := y) h

/-- If two points agree on `K`, the frozen subcubes coincide. -/
example {n : ℕ} {K : Finset (Fin n)} {x y : Point n}
    (h : ∀ i, i ∈ K → x i = y i) :
    Subcube.fromPoint x K = Subcube.fromPoint y K := by
  simpa using
    Agreement.Subcube.point_eq_core (K := K) (x := x) (x₀ := y) h

/-- Every non-trivial function evaluates to `true` somewhere on its support. -/
example :
    ∃ x, (fun y : Point 1 => y 0) x = true := by
  classical
  have hmem : (0 : Fin 1) ∈ support (fun y : Point 1 => y 0) := by
    have hx : (fun y : Point 1 => y 0) (fun _ => false) ≠
        (fun y : Point 1 => y 0) (Point.update (fun _ => false) 0 true) := by
      simp [Point.update]
    exact mem_support_iff.mpr ⟨fun _ => false, hx⟩
  have hsupp : support (fun y : Point 1 => y 0) ≠ (∅ : Finset (Fin 1)) := by
    intro hempty
    simp [hempty] at hmem
  exact BoolFunc.exists_true_on_support (f := fun y : Point 1 => y 0) hsupp

/-- `Point.update` operations on distinct coordinates commute. -/
example (n : ℕ) (x : Point n) (i j : Fin n) (h : i ≠ j) (b₁ b₂ : Bool) :
    Point.update (Point.update x i b₁) j b₂ =
      Point.update (Point.update x j b₂) i b₁ := by
  classical
  simpa using Point.update_swap (x := x) (i := i) (j := j) h b₁ b₂

/-- A trivial tree has depth zero and one leaf subcube. -/
example :
    (DecisionTree.leaves_as_subcubes (DecisionTree.leaf true : DecisionTree 1)).card = 0 :=
by
  simp [DecisionTree.leaves_as_subcubes]

/-- The depth bound lemma from the legacy library. -/
example (t : DecisionTree 2) :
    (DecisionTree.leaves_as_subcubes t).card ≤ 2 ^ DecisionTree.depth t :=
by
  simpa using DecisionTree.tree_depth_bound (t := t)

/-- A trivial decision tree has at most `2 ^ depth` leaves. -/
example :
    (DecisionTree.leaf true : DecisionTree 1).leaf_count ≤
      2 ^ (DecisionTree.depth (DecisionTree.leaf true : DecisionTree 1)) := by
  have hx :=
    DecisionTree.leaf_count_le_pow_depth
      (t := (DecisionTree.leaf true : DecisionTree 1))
  exact hx

/-- The low-sensitivity cover for a single function exists. -/
example (n s C : ℕ) (f : BFunc n) [Fintype (Point n)]
    (Hs : sensitivity f ≤ s) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ x : Point n, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using
    BoolFunc.low_sensitivity_cover_single
      (n := n) (s := s) (C := C) (f := f) Hs

/-- Dimension of a subcube freezes exactly the chosen coordinates. -/
example {n : ℕ} (x : Point n) (I : Finset (Fin n)) :
    (Agreement.Subcube.fromPoint (n := n) x I).dimension = n - I.card := by
  simp [Agreement.dimension_fromPoint (x := x) (I := I)]

/-- A full subcube is monochromatic for any function. -/
example {n : ℕ} (x : Point n) (f : BFunc n) :
    (Agreement.Subcube.fromPoint (n := n) x Finset.univ).monochromaticFor f := by
  classical
  refine ⟨f x, ?_⟩
  intro y hy
  -- Membership in the fully frozen cube implies equality with `x`.
  have h_eq : ∀ i : Fin n, y i = x i := by
    have hmem := (Agreement.fromPoint_mem (x := x) (I := Finset.univ) (y := y)).1 hy
    intro i; have := hmem i (by simp)
    simpa using this
  -- Hence `f y` evaluates to the same value as `f x`.
  have : y = x := by
    funext i; simpa using (h_eq i)
  simp [this]

/-- Core-agreement for the trivial family containing only the constantly true function. -/
example {n ℓ : ℕ} (x : Point n) :
    Agreement.Subcube.fromPoint (n := n) x Finset.univ |>.monochromaticForFamily
      ({fun _ : Point n => true} : Family n) := by
  classical
  haveI : Agreement.CoreClosed ℓ ({fun _ : Point n => true} : Family n) :=
    { closed_under_ball := by
        intro f hf x y hx hy
        have hf' : f = (fun _ => true) := by
          simpa [Finset.mem_singleton] using hf
        simp [hf'] }
  simpa using
    Agreement.coreAgreement (n := n) (ℓ := ℓ)
      (F := ({fun _ : Point n => true} : Family n))
      (x₁ := x) (x₂ := x) (I := Finset.univ)
      (h_size := by simp)
      (h_agree := by intro i hi; rfl)
      (h_val1 := by
        intro f hf
        have hf' : f = (fun _ : Point n => true) := by
          simpa [Finset.mem_singleton] using hf
        simp [hf'] )



end Pnp2Tests
