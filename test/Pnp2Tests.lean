import Pnp2.Agreement
import Pnp2.BoolFunc
import Pnp2.BoolFunc.Support
import Pnp2.DecisionTree
import Pnp2.low_sensitivity_cover
-- `collentropy` is not imported to keep the legacy library lightweight

set_option linter.unnecessarySimpa false

open BoolFunc
open Agreement

namespace Pnp2Tests

/-- The support of a constantly false function is empty. -/
example (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]
/-- The support of a constantly true function is empty. -/
example (n : ℕ) :
    support (fun _ : Point n => true) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

/-- Constant functions have zero sensitivity. -/
example (n : ℕ) [Fintype (Point n)] :
    BoolFunc.sensitivity (fun _ : Point n => false) = 0 := by
  simp [BoolFunc.sensitivity_const]

example (n : ℕ) [Fintype (Point n)] :
    BoolFunc.sensitivity (fun _ : Point n => true) = 0 := by
  simp [BoolFunc.sensitivity_const]


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
example (n s : ℕ) (f : BFunc n) [Fintype (Point n)]
    (Hs : sensitivity f ≤ s) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
    (∀ x : Point n, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ coverBound n s := by
  classical
  have hfamily : ∀ g ∈ ({f} : Family n), sensitivity g ≤ s := by
    intro g hg
    have hg' : g = f := by simpa [Finset.mem_singleton] using hg
    simpa [hg'] using Hs
  simpa using
    BoolFunc.decisionTree_cover (F := ({f} : Family n)) (s := s) hfamily

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

/-- A point outside a subcube reveals the flipped coordinate. -/
example :
    ∃ (i : Fin 1)
      (hi : i ∈ (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).idx),
        (fun _ : Fin 1 => true) i =
          ! (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).val i hi := by
  classical
  have hx :
      ¬ (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).mem
          (fun _ => true) := by
    simp [Agreement.Subcube.fromPoint, Subcube.mem]
  simpa using
    not_mem_subcube_exists_mismatch_eq
      (R := Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0})
      (x := fun _ : Fin 1 => true) hx

/-- The single-branch outside cover lemma applies to the one-bit family. -/
example :
    ∃ Rset : Finset (Subcube 1),
      (∀ f ∈ ({fun x : Point 1 => x 0} : Family 1),
          ∀ R' ∈ Rset, Subcube.monochromaticFor R' f) ∧
      (∀ f ∈ ({fun x : Point 1 => x 0} : Family 1),
          ∀ x,
            x 0 = ! (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).val
                0 (by decide) →
              f x = true → ∃ R' ∈ Rset, x ∈ₛ R') ∧
      Rset.card ≤ Cover2.mBound 1 (1 + 1) := by
  classical
  -- Instantiate `cover_outside_one_index` for the sole coordinate `0`.
  simpa using
    cover_outside_one_index
      (F := ({fun x : Point 1 => x 0} : Family 1))
      (i := 0)
      (R := Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0})
      (hnpos := by decide)
      (hi := by decide)

/-- The outside cover lemma applies to a simple one-bit family. -/
example :
    ∃ Rset : Finset (Subcube 1),
      (∀ f ∈ ({fun x : Point 1 => x 0} : Family 1),
          ∀ R' ∈ Rset, Subcube.monochromaticFor R' f) ∧
      (∀ f ∈ ({fun x : Point 1 => x 0} : Family 1),
          ∀ x, ¬ (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).mem x →
            f x = true → ∃ R' ∈ Rset, x ∈ₛ R') ∧
      Rset.card ≤
        (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).idx.card *
          Cover2.mBound 1 (1 + 1) := by
  classical
  -- Directly instantiate `cover_outside_common_cube_all`.
  simpa using
    cover_outside_common_cube_all
      (F := ({fun x : Point 1 => x 0} : Family 1))
      (R := Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0})
      (hnpos := by decide)

/-- Combine a monochromatic subcube with its exterior cover. -/
noncomputable example :
    CoverResP (F := ({fun x : Point 1 => x 0} : Family 1))
      (1 +
        (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}).idx.card *
          Cover2.mBound 1 (1 + 1)) := by
  classical
  -- The subcube fixing coordinate `0` to `false` is monochromatic for the family.
  have hmonoR :
      ∀ f ∈ ({fun x : Point 1 => x 0} : Family 1),
        Subcube.monochromaticFor
          (Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0}) f := by
    intro f hf
    have hf' : f = (fun x : Point 1 => x 0) := by
      simpa [Finset.mem_singleton] using hf
    subst hf'
    refine ⟨false, ?_⟩
    intro y hy
    have : y 0 = false := hy 0 (by decide)
    simpa [this]
  -- Instantiate the combined cover.
  simpa using
    cover_with_common_cube
      (F := ({fun x : Point 1 => x 0} : Family 1))
      (R := Agreement.Subcube.fromPoint (n := 1) (fun _ => false) {0})
      (hnpos := by decide)
      (hmono := hmonoR)

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

/-!
The specialised decision-tree cover lemmas have simple instances for
trivial families.  We verify the constant-family case here to ensure
that the base lemmas are usable in tests.
-/
example {n s : ℕ} [Fintype (Point n)] :
    ∃ Rset : Finset (Subcube n),
      (∀ f ∈ ({fun _ : Point n => true} : Family n),
          ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ f ∈ ({fun _ : Point n => true} : Family n),
          ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Build the constant witness required by `decisionTree_cover_of_constant`.
  have hconst : ∃ b, ∀ f ∈ ({fun _ : Point n => true} : Family n), ∀ x, f x = b :=
    by
      refine ⟨true, ?_⟩
      intro f hf x
      -- Membership in the singleton family pins down `f`.
      have : f = (fun _ : Point n => true) := by
        simpa [Finset.mem_singleton] using hf
      simp [this]
  -- Apply the constant-family cover lemma.
  simpa using
    BoolFunc.decisionTree_cover_of_constant
      (F := ({fun _ : Point n => true} : Family n))
      (s := s) hconst

/-- Every evaluation/path pair computed by a decision tree occurs in its
`coloredSubcubes` set.  We simply invoke the lemma
`eval_pair_mem_coloredSubcubes`. -/
example {n : ℕ} (t : DecisionTree n) (x : Point n) :
    ⟨DecisionTree.eval_tree t x,
      DecisionTree.subcube_of_path ((DecisionTree.path_to_leaf t x).reverse)⟩ ∈
      DecisionTree.coloredSubcubes (n := n) t := by
  classical
  simpa using
    DecisionTree.eval_pair_mem_coloredSubcubes (t := t) (x := x)

/-- Restricting along a concatenated path is equivalent to
    applying the restrictions sequentially. -/
example {n : ℕ} (F : Family n) (p q : List (Fin n × Bool)) :
    BoolFunc.Family.restrictPath (n := n) (F := F) (p ++ q) =
      BoolFunc.Family.restrictPath (n := n)
        (F := BoolFunc.Family.restrictPath (n := n) (F := F) q) p := by
  classical
  simpa using
    BoolFunc.Family.restrictPath_append (F := F) (p := p) (q := q)

/-- The subcube recorded by a two-step path freezes exactly two coordinates. -/
example :
    (DecisionTree.subcube_of_path
        (n := 2) [(⟨0, by decide⟩, true), (⟨1, by decide⟩, false)]).idx.card = 2 :=
by
  classical
  simp [DecisionTree.subcube_of_path]

/--
The helper lemma `exists_large_insensitive_subset_div_of_support` produces a
nontrivial insensitive set for simple projection functions.  Here the function
depends only on the first coordinate, so the remaining two coordinates form a
valid insensitive subset.
-/
example :
    ∃ A : Finset (Fin 3),
      3 / (2 * 1) ≤ A.card ∧
      (∀ ⦃T : Finset (Fin 3)⦄, T ⊆ A →
        (fun x : Point 3 => x 0) (Point.flip (fun _ => false) T) = (fun _ => false) 0) := by
  classical
  -- Define the projection function explicitly.
  let f : BFunc 3 := fun x => x 0
  -- The support of `f` is the singleton `{0}`.
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  -- Invoke the specialised insensitive-set lemma and simplify the result.
  have :=
    BoolFunc.exists_large_insensitive_subset_div_of_support
      (f := f) (s := 1) (hsupp := hsupp) (x := fun _ => false)
  simpa [f] using this

/--
The pointwise support-based lemma ensures that any point agreeing with the
reference outside the extracted set yields the same evaluation. -/
example :
    ∃ A : Finset (Fin 3),
      3 / (2 * 1) ≤ A.card ∧
      (∀ {y : Point 3}, (∀ i ∉ A, y i = (fun _ => false) i) →
        (fun x : Point 3 => x 0) y = (fun _ => false) 0) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have :=
    BoolFunc.exists_large_insensitive_subset_pointwise_div_of_support
      (f := f) (s := 1) (hsupp := hsupp) (x := fun _ => false)
  simpa [f] using this

/--
A small support bound guarantees a sizeable set of globally insensitive
coordinates.  For the projection onto the first bit, at least one of the
remaining variables is globally irrelevant.
-/
example :
    3 / (2 * 1) ≤ (BoolFunc.insensitiveCoords (fun x : Point 3 => x 0)).card := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  -- Apply the cardinality bound and simplify.
  simpa [f]
    using
      BoolFunc.insensitiveCoords_card_ge_div_of_support
        (f := f) (s := 1) (hsupp := hsupp)

/-- The support-based subcube lemma yields a monochromatic region of size
`n / (2*s)` for simple projection functions. -/
    example :
        ∃ R : Subcube 3,
        ((fun _ => false : Point 3) ∈ₛ R) ∧
        (Subcube.monochromaticFor R (fun x : Point 3 => x 0)) ∧
        (3 / (2 * 1) ≤ R.dimension) := by
  classical
  -- Projection to the first coordinate depends on only one bit.
  let f : BFunc 3 := fun x => x 0
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  -- Apply the subcube variant and simplify.
  simpa [f]
    using
      BoolFunc.exists_large_monochromatic_subcube_div_of_support
        (f := f) (s := 1) (hsupp := hsupp) (x := fun _ => false)

/-- The large subcube from the combined lemma sits inside the local
`insensitiveSubcubeAt` of the base point. -/
example :
    ∃ R : Subcube 3,
      ((fun _ => false : Point 3) ∈ₛ R) ∧
      (Subcube.monochromaticFor R (fun x : Point 3 => x 0)) ∧
      (3 / (2 * 1) ≤ R.dimension) ∧
      (∀ y : Point 3, (y ∈ₛ R) →
        y ∈ₛ BoolFunc.insensitiveSubcubeAt (fun x : Point 3 => x 0)
            (fun _ => false)) := by
  classical
  -- Projection depends only on the first coordinate, so the complement is safe.
  let f : BFunc 3 := fun x => x 0
  have hsens : BoolFunc.sensitivity f ≤ 1 := by decide
  have hsupp : (BoolFunc.support f).card ≤ 3 - 3 / (2 * 1) := by decide
  -- Apply the new lemma and simplify.
  simpa [f]
    using
      BoolFunc.exists_large_monochromatic_subcube_div_subset_insensitiveSubcubeAt
        (f := f) (s := 1) (hs := hsens)
        (hbound := Or.inr hsupp) (x := fun _ => false)

/--
`exists_large_monochromatic_subcube_div_subset_insensitiveCoordsAt` refines the
previous result by explicitly placing the free coordinates inside
`insensitiveCoordsAt`.  For the projection function all nonzero indices are
locally insensitive around the all-false point, yielding a subcube of
dimension `2`.-/
example :
    ∃ R : Subcube 3,
      ((fun _ => false : Point 3) ∈ₛ R) ∧
      (Subcube.monochromaticFor R (fun x : Point 3 => x 0)) ∧
      (3 / (2 * 1) ≤ R.dimension) ∧
      ((Finset.univ \ R.idx) ⊆
        BoolFunc.insensitiveCoordsAt (fun x : Point 3 => x 0)
          (fun _ => false)) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hsens : BoolFunc.sensitivity f ≤ 1 := by decide
  have hsupp : (BoolFunc.support f).card ≤ 3 - 3 / (2 * 1) := by decide
  simpa [f]
    using
      BoolFunc.exists_large_monochromatic_subcube_div_subset_insensitiveCoordsAt
        (f := f) (s := 1) (hs := hsens)
        (hbound := Or.inr hsupp) (x := fun _ => false)

/--
From a pointwise invariant set one can extract an explicit monochromatic
subcube.  For the projection function flipping the nonessential coordinates
`1` and `2` leaves the value unchanged, yielding a subcube of dimension `2`.
-/
example :
    ∃ R : Subcube 3,
      ((fun _ => false : Point 3) ∈ₛ R) ∧
      (Subcube.monochromaticFor R (fun x : Point 3 => x 0)) ∧
      R.dimension = 2 := by
  classical
  -- Coordinates `1` and `2` are irrelevant for the first projection.
  let f : BFunc 3 := fun x => x 0
  let x0 : Point 3 := fun _ => false
  have hA : ∀ ⦃y : Point 3⦄,
      (∀ i ∉ ({1, 2} : Finset (Fin 3)), y i = x0 i) → f y = f x0 := by
    intro y hy
    have hy0 : y 0 = x0 0 := hy 0 (by decide)
    simpa [f, x0, hy0]
  obtain ⟨R, hx, hmono, hdim⟩ :=
    BoolFunc.monochromaticSubcube_of_pointwise
      (f := f) (x := x0) (A := ({1, 2} : Finset (Fin 3))) (hA := hA)
  have hcard : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  exact ⟨R, hx, hmono, by simpa [hcard] using hdim⟩

/--
Pointwise version of the support-based subcube lemma applied to a projection
function.  The resulting subcube varies only on the nonessential coordinates
and has the expected dimension `n / (2*s)`.
-/
example :
    ∃ R : Subcube 3,
      ((fun _ => false : Point 3) ∈ₛ R) ∧
      (Subcube.monochromaticFor R (fun x : Point 3 => x 0)) ∧
      (3 / (2 * 1) ≤ R.dimension) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  -- Apply the pointwise subcube lemma and simplify.
  simpa [f]
    using
      BoolFunc.exists_large_monochromatic_subcube_pointwise_div_of_support
        (f := f) (s := 1) (hsupp := hsupp) (x := fun _ => false)

/--
The combined lemma accepts either a small global bound or a bound on the
support.  For the projection onto the first bit the support condition suffices
to obtain an insensitive set of size `n/(2*s)`.
-/
example :
    ∃ A : Finset (Fin 3),
      3 / (2 * 1) ≤ A.card ∧
      (∀ ⦃T : Finset (Fin 3)⦄, T ⊆ A →
        (fun x : Point 3 => x 0) (Point.flip (fun _ => false) T) =
          (fun _ => false) 0) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hs : BoolFunc.sensitivity f ≤ 1 := by
    have : BoolFunc.sensitivity f = 1 := by decide
    simp [this]
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have hbound :
      Fintype.card (Point 3) * 1 ≤ 3 - 3 / (2 * 1) ∨
        (support f).card ≤ 3 - 3 / (2 * 1) := Or.inr hsupp
  have :=
    BoolFunc.exists_large_insensitive_subset_div
      (f := f) (s := 1) (hs := hs) (hbound := hbound)
      (x := fun _ => false)
  simpa [f] using this

/-- Pointwise version of the combined insensitive-set lemma. -/
example :
    ∃ A : Finset (Fin 3),
      3 / (2 * 1) ≤ A.card ∧
      (∀ {y : Point 3}, (∀ i ∉ A, y i = (fun _ => false) i) →
        (fun x : Point 3 => x 0) y = (fun _ => false) 0) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hs : BoolFunc.sensitivity f ≤ 1 := by
    have : BoolFunc.sensitivity f = 1 := by decide
    simpa [this]
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have hbound :
      Fintype.card (Point 3) * 1 ≤ 3 - 3 / (2 * 1) ∨
        (support f).card ≤ 3 - 3 / (2 * 1) := Or.inr hsupp
  have :=
    BoolFunc.exists_large_insensitive_subset_pointwise_div
      (f := f) (s := 1) (hs := hs) (hbound := hbound)
      (x := fun _ => false)
  simpa [f] using this

/--
The nested subcube lemma yields a large set of locally insensitive coordinates
contained in `insensitiveCoordsAt` around the reference point.
-/
example :
    ∃ A : Finset (Fin 3),
      3 / (2 * 1) ≤ A.card ∧
      A ⊆ BoolFunc.insensitiveCoordsAt (fun x : Point 3 => x 0) (fun _ => false) ∧
      (∀ ⦃T : Finset (Fin 3)⦄, T ⊆ A →
        (fun x : Point 3 => x 0) (Point.flip (fun _ => false) T) =
          (fun _ => false) 0) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hs : BoolFunc.sensitivity f ≤ 1 := by
    have : BoolFunc.sensitivity f = 1 := by decide
    simpa [this]
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have hbound :
      Fintype.card (Point 3) * 1 ≤ 3 - 3 / (2 * 1) ∨
        (support f).card ≤ 3 - 3 / (2 * 1) := Or.inr hsupp
  have h :=
    BoolFunc.exists_large_insensitive_subset_div_subset_insensitiveCoordsAt
      (f := f) (s := 1) (hs := hs) (hbound := hbound)
      (x := fun _ => false)
  simpa [f] using h

/-- Pointwise variant of the locally insensitive set lemma. -/
example :
    ∃ A : Finset (Fin 3),
      3 / (2 * 1) ≤ A.card ∧
      A ⊆ BoolFunc.insensitiveCoordsAt (fun x : Point 3 => x 0) (fun _ => false) ∧
      (∀ {y : Point 3}, (∀ i ∉ A, y i = (fun _ => false) i) →
        (fun x : Point 3 => x 0) y = (fun _ => false) 0) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hs : BoolFunc.sensitivity f ≤ 1 := by
    have : BoolFunc.sensitivity f = 1 := by decide
    simpa [this]
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have hbound :
      Fintype.card (Point 3) * 1 ≤ 3 - 3 / (2 * 1) ∨
        (support f).card ≤ 3 - 3 / (2 * 1) := Or.inr hsupp
  have h :=
    BoolFunc.exists_large_insensitive_subset_pointwise_div_subset_insensitiveCoordsAt
      (f := f) (s := 1) (hs := hs) (hbound := hbound)
      (x := fun _ => false)
  simpa [f] using h

/--
Combining the numeric alternatives also yields a large monochromatic
subcube under the same assumptions.
-/
example :
    ∃ R : Subcube 3,
      ((fun _ => false : Point 3) ∈ₛ R) ∧
      (Subcube.monochromaticFor R (fun x : Point 3 => x 0)) ∧
      (3 / (2 * 1) ≤ R.dimension) := by
  classical
  let f : BFunc 3 := fun x => x 0
  have hs : BoolFunc.sensitivity f ≤ 1 := by
    have : BoolFunc.sensitivity f = 1 := by decide
    simpa [this]
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have hbound :
      Fintype.card (Point 3) * 1 ≤ 3 - 3 / (2 * 1) ∨
        (support f).card ≤ 3 - 3 / (2 * 1) := Or.inr hsupp
  have :=
    BoolFunc.exists_large_monochromatic_subcube_div
      (f := f) (s := 1) (hs := hs) (hbound := hbound)
      (x := fun _ => false)
  simpa [f] using this

/--
The combined cardinality lemma unifies the two numeric alternatives,
recovering the support-based bound as a special case. -/
example :
    3 / (2 * 1) ≤
      (BoolFunc.insensitiveCoords (fun x : Point 3 => x 0)).card := by
  classical
  let f : BFunc 3 := fun x => x 0
  -- Sensitivity of a projection is one, hence bounded by `1`.
  have hs : BoolFunc.sensitivity f ≤ 1 := by
    have : BoolFunc.sensitivity f = 1 := by decide
    simpa [this]
  -- The support bound witnesses the right side of the disjunction.
  have hsupp : (support f).card ≤ 3 - 3 / (2 * 1) := by decide
  have hbound :
      Fintype.card (Point 3) * 1 ≤ 3 - 3 / (2 * 1) ∨
        (support f).card ≤ 3 - 3 / (2 * 1) := Or.inr hsupp
  -- Invoke the combined lemma and simplify.
  simpa [f]
    using
      BoolFunc.insensitiveCoords_card_ge_div
        (f := f) (s := 1) (hs := hs) (hbound := hbound)

/--
The coarse numeric condition `2^n * s ≤ n - n/(2*s)` combined with a global
  sensitivity bound already ensures a large set of globally insensitive
  coordinates.  For a constant function the inequality holds trivially, so the
  entire cube is recognised as insensitive.
-/
example :
    2 / (2 * 0) ≤
      (BoolFunc.insensitiveCoords (fun _ : Point 2 => false)).card := by
  classical
  have hs : BoolFunc.sensitivity (fun _ : Point 2 => false) ≤ 0 := by decide
  have hsmall : Fintype.card (Point 2) * 0 ≤ 2 - 2 / (2 * 0) := by decide
  simpa
    using
      BoolFunc.insensitiveCoords_card_ge_div_of_small
        (f := fun _ : Point 2 => false) (s := 0)
        (hs := hs) (hsmall := hsmall)

/--
The combined lemma also handles the coarse inequality case directly. -/
example :
    2 / (2 * 0) ≤
      (BoolFunc.insensitiveCoords (fun _ : Point 2 => false)).card := by
  classical
  have hs : BoolFunc.sensitivity (fun _ : Point 2 => false) ≤ 0 := by decide
  have hbound :
      Fintype.card (Point 2) * 0 ≤ 2 - 2 / (2 * 0) ∨
        (support (fun _ : Point 2 => false)).card ≤ 2 - 2 / (2 * 0) :=
    Or.inl (by decide)
  simpa
    using
      BoolFunc.insensitiveCoords_card_ge_div
        (f := fun _ : Point 2 => false) (s := 0)
        (hs := hs) (hbound := hbound)

/--
The small-sensitivity assumption can directly yield a monochromatic subcube of
size `n / (2*s)`.  In the degenerate case `s = 0` this produces a trivial
subcube containing any point.
-/
example :
    ∃ R : Subcube 2,
      ((fun _ => false : Point 2) ∈ₛ R) ∧
      (Subcube.monochromaticFor R (fun _ : Point 2 => false)) ∧
      (2 / (2 * 0) ≤ R.dimension) := by
  classical
  have hs : sensitivity (fun _ : Point 2 => false) ≤ 0 := by decide
  have hsmall : Fintype.card (Point 2) * 0 ≤ 2 - 2 / (2 * 0) := by decide
  simpa
    using
      BoolFunc.exists_large_monochromatic_subcube_div_of_small
        (f := fun _ : Point 2 => false) (s := 0)
        (hs := hs) (hsmall := hsmall) (x := fun _ => false)

/-- Support coordinates have positive coordinate sensitivity. -/
example :
    0 < BoolFunc.coordSensitivity (fun x : Point 3 => x 0)
        (⟨0, by decide⟩ : Fin 3) := by
  classical
  have hi : (⟨0, by decide⟩ : Fin 3) ∈
      BoolFunc.support (fun x : Point 3 => x 0) := by
    refine (BoolFunc.mem_support_iff (f := fun x : Point 3 => x 0)
        (i := ⟨0, by decide⟩)).2 ?_
    refine ⟨(fun _ => false), ?_⟩
    simp
  simpa using
    BoolFunc.coordSensitivity_pos_of_mem_support
      (f := fun x : Point 3 => x 0) (i := ⟨0, by decide⟩) hi

/-- Supported coordinates contribute at least two to the total sensitivity. -/
example :
    2 ≤ BoolFunc.coordSensitivity (fun x : Point 3 => x 0)
        (⟨0, by decide⟩ : Fin 3) := by
  classical
  have hi : (⟨0, by decide⟩ : Fin 3) ∈
      BoolFunc.support (fun x : Point 3 => x 0) := by
    refine (BoolFunc.mem_support_iff (f := fun x : Point 3 => x 0)
        (i := ⟨0, by decide⟩)).2 ?_
    refine ⟨(fun _ => false), ?_⟩
    simp
  simpa using
    BoolFunc.two_le_coordSensitivity_of_mem_support
      (f := fun x : Point 3 => x 0) (i := ⟨0, by decide⟩) hi

/-- Monochromatic subcubes around a point cannot exceed the local
`insensitiveSubcubeAt`. -/
example :
    let f : BFunc 3 := fun x => x 0
    let x : Point 3 := fun _ => false
    ∃ R : Subcube 3,
      (x ∈ₛ R) ∧
      Subcube.monochromaticFor R f ∧
      R.dimension ≤ (BoolFunc.insensitiveSubcubeAt f x).dimension := by
  classical
  let f : BFunc 3 := fun x => x 0
  let x : Point 3 := fun _ => false
  have hA : ({1, 2} : Finset (Fin 3)) ⊆ BoolFunc.insensitiveCoords f := by decide
  obtain ⟨R, hxR, hmono, _hdimR⟩ :=
    BoolFunc.monochromaticSubcube_of_insensitive_subset
      (f := f) (A := ({1,2} : Finset (Fin 3))) (hA := hA) (x := x)
  refine ⟨R, hxR, hmono, ?_⟩
  exact
    BoolFunc.monochromaticSubcube_dim_le_insensitiveSubcubeAt_dim
      (f := f) (R := R) (x := x) (hxR := hxR) (hmono := hmono)

  /-- From a monochromatic subcube we can extract an insensitive set of equal
  size.  Flipping any subset of the free coordinate preserves the function's
  value. -/
  example :
      let f : BFunc 2 := fun x => x 0
      let x : Point 2 := fun _ => false
      let R : Subcube 2 := { idx := ({0} : Finset (Fin 2)), val := fun _ _ => false }
      ∃ A : Finset (Fin 2), R.dimension = A.card ∧
        ∀ ⦃T : Finset (Fin 2)⦄, T ⊆ A → f (Point.flip x T) = f x := by
    classical
    let f : BFunc 2 := fun x => x 0
    let x : Point 2 := fun _ => false
    let R : Subcube 2 := { idx := ({0} : Finset (Fin 2)), val := fun _ _ => false }
    -- The point `x` lies in `R` because the first coordinate agrees.
    have hxR : x ∈ₛ R := by
      intro i hi
      have : i = (0 : Fin 2) := by simpa [R] using hi
      subst this; simp [R, x]
    -- `R` is monochromatic for `f`: all points have first bit `false`.
    have hmono : Subcube.monochromaticFor R f := by
      refine ⟨false, ?_⟩
      intro y hy
      have hy0 : y 0 = false := hy 0 (by simp [R])
      simp [f, hy0]
    -- Apply the new lemma and unpack the result.
    have h :=
      BoolFunc.insensitive_subset_of_monochromatic_subcube
        (f := f) (R := R) (x := x) (hx := hxR) (hmono := hmono)
    rcases h with ⟨A, hAcard, hAflip⟩
    refine ⟨A, ?_⟩
    exact ⟨hAcard, hAflip⟩

/-- Extracting a large insensitive subset requires only a lower bound on the
dimension of a monochromatic subcube. -/
example :
    let f : BFunc 3 := fun _ => false
    let x : Point 3 := fun _ => false
    let R : Subcube 3 := { idx := (∅ : Finset (Fin 3)), val := fun _ _ => false }
    2 ≤ R.dimension ∧
      ∃ A : Finset (Fin 3),
        2 ≤ A.card ∧
        (∀ ⦃T : Finset (Fin 3)⦄, T ⊆ A → f (Point.flip x T) = f x) := by
  intro f x R
  -- The entire cube is monochromatic for the constant function `f`.
  have hxR : x ∈ₛ R := by intro i hi; cases hi
  have hmono : Subcube.monochromaticFor R f := by
    refine ⟨false, ?_⟩; intro y hy; rfl
  have hk : 2 ≤ R.dimension := by
    simp [R, Subcube.dimension]
  obtain ⟨A, hAcard, hAflip⟩ :=
    BoolFunc.exists_large_insensitive_subset_of_monochromatic_subcube
      (f := f) (R := R) (x := x) (hx := hxR) (hmono := hmono)
      (k := 2) (hk := hk)
  refine ⟨hk, A, hAcard, ?_⟩
  intro T hT
  exact hAflip hT

/-- The unconditional variant retrieves a large locally insensitive set inside
`insensitiveCoordsAt`. -/
example :
    let f : BFunc 2 := fun _ => false
    let x : Point 2 := fun _ => false
    ∃ A : Finset (Fin 2),
      2 ≤ A.card ∧
      A ⊆ BoolFunc.insensitiveCoordsAt f x ∧
      (∀ ⦃T : Finset (Fin 2)⦄, T ⊆ A → f (Point.flip x T) = f x) := by
  intro f x
  -- Sensitivity of the constant function is zero.
  have h : BoolFunc.sensitivity f = 0 := by
    simpa [f] using (BoolFunc.sensitivity_const (n := 2) (b := false))
  have hs : BoolFunc.sensitivity f ≤ 0 := by
    simpa [h]
  obtain ⟨A, hAcard, hAsub, hAflip⟩ :=
    BoolFunc.exists_large_insensitive_subset_subset_insensitiveCoordsAt
      (f := f) (s := 0) (hs := hs) (x := x)
  refine ⟨A, ?_, hAsub, ?_⟩
  · simpa using hAcard
  · intro T hT; exact hAflip hT

/-- A four-variable function with sensitivity `2` but no globally insensitive
coordinates. -/
example :
    BoolFunc.sensitivity BoolFunc.sensitivityTwoSupportFull = 2 ∧
      BoolFunc.insensitiveCoords BoolFunc.sensitivityTwoSupportFull
        = (∅ : Finset (Fin 4)) := by
  simpa using
    And.intro BoolFunc.sensitivityTwoSupportFull_sensitivity
      BoolFunc.sensitivityTwoSupportFull_insensitiveCoords

/-- Branching on a large insensitive subcube preserves the correctness of the
fallback decision tree. -/
example :
    ∀ y : Point 1,
      DecisionTree.eval_tree
        (BoolFunc.branchLargeInsensitive (n := 1)
          (f := fun _ : Point 1 => false) (s := 0)
          (hs := by decide) (x := fun _ => false)
          (t := DecisionTree.leaf false)) y
        = (fun _ : Point 1 => false) y := by
  classical
  -- The fallback tree is a single leaf computing the constant function.
  have ht : ∀ y : Point 1,
      DecisionTree.eval_tree (n := 1) (DecisionTree.leaf false) y =
        (fun _ : Point 1 => false) y := by intro y; simp
  -- Constant functions have zero sensitivity.
  have hs : BoolFunc.sensitivity (fun _ : Point 1 => false) ≤ 0 := by decide
  -- Invoke the correctness lemma for `branchLargeInsensitive`.
  simpa using
    (BoolFunc.eval_branchLargeInsensitive (n := 1)
      (f := fun _ : Point 1 => false) (s := 0)
      (hs := hs) (x := fun _ => false)
      (t := DecisionTree.leaf false) (ht := ht))

/-- `insensitiveSubcubeAt` is not necessarily monochromatic.  For the function
`sensitivityTwoSupportFull` the local subcube at the all-zero point already
contains points of different colours. -/
example :
    ¬ Subcube.monochromaticFor
      (BoolFunc.insensitiveSubcubeAt BoolFunc.sensitivityTwoSupportFull
        fun _ => false)
      BoolFunc.sensitivityTwoSupportFull := by
  classical
  -- The base point `x` and the flip on coordinates `1` and `2`.
  let x : Point 4 := fun _ => false
  let y := Point.flip x ({1, 2} : Finset (Fin 4))
  have hx :
      x ∈ₛ BoolFunc.insensitiveSubcubeAt BoolFunc.sensitivityTwoSupportFull x := by
    simp
  have hy :
      y ∈ₛ BoolFunc.insensitiveSubcubeAt BoolFunc.sensitivityTwoSupportFull x := by
    -- All coordinates are locally insensitive at `x`, so the flip stays inside.
    have hsens :
        BoolFunc.sensitivityAt BoolFunc.sensitivityTwoSupportFull x = 0 := by
      decide
    have huniv :
        BoolFunc.insensitiveCoordsAt BoolFunc.sensitivityTwoSupportFull x =
          (Finset.univ : Finset (Fin 4)) := by
      simpa using
        BoolFunc.insensitiveCoordsAt_eq_univ_of_sensitivityAt_zero
          (f := BoolFunc.sensitivityTwoSupportFull) (x := x) (h := hsens)
    have hsubset' :
        ({1, 2} : Finset (Fin 4)) ⊆ (Finset.univ : Finset (Fin 4)) := by
      intro i hi; simp
    have hsubset :
        ({1, 2} : Finset (Fin 4)) ⊆
          BoolFunc.insensitiveCoordsAt BoolFunc.sensitivityTwoSupportFull x := by
      simpa [huniv] using hsubset'
    exact
      BoolFunc.flip_mem_insensitiveSubcubeAt
        (f := BoolFunc.sensitivityTwoSupportFull) (x := x)
        (S := ({1, 2} : Finset (Fin 4))) (hS := hsubset)
  -- The function evaluates differently at `x` and `y`.
  have hxval :
      BoolFunc.sensitivityTwoSupportFull x = false := by decide
  have hyval :
      BoolFunc.sensitivityTwoSupportFull y = true := by decide
  -- A monochromatic subcube would force equal values, contradicting the above.
  intro hmono
  rcases hmono with ⟨b, hb⟩
  have hx_const : b = false := by
    simpa [hxval] using (hb hx).symm
  have hy_const : b = true := by
    simpa [hyval] using (hb hy).symm
  have : (false : Bool) = true := hx_const.symm.trans hy_const
  cases this


end Pnp2Tests
