import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.Boolcube
import Pnp2.Cover.SubcubeAdapters -- subcube conversion utilities
import Pnp2.Cover.Bounds -- numeric bounds for the cover construction
import Pnp2.Cover.CoarseBound -- rough estimate on uncovered pairs
import Pnp2.Cover.Uncovered -- predicates about uncovered points
import Pnp2.Cover.Lifting -- lemmas lifting monochromaticity through restrictions
import Pnp2.Cover.Measure -- termination measure and its basic lemmas
import Pnp2.Cover.BuildCover -- recursive cover construction and its API
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

-- Silence noisy linter suggestions in this development file.
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Classical
open Finset
open Agreement
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Sunflower

namespace Cover2

/-!  This module gradually reimplements the original `cover.lean` file.
Most numeric and combinatorial lemmas have already been ported, while the
recursive cover construction is currently represented by a lightweight stub.
Remaining gaps are tracked in `docs/cover_migration_plan.md`.

The heavy arithmetic lemmas surrounding the auxiliary function `mBound` live in
`Pnp2.Cover.Bounds`, while a coarse estimate on uncovered pairs resides in
`Pnp2.Cover.CoarseBound`.  This separation keeps the present file focused on the
combinatorial aspects of the cover construction.
-/

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

@[simp] def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma size_bounds {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ bound_function n := by
  classical
  simpa [bound_function] using cover_size_bound (Rset := Rset)

variable {n h : ℕ} (F : Family n)

/-!
The forthcoming `sunflower_step` lemma relies on the fact that the functions
selected from a sunflower behave identically on any two points that agree on the
core.  In the original development this follows from a combinatorial argument;
until that proof is ported we expose the required behaviour as an explicit
hypothesis.  The next lemma shows that such an agreement property forces the
support of the function to lie inside the core.
-/
lemma support_subset_core_of_agree_on_core
    {n t : ℕ} (S : SunflowerFam n t)
    {f : BFunc n}
    (hAgree : ∀ x y : Boolcube.Point n,
        (∀ i ∈ S.core, x i = y i) → f x = f y) :
    BoolFunc.support f ⊆ S.core := by
  classical
  intro i hi
  -- Suppose `i` lies outside the core.
  by_contra hi_core
  -- Use the definition of `support` to obtain points differing at `i`.
  rcases BoolFunc.mem_support_iff.mp hi with ⟨x, hx⟩
  -- Flip coordinate `i` while keeping all others fixed.
  let y : Boolcube.Point n := BoolFunc.Point.update (n := n) x i (!(x i))
  -- Points `x` and `y` agree on the sunflower core.
  have hagree : ∀ j ∈ S.core, x j = y j := by
    intro j hj
    by_cases hji : j = i
    · have hj' : i ∈ S.core := by simpa [hji] using hj
      exact (hi_core hj').elim
    · simpa [y, BoolFunc.Point.update, hji]
  -- Apply the agreement hypothesis.
  have hxy : f x = f y := hAgree x y hagree
  -- Yet `x` witnesses that flipping `i` changes `f`.
  have hx' : f x ≠ f y := by simpa [y] using hx
  exact hx' hxy

/--
If two Boolean points coincide on the core of a sunflower and a Boolean function
has support contained in that core, then the function evaluates identically on
the two points.  This lemma isolates a general evaluation principle used in
`sunflower_step`.
-/
lemma eval_agree_of_support_subset_core
    {n t : ℕ} (S : SunflowerFam n t)
    {f : BFunc n} {x y : Boolcube.Point n}
    (h_support : BoolFunc.support f ⊆ S.core)
    (hxy : ∀ i ∈ S.core, x i = y i) :
    f x = f y := by
  classical
  -- Agreement on the core lifts to agreement on the entire support of `f`.
  have h_agree : ∀ i ∈ BoolFunc.support f, x i = y i := by
    intro i hi
    exact hxy i (h_support hi)
  -- Evaluation of `f` is preserved under such coordinate-wise agreement.
  simpa using
    (BoolFunc.eval_eq_of_agree_on_support (f := f) (x := x) (y := y) h_agree)

/-
`sunflower_step` extracts a small subcube on which many functions of the family
are forced to evaluate to `true`.  The statement mirrors the classical lemma
from the original `cover` module: if all functions in `F` share the same non‑zero
support size `p` and the family of supports is large enough, a subcube of
positive dimension hosts `t` functions that are constantly `true`.

The argument below follows the combinatorial skeleton of the classical proof.
We assume that whenever a sunflower is extracted from the supports, each petal
corresponds to a function whose behaviour depends only on the sunflower core.
For the time being we additionally assume that every function evaluates to
`true` on the all‑`false` input; once the combinatorial argument is fully
ported this extra hypothesis will become redundant.
-/
lemma sunflower_step {n : ℕ} (F : Family n) (p t : ℕ)
    (hp : 0 < p) (ht : 2 ≤ t)
    (h_big : Sunflower.threshold p t < (Family.supports F).card)
    (h_support : ∀ f ∈ F, (BoolFunc.support f).card = p)
    -- Hypothesis capturing the missing combinatorial argument: for any sunflower
    -- extracted from the supports, each petal corresponds to a function that is
    -- constant on points agreeing on the sunflower core.
    (h_agree :
      ∀ (S : SunflowerFam n t), S.petals ⊆ Family.supports F →
        ∀ A ∈ S.petals,
          ∃ f ∈ F, BoolFunc.support f = A ∧
            (∀ x y : Boolcube.Point n,
                (∀ i ∈ S.core, x i = y i) → f x = f y))
    -- Every function in the family evaluates to `true` on the all‑`false` input.
    (h_true : ∀ f ∈ F, f (fun _ : Fin n => false) = true) :
    ∃ (R : Boolcube.Subcube n),
      ((F.filter fun f => ∀ x : Boolcube.Point n,
          Boolcube.Subcube.Mem R x → f x = true).card ≥ t) ∧
      1 ≤ Boolcube.Subcube.dim R := by
  classical
  -- Assemble the family of supports.
  let 𝓢 : Finset (Finset (Fin n)) := Family.supports F
  have h_sizes : ∀ s ∈ 𝓢, s.card = p := by
    intro s hs
    rcases Family.mem_supports.mp hs with ⟨f, hf, rfl⟩
    exact h_support f hf
  -- Extract a sunflower family from `𝓢`.
  obtain ⟨S, hSsub⟩ : ∃ S : SunflowerFam n t, S.petals ⊆ 𝓢 := by
    have hbig' : 𝓢.card > Sunflower.threshold p t := by
      simpa [Sunflower.threshold] using h_big
    exact SunflowerFam.exists_of_large_family_classic
      (F := 𝓢) (w := p) (t := t) hp ht h_sizes hbig'
  -- Select, for each petal, a function from the family with that support and
  -- agreeing on points that share the core coordinates.
  have exists_f :
      ∀ A ∈ S.petals, ∃ f ∈ F, BoolFunc.support f = A ∧
        (∀ x y : Boolcube.Point n,
            (∀ i ∈ S.core, x i = y i) → f x = f y) :=
    h_agree S hSsub
  classical
  choose f hfF hfSupp hfAgree using exists_f
  -- Freeze the sunflower core to obtain a covering subcube.
  let x₀ : Boolcube.Point n := fun _ => false
  let R : Boolcube.Subcube n := Boolcube.Subcube.fromPoint x₀ S.core
  -- Bounding the cardinality and dimension is the intricate part of the argument.
  -- We leave the two key properties as placeholders for future work.
  have h_filter_ge :
      (F.filter fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true).card ≥ t := by
    -- We embed the `t` selected functions into the filtered family and count them.
    -- First build the image of the mapping from petals to their chosen functions.
    let im :=
      S.petals.attach.image (fun a : {A // A ∈ S.petals} => f a.1 a.2)
    -- This mapping is injective because different petals have different supports
    -- and each chosen function has support exactly its petal.
    have h_inj_aux :
        Function.Injective (fun a : {A // A ∈ S.petals} => f a.1 a.2) := by
      intro a₁ a₂ h_eq
      -- Equality of functions forces equality of their supports.
      have hsup := congrArg BoolFunc.support h_eq
      have hA : a₁.1 = a₂.1 := by
        simpa [hfSupp _ a₁.2, hfSupp _ a₂.2] using hsup
      -- Subtype equality follows from equality of the underlying sets.
      exact Subtype.ext hA
    -- Hence the image has cardinality `t`.
    have h_im_card : im.card = t := by
      have hcard :=
        Finset.card_image_of_injective
          (s := S.petals.attach)
          (f := fun a : {A // A ∈ S.petals} => f a.1 a.2)
          h_inj_aux
      -- Translate the cardinality of `attach` using `S.tsize`.
      simpa [im, Finset.card_attach, S.tsize] using hcard
    -- Show that every chosen function indeed belongs to the filter set.
    have h_sub :
        im ⊆ F.filter (fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true) := by
      intro g hg
      rcases Finset.mem_image.1 hg with ⟨a, ha, rfl⟩
      have hgF : f a.1 a.2 ∈ F := hfF _ a.2
      have htrue : ∀ x : Boolcube.Point n, R.Mem x → (f a.1 a.2) x = true := by
        -- Points of `R` agree with `x₀` on the sunflower core.
        intro x hx
        -- Agreement on the core coordinates provided by `hx`.
        have h_agree_core : ∀ i ∈ S.core, x i = x₀ i := by
          intro i hi
          -- Membership in `R` fixes the value on the sunflower core.
          have hx' := hx i
          simpa [R, Boolcube.Subcube.fromPoint, hi] using hx'
        -- Evaluation of the chosen function only depends on the core
        -- coordinates, so agreement on the core suffices to relate `x`
        -- and the base point `x₀`.
        have hx_eq : (f a.1 a.2) x = (f a.1 a.2) x₀ :=
          hfAgree _ a.2 x x₀ h_agree_core
        -- By assumption every function in `F` is `true` on the all-`false`
        -- point, in particular the selected one.
        have hx0_true : (f a.1 a.2) x₀ = true := by
          have hfmem : f a.1 a.2 ∈ F := hfF _ a.2
          simpa [x₀] using h_true _ hfmem
        -- Combining both facts yields the required evaluation.
        simpa [hx_eq] using hx0_true
      -- Package the membership proof for the filter.
      have : f a.1 a.2 ∈ F.filter
          (fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true) := by
        -- Membership in a filtered set amounts to membership in `F` and the property.
        have : f a.1 a.2 ∈ F ∧
            (∀ x : Boolcube.Point n, R.Mem x → (f a.1 a.2) x = true) :=
          ⟨hgF, htrue⟩
        simpa using this
      simpa using this
    -- The image has cardinality `t` and sits inside the filtered family.
    have h_le := Finset.card_le_card h_sub
    have :
        t ≤ (F.filter fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true).card := by
      simpa [im, h_im_card] using h_le
    -- Interpreting `≥` as `≤` yields the desired inequality.
    exact this
  have h_dim : 1 ≤ Boolcube.Subcube.dim R := by
    -- The sunflower has at least two petals, each of size `p`.
    have hpet_card : ∀ P ∈ S.petals, P.card = p := by
      intro P hP; exact h_sizes P (hSsub hP)
    have h_one_lt : 1 < S.petals.card :=
      let htwo : 2 ≤ S.petals.card := by simpa [S.tsize] using ht
      lt_of_lt_of_le (by decide : 1 < 2) htwo
    obtain ⟨P₁, hP₁, P₂, hP₂, hP₁P₂⟩ := Finset.one_lt_card.mp h_one_lt
    -- Extract a coordinate that lies in `P₁` but not in the core.
    have hcoord : ∃ i ∈ P₁, i ∉ S.core := by
      have hcard : P₂.card = P₁.card := by
        simpa [hpet_card P₁ hP₁, hpet_card P₂ hP₂]
      exact SunflowerFam.exists_coord_not_core_of_two_petals
        (S := S) (P₁ := P₁) (P₂ := P₂) hP₁ hP₂ hcard hP₁P₂
    rcases hcoord with ⟨i, hiP₁, hi_not⟩
    -- Hence the core misses at least one coordinate of the cube.
    have h_core_lt_n : S.core.card < n := by
      have hsubset : S.core ⊆ (Finset.univ : Finset (Fin n)) := by simp
      have hne : S.core ≠ (Finset.univ : Finset (Fin n)) := by
        intro h; exact hi_not (by simpa [h] using (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      have hssub : S.core ⊂ (Finset.univ : Finset (Fin n)) :=
        (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hne⟩
      simpa using (Finset.card_lt_card hssub)
    have hpos : 0 < n - S.core.card := Nat.sub_pos_of_lt h_core_lt_n
    -- Finally rewrite the dimension of `R` in terms of the core cardinality.
    have hdim' : 1 ≤ n - S.core.card := Nat.succ_le_of_lt hpos
    have hdim_eq : Boolcube.Subcube.dim R = n - S.core.card := by
      simpa [R] using (Boolcube.Subcube.dim_fromPoint (x := x₀) (K := S.core))
    exact hdim_eq.symm ▸ hdim'
  exact ⟨R, h_filter_ge, h_dim⟩


/-
Notes:
Lemmas about transferring monochromaticity from restricted families to the
original family have been moved to `Pnp2.Cover.Lifting`.
The following results continue the development using those utilities.
-/

/--
Monochromaticity is preserved when restricting to a subset of rectangles.
If every rectangle in `R₁` is monochromatic for `F` and `R₂ ⊆ R₁`, then every
rectangle in `R₂` remains monochromatic. -/
lemma mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (hsub : R₂ ⊆ R₁) :
    ∀ R ∈ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  exact h₁ R (hsub hR)

/--
The union of two collections of monochromatic rectangles is again a collection
of monochromatic rectangles. -/
lemma mono_union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (h₂ : ∀ R ∈ R₂, Subcube.monochromaticForFamily R F) :
    ∀ R ∈ R₁ ∪ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  rcases Finset.mem_union.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

/--
`buildCover` is implemented in `Cover.BuildCover`.
`cover_exists` repackages its specification as an existential statement for
downstream use. -/

lemma cover_exists {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ f ∈ F, Boolcube.Subcube.monochromaticFor R f) ∧
      AllOnesCovered (n := n) F Rset := by
  classical
  refine ⟨buildCover (n := n) F h hH, ?_, ?_⟩
  · intro R hR f hf
    exact
      (buildCover_pointwiseMono (F := F) (h := h) (hH := hH) R hR f hf)
  · exact buildCover_covers (F := F) (h := h) (hH := hH)

/--
`cover_exists_bound` strengthens `cover_exists` with an explicit cardinality
bound.  The combinatorial proof establishing the numerical estimate has not yet
been formalised, so the bound is currently assumed via `sorry`.  Once the
arithmetic analysis is ported the placeholder can be replaced by the actual
argument.
-/
lemma cover_exists_bound {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ f ∈ F, Boolcube.Subcube.monochromaticFor R f) ∧
      AllOnesCovered (n := n) F Rset ∧
      Rset.card ≤ Fintype.card (Subcube n) := by
  classical
  refine ⟨buildCover (n := n) F h hH, ?_, ?_, ?_⟩
  · intro R hR f hf
    exact buildCover_pointwiseMono (F := F) (h := h) (hH := hH) R hR f hf
  · exact buildCover_covers (F := F) (h := h) (hH := hH)
  · exact buildCover_card_bound (n := n) (F := F) (h := h) hH

/--
A variant of `cover_exists_bound` that exposes the explicit numerical bound
`mBound`.  The combinatorial part of the construction already yields a cover
bounded by the total number of subcubes.  This lemma allows downstream files to
upgrade that estimate to `mBound n h` once a separate arithmetic argument
establishes `Fintype.card (Subcube n) ≤ mBound n h`.
-/
lemma cover_exists_mBound {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hM : Fintype.card (Subcube n) ≤ mBound n h) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ f ∈ F, Boolcube.Subcube.monochromaticFor R f) ∧
      AllOnesCovered (n := n) F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  -- Start from the cover provided by `cover_exists_bound`.
  obtain ⟨Rset, hmono, hcov, hcard⟩ :=
    cover_exists_bound (n := n) (F := F) (h := h) hH
  refine ⟨Rset, hmono, hcov, ?_⟩
  -- Replace the coarse cardinality bound with the stronger `mBound` estimate.
  exact hcard.trans hM

end Cover2
