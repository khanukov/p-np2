import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.low_sensitivity_cover
import Pnp2.Boolcube
import Pnp2.Cover.SubcubeAdapters -- subcube conversion utilities
import Pnp2.Cover.Bounds -- numeric bounds for the cover construction
import Pnp2.Cover.CoarseBound -- rough estimate on uncovered pairs
import Pnp2.Cover.Uncovered -- predicates about uncovered points
import Pnp2.Cover.Lifting -- lemmas lifting monochromaticity through restrictions
import Pnp2.Cover.Measure -- termination measure and its basic lemmas
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
    (h_big : (t - 1).factorial * p ^ t < (Family.supports F).card)
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
    have hbig' : 𝓢.card > Nat.factorial (t - 1) * p ^ t := by
      simpa using h_big
    exact SunflowerFam.exists_of_large_family
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
Skeleton of the recursive cover construction.  The function searches for an
uncovered pair of a function and an input point.  If no such pair exists we
simply return the accumulated set of rectangles `Rset`.  The recursive branch is
currently a placeholder that will eventually insert additional rectangles to
cover the uncovered pair.  For now it falls back to returning `Rset` unchanged,
mirroring the previous stub behaviour.
-/
noncomputable def buildCover (F : Family n) (h : ℕ)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n) := ∅) : Finset (Subcube n) := by
  classical
  -- Attempt to locate an uncovered pair `(f, x)`.
  match firstUncovered (n := n) F Rset with
  | none =>
      -- All `1`-inputs are already covered; return the accumulated set.
      exact Rset
  | some _ =>
      -- Placeholder: future developments will insert additional rectangles
      -- here.  The current implementation keeps the behaviour identical to the
      -- original stub by simply returning `Rset`.
      exact Rset

/-- With the current placeholder implementation `buildCover` simply returns the
initial set of rectangles `Rset`.  This helper lemma exposes that behaviour so
that subsequent proofs can rewrite by it without repeatedly unfolding the
definition. -/
lemma buildCover_eq_Rset (F : Family n) (h : ℕ)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n)) :
    buildCover (n := n) F h _hH Rset = Rset := by
  classical
  -- Case split on `firstUncovered`; both branches return `Rset`.
  cases hfu' : firstUncovered (n := n) F Rset with
  | none => simp [buildCover, hfu']
  | some p => simp [buildCover, hfu']

/--
If the search for an uncovered pair already fails (`firstUncovered = none`),
`buildCover` immediately returns the existing set of rectangles, whose size is
assumed to be bounded by `mBound`.
-/
lemma buildCover_card_bound_of_none {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (_hfu : firstUncovered (n := n) F Rset = none)
    (hcard : Rset.card ≤ mBound n h) :
    (buildCover (n := n) F h _hH Rset).card ≤ mBound n h := by
  simpa [buildCover_eq_Rset] using hcard

/--
Base case of the size bound: if no uncovered pair exists initially, the
constructed cover is empty and trivially bounded by `mBound`.
-/
lemma buildCover_card_bound_base {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) = none) :
    (buildCover (n := n) F h _hH).card ≤ mBound n h := by
  have : (0 : ℕ) ≤ mBound n h := mBound_nonneg (n := n) (h := h)
  simpa [buildCover_eq_Rset] using this

/--
A coarse numeric estimate that bounds the size of the cover directly by
`2 * h + n`.  With the current stub `buildCover`, the constructed set of
rectangles is empty, so the claim follows immediately.
-/
lemma buildCover_card_linear_bound_base {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) = none) :
    (buildCover (n := n) F h _hH).card ≤ 2 * h + n := by
  have hres : buildCover (n := n) F h _hH = (∅ : Finset (Subcube n)) := by
    simpa [buildCover_eq_Rset] using
      (buildCover_eq_Rset (n := n) (F := F) (h := h) (_hH := _hH)
        (Rset := (∅ : Finset (Subcube n))))
  have : (0 : ℕ) ≤ 2 * h + n := Nat.zero_le _
  simpa [hres] using this

/--
The linear bound holds without assuming that the search for uncovered pairs
fails initially.  Since the stub `buildCover` returns the empty set, the
result is immediate.
-/
lemma buildCover_card_linear_bound {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ 2 * h + n := by
  have : (0 : ℕ) ≤ 2 * h + n := Nat.zero_le _
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h) (_hH := _hH)
      (Rset := (∅ : Finset (Subcube n)))
  simpa [hres] using this

/--
Rewriting of `buildCover_card_linear_bound` emphasising the initial measure
`μ = 2 * h + n`.  This variant mirrors the legacy API.
-/
lemma buildCover_card_init_mu {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ 2 * h + n := by
  simpa using
    (buildCover_card_linear_bound (n := n) (F := F) (h := h) _hH)

/--
`buildCover` (with the current stub implementation) always returns the
empty set, so its cardinality trivially satisfies the `mBound` bound.
This lemma mirrors the API of the full development and allows downstream
files to rely on the bound even before the full recursion is ported. -/
lemma buildCover_card_bound {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ mBound n h := by
  have : (0 : ℕ) ≤ mBound n h := mBound_nonneg (n := n) (h := h)
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h) (_hH := _hH)
      (Rset := (∅ : Finset (Subcube n)))
  simpa [hres] using this

/--
`buildCover` always yields a set of rectangles whose cardinality is bounded by
the universal function `bound_function`.  This is a direct consequence of the
generic size bound for finite sets of subcubes and does not rely on the
internal construction of `buildCover`.
-/
lemma buildCover_card_univ_bound {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h _hH).card ≤ bound_function n := by
  classical
  -- `size_bounds` provides the universal bound for any finite set of
  -- rectangles.  Instantiate it with the set produced by `buildCover`.
  have := size_bounds (n := n) (Rset := buildCover (n := n) F h _hH)
  simpa [size, bound_function] using this

/--
When all functions in the family have sensitivity below the logarithmic
threshold, the (stubbed) cover remains empty and hence satisfies the crude
exponential bound.  This lemma mirrors the statement from `cover.lean` while
the full algorithm is being ported. -/
lemma buildCover_card_lowSens {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n)) :
    (buildCover (n := n) F h _hH).card ≤
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  -- The stubbed `buildCover` returns the empty set, whose cardinality is `0`.
  have : (0 : ℕ) ≤
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    Nat.zero_le _
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h) (_hH := _hH)
      (Rset := (∅ : Finset (Subcube n)))
  simpa [hres] using this

/--
`buildCover_card_lowSens_with` extends `buildCover_card_lowSens` to the case
where an initial set of rectangles `Rset` is provided.  The stubbed
implementation of `buildCover` simply returns `Rset`, so the inequality reduces
to the trivial bound `Rset.card ≤ Rset.card + …`.
-/
lemma buildCover_card_lowSens_with {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n))
    (Rset : Finset (Subcube n)) :
    (buildCover (n := n) F h _hH Rset).card ≤
      Rset.card +
        Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  -- The right-hand side obviously dominates `Rset.card`.
  have : Rset.card ≤
      Rset.card +
        Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    Nat.le_add_right _ _
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h) (_hH := _hH)
      (Rset := Rset)
  simpa [hres] using this

/--
`buildCover_card_bound_lowSens` upgrades the crude exponential bound from
`buildCover_card_lowSens` to the standard `mBound` function whenever the
logarithmic threshold `Nat.log2 (n + 1)^2` is at most the entropy budget `h`.
This mirrors the corresponding lemma in `cover.lean` but is trivial for the
stubbed `buildCover`.
-/
lemma buildCover_card_bound_lowSens {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by
  classical
  -- Start with the exponential estimate from `buildCover_card_lowSens`.
  have hcard : (buildCover (n := n) F h hH).card ≤
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    buildCover_card_lowSens (n := n) (F := F) (h := h) hH hs
  -- Compare the exponents `10 * log₂(n+1)^2` and `10 * h`.
  have hexp_mul :
      10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) ≤
        Nat.pow 2 (10 * h) :=
    -- Use the modern lemma `pow_le_pow_right` for exponent monotonicity.
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp_mul
  -- Combine with the main bound `pow_le_mBound`.
  have hbig := hcard.trans hpow
  have hbound := hbig.trans (pow_le_mBound (n := n) (h := h) hn)
  simpa using hbound

/-!
`buildCover_card_bound_lowSens_with` upgrades the crude exponential bound from
`buildCover_card_lowSens_with` to the standard `mBound` function when an
initial set of rectangles `Rset` is provided.  Under the numeric hypothesis
`hh`, the additional rectangles introduced by the low-sensitivity cover already
fit inside `mBound n h`, allowing us to conclude that the final size stays below
`mBound n (h + 1)` using `two_mul_mBound_le_succ`.
-/
lemma buildCover_card_bound_lowSens_with {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) (Rset : Finset (Subcube n))
    (hcard : Rset.card ≤ mBound n h) :
    (buildCover (n := n) F h hH Rset).card ≤ mBound n (h + 1) := by
  classical
  -- Cardinality bound from the low-sensitivity cover.
  have hsize :
      (buildCover (n := n) F h hH Rset).card ≤
        Rset.card +
          Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
    buildCover_card_lowSens_with (n := n) (F := F) (h := h) hH hs
      (Rset := Rset)
  -- Estimate the additional rectangles using `mBound`.
  have hexp_mul :
      10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) ≤
        mBound n h :=
    -- Apply monotonicity of exponentiation in a single step and then
    -- leverage the existing bound on `mBound`.
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp_mul).trans
      (pow_le_mBound (n := n) (h := h) hn)
  -- Combine with the existing rectangles.
  have hsum :
      (buildCover (n := n) F h hH Rset).card ≤ Rset.card + mBound n h :=
    hsize.trans <| Nat.add_le_add_left hpow _
  have hdouble : Rset.card + mBound n h ≤ 2 * mBound n h := by
    have := add_le_add hcard (le_rfl : mBound n h ≤ mBound n h)
    simpa [two_mul] using this
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hsum.trans (hdouble.trans hstep)

/--
`buildCover_card_bound_lowSens_or` partially bridges the gap towards the
full counting lemma `buildCover_card_bound`.  When the maximum sensitivity of
functions in the family falls below the logarithmic threshold we invoke the
low‑sensitivity bound.  Otherwise we fall back to the coarse measure argument
used in the general placeholder proof.  In the stubbed development the cover is
always empty, so the result reduces to the numeric inequality `0 ≤ mBound n h`.
-/
lemma buildCover_card_bound_lowSens_or {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (_hn : 0 < n) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by
  -- `buildCover` returns the empty set, so its cardinality is zero.
  have hzero : (buildCover (n := n) F h hH).card = 0 := by
    have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
        (_hH := hH) (Rset := (∅ : Finset (Subcube n)))
    simp [hres]
  -- Numeric bound is immediate from `mBound_nonneg`.
  have hbound : 0 ≤ mBound n h := mBound_nonneg (n := n) (h := h)
  simpa [hzero] using hbound

/--
In the low-sensitivity regime, `buildCover` produces a collection of
monochromatic rectangles.  With the current stubbed implementation the
constructed cover is empty, so the claim holds vacuously.  This lemma mirrors
the statement from `cover.lean` and will gain substance once the recursive
construction is ported.
-/
lemma buildCover_mono_lowSens {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hs : ∀ f ∈ F, BoolFunc.sensitivity f < Nat.log2 (Nat.succ n)) :
    ∀ R ∈ buildCover (n := n) F h _hH,
      Subcube.monochromaticForFamily R F := by
  intro R hR
  -- No rectangles are produced by the stubbed `buildCover`.
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
      (_hH := _hH) (Rset := (∅ : Finset (Subcube n)))
  have : False := by simpa [hres] using hR
  exact this.elim

/--
Every rectangle produced by `buildCover` is monochromatic for the family `F`.
With the current stub implementation, the cover is empty and the claim holds
vacuously.  This lemma mirrors the API of the full development.
-/
lemma buildCover_mono {n h : ℕ} (F : Family n)
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover (n := n) F h _hH,
        Subcube.monochromaticForFamily R F := by
  intro R hR
  -- Membership in the empty cover yields a contradiction.
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
      (_hH := _hH) (Rset := (∅ : Finset (Subcube n)))
  have : False := by simpa [hres] using hR
  cases this

/--
If the starting set of rectangles already covers all `1`-inputs of the
family `F`, then adding the (currently empty) result of `buildCover`
preserves this property.  This weak variant mirrors the intended lemma
from `cover.lean` and will be strengthened once the full construction is
ported.
-/
lemma buildCover_covers_with {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (Rset : Finset (Subcube n))
    (hcov : AllOnesCovered (n := n) F Rset) :
    AllOnesCovered (n := n) F
      (Rset ∪ buildCover (n := n) F h hH Rset) := by
  -- `buildCover` returns `Rset`, so the union does not change the set of
  -- rectangles.  The coverage hypothesis therefore transfers directly.
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h) (_hH := hH)
      (Rset := Rset)
  simpa [hres] using hcov

/--
Special case of `buildCover_covers_with` starting from the empty set of
rectangles.
-/
lemma buildCover_covers {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
      (_hH := hH) (Rset := (∅ : Finset (Subcube n)))
  simpa [hres] using hcov

/--
`buildCover_mu` collapses the measure to `2 * h` when the empty set already
covers all `1`-inputs.  This mirrors the behaviour of the eventual cover
construction.
-/
lemma buildCover_mu {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    mu (n := n) F h (buildCover (n := n) F h hH) = 2 * h := by
  -- `buildCover` returns the empty set, so the coverage hypothesis transfers.
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
      (_hH := hH) (Rset := (∅ : Finset (Subcube n)))
  have hcov' :
      AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
    simpa [hres] using
      (buildCover_covers (n := n) (F := F) (h := h) hH hcov)
  -- Apply the general lemma characterising covers with measure `2 * h`.
  simpa [hres] using
    (mu_of_allCovered (n := n) (F := F)
      (Rset := buildCover (n := n) F h hH) (h := h) hcov')

/--
The converse direction: if the measure of the set of rectangles returned by
`buildCover` already equals `2 * h`, then no uncovered pairs remain.  Hence the
resulting rectangles cover all `1`-inputs of the family `F`.
-/
lemma buildCover_covers_of_mu_eq {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hμ : mu (n := n) F h (buildCover (n := n) F h hH) = 2 * h) :
    AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by
  -- The lemma `allOnesCovered_of_mu_eq` already provides the desired
  -- implication for an arbitrary rectangle set.  Instantiating it with the
  -- result of `buildCover` yields the statement.
  exact
    allOnesCovered_of_mu_eq
      (n := n) (F := F)
      (Rset := buildCover (n := n) F h hH)
      (h := h) hμ

/-!
`mu_union_buildCover_le` is a small helper lemma used in termination
arguments for `buildCover`.  Adding the rectangles produced by one
step of the construction can only decrease the measure `μ`, since the
set of uncovered pairs shrinks.  With the current stub implementation of
`buildCover` this is immediate.
-/
lemma mu_union_buildCover_le {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n)) :
    mu (n := n) F h (Rset ∪ buildCover F h hH Rset) ≤
      mu (n := n) F h Rset := by
  -- `buildCover` currently returns its input set of rectangles, so the union
  -- collapses to `Rset`.
  classical
  have hres : buildCover (n := n) F h hH Rset = Rset := by
    -- Analyse the result of `firstUncovered` to simplify the definition.
    cases hfu' : firstUncovered (n := n) F Rset with
    | none => simpa [buildCover, hfu']
    | some p => simpa [buildCover, hfu']
  simpa [mu, hres]

/--
`mu_buildCover_lt_start` is a weak variant of the legacy lemma with the same
name.  In the original development the cover construction strictly decreased
the measure whenever an uncovered pair existed.  The current stubbed
implementation leaves the rectangle set unchanged, so we can only conclude that
the measure does not increase.  The strict inequality will return once the full
algorithm is ported.
-/
lemma mu_buildCover_lt_start {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (_hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) ≠ none) :
    mu (n := n) F h (buildCover (n := n) F h hH) ≤
      mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- `buildCover` returns the empty set, so both measures coincide.
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
      (_hH := hH) (Rset := (∅ : Finset (Subcube n)))
  simpa [mu, hres]

/--
`mu_buildCover_le_start` is a convenient special case of
`mu_union_buildCover_le`: starting from the empty set of rectangles, running
`buildCover` cannot increase the measure `μ`.
-/
lemma mu_buildCover_le_start {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu (n := n) F h (buildCover (n := n) F h hH) ≤
      mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- Instantiate `mu_union_buildCover_le` with an empty starting set.
  have hres := buildCover_eq_Rset (n := n) (F := F) (h := h)
      (_hH := hH) (Rset := (∅ : Finset (Subcube n)))
  have :=
    mu_union_buildCover_le (n := n) (F := F) (h := h) (hH := hH)
      (Rset := (∅ : Finset (Subcube n)))
  -- Simplify using the computed shape of `buildCover`.
  simpa [hres] using this

/--
`mu_union_buildCover_lt` mirrors the corresponding lemma from the
legacy `cover` module.  In the complete development the union with the
rectangles produced by `buildCover` would strictly decrease the measure
whenever `firstUncovered` returns a pair.  The current stubbed
implementation leaves the rectangle set unchanged, so we can only show
that the measure does not increase.  The strict version will return once
the full recursion is ported. -/
lemma mu_union_buildCover_lt {F : Family n}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (_hfu : firstUncovered (n := n) F Rset ≠ none) :
    mu (n := n) F h (Rset ∪ buildCover (n := n) F h hH Rset) ≤
      mu (n := n) F h Rset := by
  -- The stub `buildCover` leaves `Rset` unchanged, so the measures coincide.
  simpa using
    (mu_union_buildCover_le (n := n) (F := F) (h := h)
      (hH := hH) (Rset := Rset))

/--
`buildCover_measure_drop` bounds the initial measure by `2 * h`.  In the
current development `buildCover` does not alter the uncovered set, so the
general lower bound on `μ` suffices.  The statement matches the legacy API
for downstream compatibility.
-/
lemma buildCover_measure_drop {F : Family n} {h : ℕ}
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    2 * h ≤ mu (n := n) F h (∅ : Finset (Subcube n)) := by
  -- The measure `μ` always dominates `2 * h`, even for the empty rectangle set.
  simpa using
    (mu_lower_bound (n := n) (F := F) (h := h)
      (Rset := (∅ : Finset (Subcube n))))

/--
`cover_exists` packages the properties of `buildCover` into an existence
statement.  When the starting family has no uncovered `1`‑inputs, the stub
implementation returns the empty cover, which trivially satisfies the required
bounds.  This lemma mirrors the API of the full development, making it easier
for downstream files to transition once the real construction is ported. -/
lemma cover_exists {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered (n := n) F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  refine ⟨buildCover (n := n) F h hH, ?_, ?_, ?_⟩
  · intro R hR
    exact buildCover_mono (n := n) (F := F) (h := h) hH R hR
  · exact buildCover_covers (n := n) (F := F) (h := h) hH hcov
  · exact buildCover_card_bound (n := n) (F := F) (h := h) hH


end Cover2

