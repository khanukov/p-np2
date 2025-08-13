import Pnp2.BoolFunc.Sensitivity
import Pnp2.BoolFunc
import Pnp2.DecisionTree
import Pnp2.entropy

open BoolFunc

namespace BoolFunc

variable {n : ℕ}

/-- Universal constant used in all depth and cover bounds.  The exact value is
chosen for convenience and does not attempt to be optimal. -/
def coverConst : Nat := 10

-- This axiom summarises the decision-tree construction for families of
-- low-sensitivity Boolean functions.  The underlying combinatorial result
-- (due to Gopalan--Moshkovitz--Oliveira) shows that a single decision tree of
-- depth `O(s * log n)` suffices to compute every function in the family.
-- Each leaf of that tree corresponds to a rectangular subcube on which all
-- functions agree.  The number of such subcubes is therefore bounded by an
-- exponential in `s * log₂ (n + 1)`.  We assume this theorem as an axiom in
-- the current development.
axiom decisionTree_cover
  {n : Nat} (F : Family n) (s : Nat) [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n))

/-!
The lemma states that a family of low-sensitivity Boolean functions admits a
compact cover by monochromatic subcubes.  A constructive proof would proceed by
recursively building a decision tree:

* At each node pick a coordinate on which some function in the family is
  sensitive and branch on its value.
* Restrict every function to the chosen half of the cube and continue
  recursively until the family becomes constant on the remaining subcube.
* Each leaf of the resulting tree corresponds to a rectangular subcube on which
  all functions agree.

Establishing the required depth bound `O(s * log n)` involves a careful analysis
of how sensitivity behaves under restrictions.  This development has not yet
been formalised, so `decisionTree_cover` remains an axiom providing the intended
statement. -/

/-- Trivial base case: if all functions in the family are constant on the full
cube, we can cover all ones with just that cube.  This lemma acts as a base case
for the eventual recursive construction of `decisionTree_cover`. -/
lemma decisionTree_cover_of_constant
  {n : Nat} (F : Family n) (s : Nat) [Fintype (Point n)]
  (hconst : ∃ b, ∀ f ∈ F, ∀ x, f x = b) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  rcases hconst with ⟨b, hb⟩
  -- The full cube represented as a subcube.
  let R : Subcube n :=
    { idx := ∅,
      val := by
        intro i hi
        exact False.elim <| Finset.notMem_empty _ hi }
  have hmem : ∀ x : Point n, x ∈ₛ R := by
    intro x i hi; cases hi
  have hmono : Subcube.monochromaticForFamily R F := by
    refine ⟨b, ?_⟩
    intro f hf x hx
    simpa using hb f hf x
  refine ⟨{R}, ?_, ?_, ?_⟩
  · intro R' hR'
    have hR : R' = R := by simpa using Finset.mem_singleton.mp hR'
    simpa [hR] using hmono
  · intro f hf x hx
    refine ⟨R, by simp, ?_⟩
    simpa using hmem x
  · have hcard : ({R} : Finset (Subcube n)).card = 1 := by simp
    have hpos : 0 < Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) :=
      pow_pos (by decide) _
    have : 1 ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) :=
      Nat.succ_le_of_lt hpos
    simpa [hcard] using this

/--
  Degenerate base case: the empty family has no `1`-inputs to cover.
  Returning the empty set of rectangles trivially satisfies the
  monochromaticity and coverage requirements.
-/
lemma decisionTree_cover_empty
  {n s : Nat} [Fintype (Point n)] :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R (∅ : Family n)) ∧
    (∀ f ∈ (∅ : Family n), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  refine ⟨∅, ?_, ?_, ?_⟩
  · intro R hR; cases hR
  · intro f hf; cases hf
  · have : 0 ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) :=
      Nat.zero_le _
    exact this

/-!
Integrate the explicit decision tree with the cover construction.
If a tree has monochromatic leaves for `F` and covers every `1`-input,
its leaf subcubes form a valid cover whose size is bounded by `2 ^ depth`.
-/
lemma decisionTree_cover_of_tree
  {n s : Nat} (F : Family n) (t : DecisionTree n) [Fintype (Point n)]
  (hmono : ∀ R ∈ DecisionTree.leaves_as_subcubes t,
      Subcube.monochromaticForFamily R F)
  (hcov : ∀ f ∈ F, ∀ x, f x = true →
      ∃ R ∈ DecisionTree.leaves_as_subcubes t, x ∈ₛ R)
  (hdepth : DecisionTree.depth t ≤ coverConst * s * Nat.log2 (Nat.succ n)) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Choose the set of leaf subcubes as the cover.
  let Rset := DecisionTree.leaves_as_subcubes t
  have hcard_le : Rset.card ≤ 2 ^ DecisionTree.depth t :=
    DecisionTree.tree_depth_bound (t := t)
  have hcard : Rset.card ≤ 2 ^ (coverConst * s * Nat.log2 (Nat.succ n)) := by
    exact le_trans hcard_le
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hdepth)
  refine ⟨Rset, ?_, ?_, hcard⟩
  · intro R hR; exact hmono R hR
  · intro f hf x hx; exact hcov f hf x hx

lemma monochromaticFor_of_family_singleton {R : Subcube n} {f : BFunc n} :
    Subcube.monochromaticForFamily R ({f} : Family n) →
    Subcube.monochromaticFor R f := by
  intro h
  rcases h with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  have := hb f (by simp) hx
  simpa using this

/--
Refined orientation of `non_constant_family_has_sensitive_coord`.
It produces a sensitive coordinate together with an input where the
value changes from `true` to `false`.  This direction is convenient for
the recursive cover construction, which always follows a `true` branch. -/
lemma exists_sensitive_coord_true_false (F : Family n) [Fintype (Point n)]
    (hconst : ¬ ∃ b, ∀ f ∈ F, ∀ x, f x = b)
    (htrue : ∀ f ∈ F, ∃ x, f x = true) :
    ∃ i : Fin n, ∃ f ∈ F, ∃ x : Point n,
      f x = true ∧ f (Point.update x i (!x i)) = false := by
  classical
  -- Obtain a sensitive coordinate and a witness where the value flips.
  obtain ⟨i, f, hfF, x, hxneq⟩ :=
    non_constant_family_has_sensitive_coord (F := F) (n := n) hconst htrue
  -- Case analysis on the value of `f` at `x`.
  by_cases hfx : f x = true
  · refine ⟨i, f, hfF, x, hfx, ?_⟩
    -- The flipped point must evaluate to `false`.
    have : f (Point.update x i (!x i)) ≠ true := by
      simpa [hfx] using hxneq
    cases hflip : f (Point.update x i (!x i)) with
    | false => simpa [hflip]
    | true => simpa [hflip] using this
  · -- Otherwise `f x = false`; flip the bit to get a `true` value.
    have hfxfalse : f x = false := by
      cases hval : f x with
      | false => simpa [hval]
      | true => cases hfx hval
    -- Consider the flipped input.
    refine ⟨i, f, hfF, Point.update x i (!x i), ?_, ?_⟩
    · -- Show that the flipped input yields `true`.
      have : f (Point.update x i (!x i)) ≠ false := by
        simpa [hfxfalse] using hxneq.symm
      cases hflip : f (Point.update x i (!x i)) with
      | true => simpa [hflip]
      | false => simpa [hflip] using this
    · -- Flipping again returns to `x`, where the value is `false`.
      have hxupd :
          Point.update (Point.update x i (!x i)) i (! (Point.update x i (!x i)) i) = x := by
        -- simplify the double update
        funext j; by_cases hji : j = i
        · subst hji; simp [Point.update]
        · simp [Point.update, hji]
      have := congrArg f hxupd
      simpa [hfxfalse] using this

/--
The images of two rectangle sets under extension with opposite fixed values of
`i` are disjoint.  Intuitively, any point lying in an extension with `i = false`
must satisfy `x i = false`, whereas membership in an extension with
`i = true` forces `x i = true`.  The hypotheses `hi₀`/`hi₁` guarantee that `i`
was not already fixed in the original rectangles, so the extensions genuinely
record the new value of `i`.
-/
lemma disjoint_extend_images (i : Fin n) {R0 R1 : Finset (Subcube n)}
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    Disjoint (R0.image (fun R => Subcube.extend R i false))
             (R1.image (fun R => Subcube.extend R i true)) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro R hR0 hR1
  -- Decode membership of `R` in the two images.
  obtain ⟨S0, hS0, hR0'⟩ := Finset.mem_image.mp hR0
  obtain ⟨S1, hS1, hR1'⟩ := Finset.mem_image.mp hR1
  -- Consequently the same subcube arises by extending with both `false` and `true`.
  have hEq : Subcube.extend S0 i false = Subcube.extend S1 i true :=
    by simpa [hR0', hR1'] using Eq.trans hR0' (hR1'.symm)
  -- Build a point in `S0` forcing `x i = false`.
  classical
  let x : Point n := fun j => if h : j ∈ S0.idx then S0.val j h else false
  have hx0 : x ∈ₛ S0 := by
    intro j hj; dsimp [x]; simp [hj]
  have hxi : x i = false := by
    dsimp [x];
    have : i ∉ S0.idx := hi0 _ hS0
    simp [this]
  -- The point `x` lies in the extended subcube on the `false` branch.
  have hxR0 : x ∈ₛ Subcube.extend S0 i false :=
    (Subcube.mem_extend_iff (R := S0) (i := i) (b := false)
        (x := x) (hi0 _ hS0)).2 ⟨hxi, hx0⟩
  -- Due to `hEq`, it also lies in the extension on the `true` branch.
  have hxR1 : x ∈ₛ Subcube.extend S1 i true := by
    simpa [hEq] using hxR0
  have hx1 : x i = true :=
    (Subcube.mem_extend_iff (R := S1) (i := i) (b := true)
        (x := x) (hi1 _ hS1)).1 hxR1 |>.1
  -- Finally derive the contradiction `false = true`.
  have : False := by simpa [hxi] using hx1
  exact this

/-!
`disjoint_extend_images` immediately yields a convenient cardinality
statement: when extending two rectangle collections along opposite values of
the same coordinate, the resulting images are disjoint.  Consequently the size
of their union is just the sum of the original sizes.  This fact will be used
when estimating the number of rectangles produced by the recursive cover
construction.
-/
lemma card_extend_union_le (i : Fin n) {R0 R1 : Finset (Subcube n)}
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    (R0.image (fun R => Subcube.extend R i false) ∪
       R1.image (fun R => Subcube.extend R i true)).card ≤
      R0.card + R1.card := by
  classical
  have hdis :=
    disjoint_extend_images (i := i) (R0 := R0) (R1 := R1) hi0 hi1
  have hcard :=
    (Finset.card_union_of_disjoint hdis :
        (R0.image (fun R => Subcube.extend R i false) ∪
            R1.image (fun R => Subcube.extend R i true)).card =
          (R0.image (fun R => Subcube.extend R i false)).card +
            (R1.image (fun R => Subcube.extend R i true)).card)
  have h0 := Finset.card_image_le (s := R0) (f := fun R => Subcube.extend R i false)
  have h1 := Finset.card_image_le (s := R1) (f := fun R => Subcube.extend R i true)
  have hsum := Nat.add_le_add h0 h1
  simpa [hcard] using hsum

/--
If two collections of subcubes cover all `1`-inputs of the restricted families
`F.restrict i false` and `F.restrict i true` respectively, then after extending
each subcube with the fixed value of `i` their union covers every `1`-input of
the original family `F`.  The hypothesis `hi₀`/`hi₁` ensures that the
coordinate `i` is not already fixed in the rectangles before extension.
-/
lemma cover_all_inputs_extend_union (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x,
        f x = true → ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true, ∀ x,
        f x = true → ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    ∀ f ∈ F, ∀ x, f x = true →
      ∃ R ∈ (R0.image (fun R => Subcube.extend R i false) ∪
              R1.image (fun R => Subcube.extend R i true)),
        x ∈ₛ R := by
  classical
  intro f hf x hx
  cases hxi : x i
  ·
    -- Case `x i = false`: use the cover for the `false` branch.
    have hg : BFunc.restrictCoord f i false ∈ F.restrict i false :=
      (Family.mem_restrict).2 ⟨f, hf, rfl⟩
    have hx' : BFunc.restrictCoord f i false x = true := by
      simpa [restrictCoord_agrees (f := f) (j := i) (b := false)
              (x := x) hxi] using hx
    obtain ⟨R, hR, hxR⟩ := hcov0 _ hg x hx'
    refine ⟨Subcube.extend R i false, ?_, ?_⟩
    · refine Finset.mem_union.mpr ?_
      refine Or.inl ?_
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    ·
      have hiR : i ∉ R.idx := hi0 R hR
      have : x ∈ₛ Subcube.extend R i false :=
        (Subcube.mem_extend_iff (R := R) (i := i) (b := false)
            (x := x) hiR).2 ⟨hxi, hxR⟩
      simpa using this
  ·
    -- Case `x i = true`.
    have hg : BFunc.restrictCoord f i true ∈ F.restrict i true :=
      (Family.mem_restrict).2 ⟨f, hf, rfl⟩
    have hx' : BFunc.restrictCoord f i true x = true := by
      simpa [restrictCoord_agrees (f := f) (j := i) (b := true)
              (x := x) hxi] using hx
    obtain ⟨R, hR, hxR⟩ := hcov1 _ hg x hx'
    refine ⟨Subcube.extend R i true, ?_, ?_⟩
    · refine Finset.mem_union.mpr ?_
      refine Or.inr ?_
      exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    ·
      have hiR : i ∉ R.idx := hi1 R hR
      have : x ∈ₛ Subcube.extend R i true :=
        (Subcube.mem_extend_iff (R := R) (i := i) (b := true)
            (x := x) hiR).2 ⟨hxi, hxR⟩
      simpa using this

/--
Combines covers of the restricted families `F.restrict i false` and
`F.restrict i true` into a cover of the original family `F`.  Each subcube in
the branch covers is assumed not to fix the splitting coordinate `i`; after
extension with the corresponding value of `i`, their union forms a cover for
`F`, and its size is bounded by the sum of branch sizes.
-/
lemma extend_union_cover (F : Family n) (i : Fin n)
    {R0 R1 : Finset (Subcube n)}
    (hmono0 : ∀ R ∈ R0, Subcube.monochromaticForFamily R (F.restrict i false))
    (hmono1 : ∀ R ∈ R1, Subcube.monochromaticForFamily R (F.restrict i true))
    (hcov0 : ∀ f ∈ F.restrict i false, ∀ x,
        f x = true → ∃ R ∈ R0, x ∈ₛ R)
    (hcov1 : ∀ f ∈ F.restrict i true, ∀ x,
        f x = true → ∃ R ∈ R1, x ∈ₛ R)
    (hi0 : ∀ R ∈ R0, i ∉ R.idx)
    (hi1 : ∀ R ∈ R1, i ∉ R.idx) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ R0.card + R1.card := by
  classical
  -- The final cover extends rectangles from both branches and unites them.
  let Rset :=
    R0.image (fun R => Subcube.extend R i false) ∪
      R1.image (fun R => Subcube.extend R i true)
  refine ⟨Rset, ?mono, ?cov, ?card⟩
  · -- Monochromaticity transfers from each branch to the corresponding extension.
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · -- Case: `R` comes from the `false` branch.
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      have hmonoS := hmono0 S hS
      have hiS : i ∉ S.idx := hi0 S hS
      -- Extend monochromaticity to the original family.
      exact Subcube.monochromaticForFamily_extend_restrict (F := F)
        (R := S) (i := i) (b := false) hiS hmonoS
    · -- Case: `R` comes from the `true` branch.
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      have hmonoS := hmono1 S hS
      have hiS : i ∉ S.idx := hi1 S hS
      exact Subcube.monochromaticForFamily_extend_restrict (F := F)
        (R := S) (i := i) (b := true) hiS hmonoS
  · -- Coverage follows from the branch covers via `cover_all_inputs_extend_union`.
    exact cover_all_inputs_extend_union (F := F) (i := i)
      (R0 := R0) (R1 := R1) hcov0 hcov1 hi0 hi1
  · -- The cardinality of the combined cover is bounded by the sum of branch sizes.
    exact card_extend_union_le (i := i) (R0 := R0) (R1 := R1) hi0 hi1

/--
Recursive cover construction driven by the three-component measure
`measureLex3`.  For a family `F` and a set of available coordinates `A` the
function returns a tentative set of subcubes.  At the moment this only provides
the structural recursion; proofs of monochromaticity and coverage are postponed
to future iterations.
-/
noncomputable def buildCoverLex3
    (F : Family n) (A : Finset (Fin n)) (s h : ℕ)
    [Fintype (Point n)]
    (hSens : ∀ f ∈ F, sensitivity f ≤ s)
    (hEnt  : measure F ≤ h) :
    Finset (Subcube n) :=
by
  classical
  -- Relation on pairs `(F, A)` induced by the lexicographic measure.
  let R : (Family n × Finset (Fin n)) → (Family n × Finset (Fin n)) → Prop :=
    fun p q => measureLex3Rel (measureLex3 p.1 p.2) (measureLex3 q.1 q.2)
  -- Well-foundedness follows from the corresponding result on `ℕ³`.
  have hWF : WellFounded R := by
    simpa [R] using
      (InvImage.wf (f := fun p : Family n × Finset (Fin n) =>
        measureLex3 p.1 p.2) measureLex3Rel_wf)
  -- Run the well-founded recursion.
  refine (hWF.fix (C := fun _ => Finset (Subcube n)) ?_ (F, A))
  intro p rec
  rcases p with ⟨F, A⟩
  -- Base case: constant family.
  by_cases hconst : ∃ b, ∀ f ∈ F, ∀ x, f x = b
  · exact {⟨∅, fun _ hi => False.elim (Finset.not_mem_empty _ hi)⟩}
  -- No coordinates left to branch on.
  by_cases hAempty : A = ∅
  · exact {⟨∅, fun _ hi => False.elim (Finset.not_mem_empty _ hi)⟩}
  -- Recursive step: pick a coordinate and split.
  have hAne : A.Nonempty := Finset.nonempty_of_ne_empty (by simpa [hAempty])
  let i : Fin n := hAne.choose
  have hiA : i ∈ A := hAne.choose_spec
  let F0 := F.restrict i false
  let F1 := F.restrict i true
  let A' := A.erase i
  let R0 :=
    rec ⟨F0, A'⟩
      (measureLex3_restrict_lt_dim (F := F) (A := A) (i := i) hiA (b := false))
  let R1 :=
    rec ⟨F1, A'⟩
      (measureLex3_restrict_lt_dim (F := F) (A := A) (i := i) hiA (b := true))
  exact
    R0.image (fun R => Subcube.extend R i false) ∪
      R1.image (fun R => Subcube.extend R i true)

/-- **Low-sensitivity cover** (statement only).  If every function in the
    family has sensitivity at most `s`, then there exists a small set of
    subcubes covering all ones of the family.  The proof will use decision
    trees or the Gopalan--Moshkovitz--Oliveira bound.  Here we only record the
    statement. -/
lemma low_sensitivity_cover (F : Family n) (s : ℕ)
    [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using decisionTree_cover (F := F) (s := s) Hsens

/-/ Variant of `low_sensitivity_cover` for a single Boolean function.
    This skeleton assumes a suitable decision tree for `f` of depth
    `O(s * log n)`.  All remaining steps are placeholders. -/

lemma low_sensitivity_cover_single
  (n s : ℕ) (f : BoolFunc.BFunc n)
    [Fintype (BoolFunc.Point n)]
    (Hsens : BoolFunc.sensitivity f ≤ s) :
  ∃ Rset : Finset (BoolFunc.Subcube n),
    (∀ R ∈ Rset, BoolFunc.Subcube.monochromaticFor R f) ∧
    (∀ x : BoolFunc.Point n, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  -- Treat `{f}` as a family and apply `decisionTree_cover`.
  have hfamily : ∀ g ∈ ({f} : Family n), sensitivity g ≤ s := by
    intro g hg
    have hg' : g = f := by simpa [Finset.mem_singleton] using hg
    simpa [hg'] using Hsens
  obtain ⟨Rset, hmono, hcov, hcard⟩ :=
    decisionTree_cover (F := ({f} : Family n)) (s := s) hfamily
  refine ⟨Rset, ?_, ?_, hcard⟩
  · intro R hR
    have := hmono R hR
    exact monochromaticFor_of_family_singleton this
  · intro x hx
    simpa using hcov f (by simp) x hx



/-- Specialized version of `low_sensitivity_cover` for the empty family.
    This is a small convenience wrapper around `decisionTree_cover_empty`. -/
lemma low_sensitivity_cover_empty (n s : ℕ)
    [Fintype (Point n)] :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R (∅ : Family n)) ∧
    (∀ f ∈ (∅ : Family n), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (coverConst * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using
    (decisionTree_cover_empty (n := n) (s := s))

end BoolFunc
