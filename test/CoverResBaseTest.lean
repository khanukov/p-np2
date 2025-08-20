import Pnp2.low_sensitivity_cover

open BoolFunc

/-- A simple family consisting of the constantly-false function on one bit. -/
def constFamily : Family 1 :=
  ({fun (_ : Point 1) => false} : Finset (BFunc 1))

/-- The constantly-true function on one bit, used for evaluation tests. -/
def trueFamily : Family 1 :=
  ({fun (_ : Point 1) => true} : Finset (BFunc 1))

/-- Constructing a cover for a constant `false` family. -/
example : True := by
  classical
  have hconst : ∀ f ∈ constFamily, ∀ x, f x = false := by
    intro f hf x
    have h : f = (fun (_ : Point 1) => false) := by
      simpa [constFamily] using Finset.mem_singleton.mp hf
    simpa [h]
  let cover := CoverRes.const (F := constFamily) (b := false) hconst
  exact trivial

/-- Constructing an empty cover for the empty family. -/
example : True := by
  classical
  have cover := CoverRes.empty (n := 1)
  exact trivial

/-- Evaluating the decision tree generated from a constant `true` family. -/
example :
    DecisionTree.eval_tree
        (CoverRes.toDecisionTree (n := 1) (F := trueFamily)
          (CoverRes.const (F := trueFamily) (b := true)
            (by
              intro f hf x
              have h : f = (fun (_ : Point 1) => true) := by
                simpa [trueFamily] using Finset.mem_singleton.mp hf
              simpa [h])))
        (fun _ : Fin 1 => true) = true := by
  classical
  -- Evaluate the tree on the all-true point.
  simpa using
    (CoverRes.eval_true (n := 1) (F := trueFamily) (k := 1)
      (cover := CoverRes.const (F := trueFamily) (b := true)
        (by
          intro f hf x
          have h : f = (fun (_ : Point 1) => true) := by
            simpa [trueFamily] using Finset.mem_singleton.mp hf
          simpa [h]))
      (f := fun _ : Point 1 => true) (by simp [trueFamily])
      (x := fun _ : Fin 1 => true) (by simp))

/-- Extracting a plain cover from a `CoverRes` using `CoverRes.as_cover`. -/
example : True := by
  classical
  have hconst : ∀ f ∈ constFamily, ∀ x, f x = false := by
    intro f hf x
    have h : f = (fun (_ : Point 1) => false) := by
      simpa [constFamily] using Finset.mem_singleton.mp hf
    simpa [h]
  let cover := CoverRes.const (F := constFamily) (b := false) hconst
  have _h :=
    CoverRes.as_cover (n := 1) (F := constFamily) (k := 1)
      (k' := Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1))) cover
      (by
        -- The target bound simplifies to `1`, matching the size of the cover.
        simp [coverConst])
  exact trivial

-- Bounding the depth of the generated tree via the number of rectangles.
example : True := by
  classical
  -- Construct the singleton cover and apply the depth bound.
  have cover := CoverRes.const (F := trueFamily) (b := true)
    (by
      intro f hf x
      have h : f = (fun (_ : Point 1) => true) := by
        simpa [trueFamily] using Finset.mem_singleton.mp hf
      simpa [h])
  have _ :
      DecisionTree.depth (CoverRes.toDecisionTree (n := 1) (F := trueFamily) cover)
        ≤ 1 :=
    by
      -- The general lemma gives `depth ≤ n * |Rset| = 1` for this cover.
      simpa using
        (CoverRes.depth_le_card_mul (n := 1) (F := trueFamily) (k := 1) cover)
  exact trivial

-- Specialised depth bound using `coverConst`.
example : True := by
  classical
  have cover0 := CoverRes.const (F := trueFamily) (b := true)
    (by
      intro f hf x
      have h : f = (fun (_ : Point 1) => true) := by
        simpa [trueFamily] using Finset.mem_singleton.mp hf
      simpa [h])
  -- Repackage the cover with the larger bound expected by `depth_le_coverConst`.
  have hpow : 1 ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) := by
    have hpos : 0 < Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
      pow_pos (by decide) _
    exact Nat.succ_le_of_lt hpos
  let cover : CoverRes (F := trueFamily)
      (Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1))) :=
    { rects := cover0.rects
      , mono := cover0.mono
      , covers := cover0.covers
      , card_le := le_trans cover0.card_le hpow }
  have _ :
      DecisionTree.depth (CoverRes.toDecisionTree (n := 1) (F := trueFamily) cover)
        ≤ 1 * Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    by
      simpa [coverConst] using
        (CoverRes.depth_le_coverConst (n := 1) (s := 0) (F := trueFamily) cover)
  exact trivial

-- Obtaining a cover for a constant family via `decisionTree_cover_of_constant`.
example : True := by
  classical
  have hconst : ∃ b, ∀ f ∈ constFamily, ∀ x, f x = b := by
    refine ⟨false, ?_⟩
    intro f hf x
    have h : f = (fun (_ : Point 1) => false) := by
      simpa [constFamily] using Finset.mem_singleton.mp hf
    simpa [h]
  have _ :
      ∃ Rset : Finset (Subcube 1),
        (∀ f ∈ constFamily, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
        (∀ f ∈ constFamily, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    decisionTree_cover_of_constant (n := 1) (F := constFamily) (s := 0) hconst
  exact trivial

-- The empty family admits the trivial cover returned by `decisionTree_cover_empty`.
example : True := by
  classical
  have _ :
      ∃ Rset : Finset (Subcube 1),
        (∀ f ∈ (∅ : Family 1), ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
        (∀ f ∈ (∅ : Family 1), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    decisionTree_cover_empty (n := 1) (s := 0)
  exact trivial

-- Direct use of `decisionTree_cover_of_coverResP` on a constant family.
example : True := by
  classical
  -- Construct the trivial pointwise cover.
  have hconst : ∀ f ∈ constFamily, ∀ x, f x = false := by
    intro f hf x
    have h : f = (fun (_ : Point 1) => false) := by
      simpa [constFamily] using Finset.mem_singleton.mp hf
    simpa [h]
  let cover := CoverResP.const (F := constFamily) (b := false) hconst
  have hpow : 1 ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) := by
    have hpos : 0 < Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
      pow_pos (by decide) _
    exact Nat.succ_le_of_lt hpos
  have _ :
      ∃ Rset : Finset (Subcube 1),
        (∀ f ∈ constFamily, ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
        (∀ f ∈ constFamily, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    decisionTree_cover_of_coverResP (n := 1) (F := constFamily) (s := 0)
      (cover := cover) hpow
  exact trivial

-- Specialisation to a single function using `low_sensitivity_cover_single`.
example : True := by
  classical
  -- Prove the sensitivity bound for the constant `false` function directly.
  have hSens : BoolFunc.sensitivity (fun _ : BoolFunc.Point 1 => false) ≤ 0 := by
    simpa using (le_of_eq (BoolFunc.sensitivity_const (n := 1) (b := false)))
  have _ :
      ∃ Rset : Finset (BoolFunc.Subcube 1),
        (∀ R ∈ Rset,
            BoolFunc.Subcube.monochromaticFor R (fun _ : BoolFunc.Point 1 => false)) ∧
        (∀ x : BoolFunc.Point 1, (fun _ : BoolFunc.Point 1 => false) x = true →
            ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    low_sensitivity_cover_single (n := 1) (s := 0)
      (f := fun _ : BoolFunc.Point 1 => false) hSens
  exact trivial

-- Wrapper lemma for the empty family `low_sensitivity_cover_empty`.
example : True := by
  classical
  have _ :
      ∃ Rset : Finset (Subcube 1),
        (∀ f ∈ (∅ : Family 1), ∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
        (∀ f ∈ (∅ : Family 1), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    low_sensitivity_cover_empty (n := 1) (s := 0)
  exact trivial

/-- Evaluating the decision tree produced from a pointwise cover. -/
example : True := by
  classical
  -- Prepare the constant `true` family and its pointwise cover.
  have hconst : ∀ f ∈ trueFamily, ∀ x, f x = true := by
    intro f hf x
    have h : f = (fun (_ : Point 1) => true) := by
      simpa [trueFamily] using Finset.mem_singleton.mp hf
    simpa [h]
  let cover := CoverResP.const (F := trueFamily) (b := true) hconst
  have hf : (fun (_ : Point 1) => true) ∈ trueFamily := by
    simp [trueFamily]
  -- The resulting decision tree evaluates to `true` on the all-true input.
  have _ :
      DecisionTree.eval_tree
          (CoverResP.toDecisionTree_for (n := 1) (F := trueFamily) (k := 1)
            cover (f := fun _ : Point 1 => true) hf)
          (fun _ : Fin 1 => true) = true := by
    simpa using
      (CoverResP.eval_true (n := 1) (F := trueFamily) (k := 1)
        (cover := cover) (f := fun _ : Point 1 => true) hf
        (x := fun _ : Fin 1 => true) (by simp))
  exact trivial

/-- `buildCoverLex3` first erases constantly `false` functions before
constructing the pointwise cover.  The remaining functions are covered as in
the base case. -/
example : True := by
  classical
  -- One constantly `false` function and one sensitive identity function.
  let f₀ : BFunc 1 := fun _ => false
  let f₁ : BFunc 1 := fun x => x 0
  let F : Family 1 := {f₀, f₁}
  have hn : 0 < 1 := by decide
  have hbase : (1 : ℕ) ≤ 5 * 1 := by decide
  -- Build the cover; the `false` function is discarded internally.
  let cover := buildCoverLex3 (F := F) (h := 1) hn hbase
  have hf₁F : f₁ ∈ F := by simp [F]
  -- Evaluate on the `true` input; the decision tree should return `true`.
  have _ :
      DecisionTree.eval_tree
          (CoverResP.toDecisionTree_for (n := 1) (F := F)
            (k := Cover2.mBound 1 (1 + 1)) cover (f := f₁) hf₁F)
          (fun _ : Fin 1 => true) = true := by
    simpa [f₁] using
      (CoverResP.eval_true (n := 1) (F := F)
        (k := Cover2.mBound 1 (1 + 1)) (cover := cover) (f := f₁) hf₁F
        (x := fun _ : Fin 1 => true) (by simp [f₁]))
  exact trivial

/-- `buildCoverLex3` collapses to a single rectangle when the family has no
sensitive coordinates. -/
example : True := by
  classical
  -- The singleton family containing only the constantly `true` function.
  let f : BFunc 1 := fun _ => true
  let F : Family 1 := {f}
  have hn : 0 < 1 := by decide
  have hbase : (1 : ℕ) ≤ 5 * 1 := by decide
  -- Build the cover; it should be the constant full cube.
  let cover := buildCoverLex3 (F := F) (h := 1) hn hbase
  -- The cover contains exactly one rectangle.
  have : cover.rects.card = 1 := by
    -- Simplify the definition using the constant-family branch.
    have hfalse : ¬ ∃ f' ∈ F, ∀ x, f' x = false := by
      intro h; rcases h with ⟨g, hg, hgfalse⟩
      have : g = f := by simpa [F] using Finset.mem_singleton.mp hg
      subst this; have := hgfalse (fun _ => true); simp [f] at this
    have hsens : ¬ ∃ i : Fin 1, sensitiveCoord F i := by
      simp [F, f, sensitiveCoord]
    have hconst : ∀ g ∈ F, ∀ x, g x = true := by
      simpa [F, f] using
        all_true_of_no_sensitive_coord (F := F)
          (hins := not_exists.mp hsens) (hfalse := hfalse)
    -- Evaluate `buildCoverLex3` in this constant-family setting and
    -- compute the number of rectangles explicitly.
    have hcard : cover.rects.card = 1 := by
      -- Use `hsens` to simplify away the sensitive-branch `if`.
      have hsens0 : ¬ sensitiveCoord F 0 := by
        simpa using (not_exists.mp hsens 0)
      simp [cover, buildCoverLex3, buildCoverLex3A, hfalse, hsens0,
        CoverResP.const_mBound, CoverResP.const]
    simpa [hcard]
  -- Sanity check: the single rectangle covers the all-true input.
  have hfF : f ∈ F := by simp [F]
  have _ :
      DecisionTree.eval_tree
          (CoverResP.toDecisionTree_for (n := 1) (F := F)
            (k := Cover2.mBound 1 (1 + 1)) cover (f := f) hfF)
          (fun _ : Fin 1 => true) = true := by
    simpa [f] using
      (CoverResP.eval_true (n := 1) (F := F)
        (k := Cover2.mBound 1 (1 + 1)) (cover := cover) (f := f) hfF
        (x := fun _ : Fin 1 => true) (by simp [f]))
  exact trivial

/-- Lifting a cover after reintroducing a constantly `false` function. -/
example : True := by
  classical
  -- Define two Boolean functions and their family.
  let f0 : BFunc 1 := fun _ => false
  let f1 : BFunc 1 := fun _ => true
  let F : Family 1 := ({f0, f1} : Finset (BFunc 1))
  -- Witness that `f0` belongs to the family and is constantly `false`.
  have hf0F : f0 ∈ F := by simp [F]
  have hf0false : ∀ x : Point 1, f0 x = false := by intro x; simp [f0]
  -- Cover the subfamily without `f0`, which reduces to the constant `true` family.
  have hconst1 : ∀ f ∈ F.erase f0, ∀ x, f x = true := by
    intro f hf x
    have hfmem : f ∈ ({f1} : Finset (BFunc 1)) := by
      -- Simplify membership in the erased family and eliminate the `f0` case.
      have hf' := Finset.mem_erase.mp hf
      have : f ∈ ({f0, f1} : Finset (BFunc 1)) := by
        simpa [F] using hf'.2
      -- Analyse membership in the two-element set.
      have hcases := Finset.mem_insert.mp this
      cases hcases with
      | inl h => cases hf'.1 h
      | inr h => exact h
    have hf' : f = f1 := by
      simpa using Finset.mem_singleton.mp hfmem
    subst hf'
    simp [f1]
  let cover' := CoverResP.const (F := F.erase f0) (b := true) hconst1
  -- Lift the cover back to the original family `F`.
  let cover :=
    CoverResP.lift_erase_false (n := 1) (F := F) (f₀ := f0) (k := 1)
      hf0F hf0false cover'
  -- Evaluate the resulting decision tree for the `true` function.
  have hf1F : f1 ∈ F := by simp [F]
  have _ :
      DecisionTree.eval_tree
          (CoverResP.toDecisionTree_for (n := 1) (F := F) (k := 1)
            cover (f := f1) hf1F)
          (fun _ : Fin 1 => true) = true := by
    simpa [f1] using
      (CoverResP.eval_true (n := 1) (F := F) (k := 1)
        (cover := cover) (f := f1) hf1F
        (x := fun _ : Fin 1 => true) (by simp [f1]))
  exact trivial

/-- Gluing covers of the false and true branches via `glue_branch_coversPw`. -/
example : True := by
  classical
  -- Define the identity function on one bit and the singleton family containing it.
  let f : BFunc 1 := fun x => x 0
  let F : Family 1 := {f}
  -- On the `false` branch the restricted function is constantly `false`.
  have hconst0 : ∀ g ∈ F.restrict 0 false, ∀ x, g x = false := by
    intro g hg x
    rcases (Family.mem_restrict (F := F) (i := (0 : Fin 1)) (b := false)).1 hg with
      ⟨f', hf', rfl⟩
    have hf' : f' = f := by
      simpa [F] using Finset.mem_singleton.mp hf'
    subst hf'
    simp [f, BFunc.restrictCoord]
  -- Similarly, the `true` branch is constantly `true`.
  have hconst1 : ∀ g ∈ F.restrict 0 true, ∀ x, g x = true := by
    intro g hg x
    rcases (Family.mem_restrict (F := F) (i := (0 : Fin 1)) (b := true)).1 hg with
      ⟨f', hf', rfl⟩
    have hf' : f' = f := by
      simpa [F] using Finset.mem_singleton.mp hf'
    subst hf'
    simp [f, BFunc.restrictCoord]
  -- Assemble the branch covers and glue them.
  let cover0 :=
    CoverResP.const (F := F.restrict 0 false) (b := false) hconst0
  let cover1 :=
    CoverResP.const (F := F.restrict 0 true)  (b := true)  hconst1
  -- Functions in the restricted families are insensitive to the splitting coordinate.
  have hins0 := coordSensitivity_family_restrict_self_zero (F := F) (i := (0 : Fin 1))
      (b := false)
  have hins1 := coordSensitivity_family_restrict_self_zero (F := F) (i := (0 : Fin 1))
      (b := true)
  let cover :=
    glue_branch_coversPw (F := F) (i := (0 : Fin 1)) cover0 cover1 hins0 hins1
  -- The resulting decision tree correctly recognises the `true` input.
  have hfF : f ∈ F := by simp [F]
  have _ :
      DecisionTree.eval_tree
          (CoverResP.toDecisionTree_for (n := 1) (F := F) (k := 2)
            cover (f := f) hfF)
          (fun _ : Fin 1 => true) = true := by
    simpa [f] using
      (CoverResP.eval_true (n := 1) (F := F) (k := 2)
        (cover := cover) (f := f) hfF
        (x := fun _ : Fin 1 => true) (by simp [f]))
  exact trivial

/-- Bounding the size of glued branch covers via `glue_branch_coversPw_mBound`. -/
example : True := by
  classical
  -- Same setup as above: a single identity function on one bit.
  let f : BFunc 1 := fun x => x 0
  let F : Family 1 := {f}
  have hconst0 : ∀ g ∈ F.restrict 0 false, ∀ x, g x = false := by
    intro g hg x
    rcases (Family.mem_restrict (F := F) (i := (0 : Fin 1)) (b := false)).1 hg with
      ⟨f', hf', rfl⟩
    have hf' : f' = f := by
      simpa [F] using Finset.mem_singleton.mp hf'
    subst hf'
    simp [f, BFunc.restrictCoord]
  have hconst1 : ∀ g ∈ F.restrict 0 true, ∀ x, g x = true := by
    intro g hg x
    rcases (Family.mem_restrict (F := F) (i := (0 : Fin 1)) (b := true)).1 hg with
      ⟨f', hf', rfl⟩
    have hf' : f' = f := by
      simpa [F] using Finset.mem_singleton.mp hf'
    subst hf'
    simp [f, BFunc.restrictCoord]
  -- Each branch is covered by a single rectangle; relax the cardinality to `mBound`.
  let cover0' :=
    CoverResP.const (F := F.restrict 0 false) (b := false) hconst0
  let cover1' :=
    CoverResP.const (F := F.restrict 0 true)  (b := true)  hconst1
  have hk0 : cover0'.rects.card ≤ Cover2.mBound 1 0 :=
    le_trans cover0'.card_le
      (Nat.succ_le_of_lt (Cover2.mBound_pos (n := 1) (h := 0) (hn := by decide)))
  have hk1 : cover1'.rects.card ≤ Cover2.mBound 1 0 :=
    le_trans cover1'.card_le
      (Nat.succ_le_of_lt (Cover2.mBound_pos (n := 1) (h := 0) (hn := by decide)))
  let cover0 : CoverResP (F := F.restrict 0 false) (Cover2.mBound 1 0) :=
    { rects := cover0'.rects, monoPw := cover0'.monoPw, covers := cover0'.covers, card_le := hk0 }
  let cover1 : CoverResP (F := F.restrict 0 true) (Cover2.mBound 1 0) :=
    { rects := cover1'.rects, monoPw := cover1'.monoPw, covers := cover1'.covers, card_le := hk1 }
  have hins0 := coordSensitivity_family_restrict_self_zero (F := F)
      (i := (0 : Fin 1)) (b := false)
  have hins1 := coordSensitivity_family_restrict_self_zero (F := F)
      (i := (0 : Fin 1)) (b := true)
  -- Gluing with an explicit `mBound` cardinality estimate.
  let cover :=
    glue_branch_coversPw_mBound (F := F) (i := (0 : Fin 1)) (h := 0)
      cover0 cover1 hins0 hins1
  -- The constructed cover contains at most `mBound 1 (0+1)` rectangles.
  have _ : cover.rects.card ≤ Cover2.mBound 1 (0 + 1) := cover.card_le
  exact trivial
/-- Building a cover via `buildCoverLex3` in the base case `n ≤ 5*h`. -/
example : True := by
  classical
  -- Single sensitive function on one bit.
  let f : BFunc 1 := fun x => x 0
  let F : Family 1 := {f}
  -- `buildCoverLex3` requires a positive dimension and the inequality `n ≤ 5*h`.
  have hn : 0 < 1 := by decide
  have hbase : (1 : ℕ) ≤ 5 * 1 := by decide
  let cover := buildCoverLex3 (F := F) (h := 1) hn hbase
  -- Evaluate the resulting decision tree on the `true` input.
  have hfF : f ∈ F := by simp [F]
  have _ :
      DecisionTree.eval_tree
          (CoverResP.toDecisionTree_for (n := 1) (F := F)
            (k := Cover2.mBound 1 (1 + 1)) cover (f := f) hfF)
          (fun _ : Fin 1 => true) = true := by
    simpa [f] using
      (CoverResP.eval_true (n := 1) (F := F)
        (k := Cover2.mBound 1 (1 + 1)) (cover := cover) (f := f) hfF
        (x := fun _ : Fin 1 => true) (by simp [f]))
  exact trivial

/-- Even in the degenerate family `{id, not}`, restricting along the sensitive
coordinate decreases the three-component measure `measureLex3`. -/
example : True := by
  classical
  -- Two opposing functions on one bit.
  let f_id  : BFunc 1 := fun x => x 0
  let f_not : BFunc 1 := fun x => !x 0
  let F : Family 1 := {f_id, f_not}
  -- Coordinate `0` is sensitive for this family.
  have hsens : sensitiveCoord F (0 : Fin 1) := by
    refine ⟨f_id, by simp [F, f_id], ?_⟩
    refine ⟨fun _ => false, ?_⟩
    simp [f_id]
  -- Instantiate the existential lemma on the singleton set `{0}`.
  have hA : (0 : Fin 1) ∈ ({0} : Finset (Fin 1)) := by simp
  have h := exists_branch_measure_drop_of_sensitive (F := F)
      (A := ({0} : Finset (Fin 1))) ⟨0, hA, hsens⟩
  -- Extract the witness and confirm measure drop for both branches.
  obtain ⟨i, hi, hdrop⟩ := h
  have _ := hdrop false
  have _ := hdrop true
  exact trivial

/-- Specialised variant `exists_branch_measure_drop_univ` also detects the
measure decrease when branching on the sensitive coordinate of `{id, not}`. -/
example : True := by
  classical
  let f_id  : BFunc 1 := fun x => x 0
  let f_not : BFunc 1 := fun x => !x 0
  let F : Family 1 := {f_id, f_not}
  -- The family has a sensitive coordinate at `0`.
  have hsens : ∃ i : Fin 1, sensitiveCoord F i := by
    refine ⟨0, ?_⟩
    refine ⟨f_id, by simp [F, f_id], ?_⟩
    refine ⟨fun _ => false, ?_⟩
    simp [f_id]
  -- Applying the specialised lemma on the universal set.
  have h := exists_branch_measure_drop_univ (F := F) hsens
  obtain ⟨i, hdrop⟩ := h
  have _ := hdrop false
  have _ := hdrop true
  exact trivial
