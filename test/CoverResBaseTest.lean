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
        (∀ R ∈ Rset, Subcube.monochromaticForFamily R constFamily) ∧
        (∀ f ∈ constFamily, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    decisionTree_cover_of_constant (n := 1) (F := constFamily) (s := 0) hconst
  exact trivial

-- The empty family admits the trivial cover returned by `decisionTree_cover_empty`.
example : True := by
  classical
  have _ :
      ∃ Rset : Finset (Subcube 1),
        (∀ R ∈ Rset, Subcube.monochromaticForFamily R (∅ : Family 1)) ∧
        (∀ f ∈ (∅ : Family 1), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    decisionTree_cover_empty (n := 1) (s := 0)
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
        (∀ R ∈ Rset, Subcube.monochromaticForFamily R (∅ : Family 1)) ∧
        (∀ f ∈ (∅ : Family 1), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
        Rset.card ≤ Nat.pow 2 (coverConst * 0 * Nat.log2 (Nat.succ 1)) :=
    low_sensitivity_cover_empty (n := 1) (s := 0)
  exact trivial
