import Pnp.BoolFunc
import Pnp.BoolFunc.Support
import Pnp.DecisionTree
import Pnp.Agreement
import Pnp.Boolcube
import Pnp.CanonicalCircuit
import Pnp.ComplexityClasses
import Pnp.NPSeparation
import Pnp.Entropy
import Pnp.Collentropy
import Pnp.LowSensitivityCover
import Pnp.AccMcspSat
import Pnp.Bound
import Pnp.CoverNumeric
import Pnp.LowSensitivity
import Pnp.MergeLowSens
import Pnp.TableLocality

open BoolFunc
open Bound

namespace BasicTests

/-- The support of a constant false function is empty. -/
lemma support_const_false (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

-- We can also verify that toggling an irrelevant coordinate leaves a
-- function unchanged by direct calculation.
example (x : Point 2) (b : Bool) :
    let f : BFunc 2 := fun y => y 0
    f x = f (Point.update x 1 b) := by
  classical
  let f : BFunc 2 := fun y => y 0
  have hneq : (0 : Fin 2) ≠ 1 := by decide
  simp [Point.update, hneq]

-- `eval_update_not_support` automatically shows that modifying a
-- non-essential coordinate leaves a function unchanged.
example (x : Point 2) (b : Bool) :
    (fun y : Point 2 => y 0) x = (fun y : Point 2 => y 0) (Point.update x 1 b) := by
  classical
  have hi : (1 : Fin 2) ∉ support (fun y : Point 2 => y 0) := by
    simp [support]
  have hx :=
    BoolFunc.eval_update_not_support
      (f := fun y : Point 2 => y 0) (i := 1) hi x b
  exact hx

-- A trivial decision tree has at most `2 ^ depth` leaves.
example :
    (DecisionTree.leaf true : DecisionTree 1).leaf_count ≤
      2 ^ (DecisionTree.depth (DecisionTree.leaf true : DecisionTree 1)) := by
  have hx :=
    DecisionTree.leaf_count_le_pow_depth
      (t := (DecisionTree.leaf true : DecisionTree 1))
  exact hx

example {n : ℕ} (x : Point n) :
    x ∈ₛ Agreement.Subcube.fromPoint (n := n) x Finset.univ := by
  classical
  intro i hi
  simp [Agreement.Subcube.fromPoint]

-- There exists a point where a non-trivial function evaluates to `true`.
example :
    ∃ x, (fun y : Point 1 => y 0) x = true := by
  classical
  have hmem : (0 : Fin 1) ∈ support (fun y : Point 1 => y 0) := by
    classical
    have hx : (fun y : Point 1 => y 0) (fun _ => false) ≠
        (fun y : Point 1 => y 0) (Point.update (fun _ => false) 0 true) := by
      simp [Point.update]
    exact mem_support_iff.mpr ⟨fun _ => false, hx⟩
  have hsupp : support (fun y : Point 1 => y 0) ≠ (∅ : Finset (Fin 1)) := by
    intro hempty
    simp [hempty] at hmem
  exact BoolFunc.exists_true_on_support (f := fun y : Point 1 => y 0) hsupp


-- Basic lemmas from `Boolcube`
example (n : ℕ) :
    (Boolcube.Subcube.full : Boolcube.Subcube n).dim = n := by
  classical
  simp

-- Basic bounds on collision probability.
example (F : Family 0) :
    0 ≤ collProb F ∧ collProb F ≤ 1 := by
  constructor
  · simp [BoolFunc.collProb_nonneg (F := F)]
  · simp [BoolFunc.collProb_le_one (F := F)]

-- Collision probability of a constant function is one.
example (n : ℕ) :
    BoolFunc.collProbFun (fun _ : Point n => false) = 1 := by
  classical
  simpa using BoolFunc.collProbFun_const_false (n := n)

-- Collision probability is bounded below by one half.
example (n : ℕ) (f : BFunc n) :
    (1 / 2 : ℝ) ≤ BoolFunc.collProbFun f := by
  classical
  simpa using BoolFunc.collProbFun_ge_half (f := f)

  -- A single-point subcube is monochromatic for any function.
  example {n : ℕ} (x : Point n) (f : BFunc n) :
      (Agreement.Subcube.fromPoint (n := n) x Finset.univ).monochromaticFor f := by
    classical
    exact Agreement.Subcube.monochromatic_point (x := x) (f := f)

  -- The low-sensitivity cover for a single function follows from `decisionTree_cover`.
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

  -- There exists a coordinate whose restriction drops the entropy by one bit.
  example :
      ∃ i : Fin 1, ∃ b : Bool,
        BoolFunc.H₂ (({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
          Family 1).restrict i b) ≤
          BoolFunc.H₂ ({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
            Family 1) - 1 := by
    classical
    have hn : 0 < (1 : ℕ) := by decide
    have hF : 1 < ({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
        Family 1).card := by
      classical
      have hne : (fun _ : Point 1 => true) ≠ (fun _ : Point 1 => false) := by
        intro h
        have := congrArg (fun f => f (fun _ => false)) h
        simp at this
      have hcard : ({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
          Family 1).card = 2 := by
        simp [hne]
      simp [hcard]
    simpa using
      BoolFunc.exists_coord_entropy_drop
        (F := {(fun _ : Point 1 => true), (fun _ : Point 1 => false)})
        hn hF

-- There exists a coordinate whose restriction halves the family size.
example :
    ∃ i : Fin 1, ∃ b : Bool,
      (({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
        Family 1).restrict i b).card ≤
      ({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
        Family 1).card / 2 := by
  classical
  have hn : 0 < (1 : ℕ) := by decide
  have hF : 1 < ({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
      Family 1).card := by
    classical
    have hne : (fun _ : Point 1 => true) ≠ (fun _ : Point 1 => false) := by
      intro h
      have := congrArg (fun f => f (fun _ => false)) h
      simp at this
    have hcard : ({(fun _ : Point 1 => true), (fun _ : Point 1 => false)} :
        Family 1).card = 2 := by
      simp [hne]
    simp [hcard]
  simpa using
    BoolFunc.exists_restrict_half
      (F := {(fun _ : Point 1 => true), (fun _ : Point 1 => false)}) hn hF

-- Evaluate a simple Boolean circuit.
example (x : Point 2) :
    Boolcube.Circuit.eval
      (Boolcube.Circuit.or
        (Boolcube.Circuit.and (Boolcube.Circuit.var 0)
                               (Boolcube.Circuit.not (Boolcube.Circuit.var 1)))
        (Boolcube.Circuit.var 1))
      x =
    (x 0 && !x 1) || x 1 := by
  classical
  cases hx : x 0 <;> cases hy : x 1 <;> simp [Boolcube.Circuit.eval, hx, hy]

-- Canonicalisation preserves evaluation.
example (n : ℕ) (c : Boolcube.Circuit n) (x : Boolcube.Point n) :
    Boolcube.Circuit.eval c x =
      Boolcube.Circuit.evalCanon (Boolcube.Circuit.canonical c) x := by
  simpa using Boolcube.Circuit.eval_canonical (c := c) (x := x)

-- Circuits with the same canonical form are extensionally equal.
example {n : ℕ} {c₁ c₂ : Boolcube.Circuit n}
    (h : Boolcube.Circuit.canonical c₁ = Boolcube.Circuit.canonical c₂)
    (x : Boolcube.Point n) :
    Boolcube.Circuit.eval c₁ x = Boolcube.Circuit.eval c₂ x := by
  have hfun := Boolcube.Circuit.canonical_inj (c₁ := c₁) (c₂ := c₂) h
  simpa using hfun x

-- Encoding length of a canonical circuit is bounded by `codeLen`.
example {n : ℕ} (c : Boolcube.Circuit.Canon n) :
    (Boolcube.Circuit.encodeCanon c).length ≤
      Boolcube.Circuit.codeLen c := by
  simpa using Boolcube.Circuit.encodeCanon_length (c := c)

-- The canonical description length of a circuit grows at most linearly with
-- its size (up to a logarithmic factor).
example {n : ℕ} (c : Boolcube.Circuit n) :
    Boolcube.Circuit.codeLen (Boolcube.Circuit.canonical c) ≤
      (sizeOf c) * (Nat.log2 n + 1) + 1 := by
  simpa using Boolcube.Circuit.canonical_desc_length (c := c)

-- A trivial Turing machine that always rejects in constant time.
def constFalseTM : TM :=
  { runTime := fun _ => 1,
    accepts := fun _ _ => false }

-- This machine decides the constantly false language in polynomial time.
example : polyTimeDecider (fun _ _ => false) := by
  refine ⟨constFalseTM, 1, ?h_run, ?h_accept⟩
  · intro n; simp [constFalseTM]
  · intro n x; rfl

-- Splitting a small vector using `leftBits`.
example (x : Fin 3 → Bool) :
    ACCSAT.leftBits (N := 3) (k := 1) (ℓ := 2) rfl x ⟨0, by decide⟩ = x 0 := by
  rfl

-- The convenience bound `n₀` is positive for every `h`.
example (h : ℕ) : 0 < Bound.n₀ h := by
  have hpow : 0 < Nat.pow 2 (10 * h) := pow_pos (by decide) _
  have hpos : 0 < 10000 * (h + 2) * Nat.pow 2 (10 * h) :=
    mul_pos (mul_pos (by decide) (Nat.succ_pos _)) hpow
  dsimp [Bound.n₀]
  exact hpos

-- `aux_growth` bounds the linear term by the exponential one.
example (h : ℕ) :
    (18 + 22 * h : ℝ) < 100 * (h + 2) * 2 ^ (10 * h) := by
  simpa using Bound.aux_growth h

-- Entropy-based numeric bound on cover size.
example {N Nδ : ℕ} (F : Family N)
    (h₂ : BoolFunc.H₂ F ≤ N - Nδ) :
    CoverNumeric.minCoverSize F ≤ 2 ^ (N - Nδ) := by
  simpa using CoverNumeric.numeric_bound (F := F) (Nδ := Nδ) h₂

-- Existence of a low-sensitivity cover for a finite set of functions.
example {n s : ℕ} (F : Finset (BoolFunc.Point n → Bool))
    (hF : F.Nonempty) :
    ∃ R : List (BoolFunc.Subcube n),
      R.length ≤ F.card * 2 ^ (4 * s * Nat.log2 (Nat.succ n)) := by
  obtain ⟨R, -, hlen⟩ := LowSensitivity.low_sensitivity_cover (F := F) (s := s) hF
  exact ⟨R, hlen⟩

-- Wrapper for entropy-based cover construction.
noncomputable example {n : ℕ} (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    Finset (BoolFunc.Subcube n) :=
  Boolcube.mergeLowSensitivityCover F h hH

-- Table locality reduces to `k = n` for the placeholder version.
example : ∃ k ≤ 1, True := by
  classical
  obtain ⟨k, hk, _⟩ := Boolcube.tableLocal (n := 1) (c := 1)
  exact ⟨k, hk, trivial⟩

-- Numeric bound on cover size is trivial to verify for small parameters.
example : 2 * 0 + 1 ≤ Cover.mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  exact Cover.numeric_bound (n := 1) (h := 0) hn

-- When no functions and no rectangles are present, there is no uncovered point.
example :
    Cover.firstUncovered (F := (∅ : BoolFunc.Family 1)) (Rset := (∅ : Finset (BoolFunc.Subcube 1))) = none := by
  classical
  simp [Cover.firstUncovered, Cover.uncovered, Cover.NotCovered]

-- The Family Collision-Entropy Lemma bounds the size of the entropy cover.
example {n h : ℕ} (F : Family n) (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn : n ≥ Bound.n₀ h) :
    (Boolcube.familyEntropyCover (F := F) (h := h) hH).rects.card <
      Nat.pow 2 (n / 100) := by
  simpa using Bound.FCE_lemma (F := F) (h := h) hH hn

-- A concrete instance of the sub-exponential bound.
example :
    Bound.mBound 20000 0 < Nat.pow 2 (20000 / 100) := by
  have h0 : (20000 : ℕ) ≥ Bound.n₀ 0 := by
    simp [Bound.n₀]
  exact Bound.mBound_lt_subexp (h := 0) (n := 20000) h0


end BasicTests
