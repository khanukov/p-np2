import Pnp.BoolFunc
import Pnp.BoolFunc.Support
import Pnp.DecisionTree
import Pnp.Agreement
import Pnp.Boolcube
import Pnp.CanonicalCircuit
import Pnp.ComplexityClasses
import Pnp.Entropy
import Pnp.Collentropy
import Pnp.LowSensitivityCover

open BoolFunc

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

-- A trivial Turing machine that always rejects in constant time.
def constFalseTM : TM :=
  { runTime := fun _ => 1,
    accepts := fun _ _ => false }

-- This machine decides the constantly false language in polynomial time.
example : polyTimeDecider (fun _ _ => false) := by
  refine ⟨constFalseTM, 1, ?h_run, ?h_accept⟩
  · intro n; simp [constFalseTM]
  · intro n x; rfl


end BasicTests
