import Pnp2.cover2
import Pnp2.BoolFunc

open Boolcube (Point Subcube)
open BoolFunc (BFunc Family)

open Cover2

namespace Cover2Test

/-- `mBound` is computed via the wrapper definition. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- Numeric bound specialised to trivial parameters using the positive version. -/
example : 2 * 0 + 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simp [numeric_bound_pos (n := 1) (h := 0) hn]

/-- `numeric_bound_pos` also holds when `n` is strictly positive. -/
example : 2 * 0 + 2 ≤ mBound 2 0 := by
  have hn : 0 < (2 : ℕ) := by decide
  simp [numeric_bound_pos (n := 2) (h := 0) hn]

/-- Doubling the bound for a smaller budget stays below the next budget. -/
example : 2 * mBound 1 0 ≤ mBound 1 1 := by
  simpa using two_mul_mBound_le_succ (n := 1) (h := 0)

/-- `pow_le_mBound_simple` for trivial parameters. -/
example : 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simp [pow_le_mBound_simple (n := 1) (h := 0) hn]

/-- `two_le_mBound` verifies the bound is at least `2`. -/
example : 2 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simp [two_le_mBound (n := 1) (h := 0) hn]

/-- Doubling the bound for `h = 0` stays below the next budget. -/
example : 2 * mBound 1 0 ≤ mBound 1 1 := by
  simpa using two_mul_mBound_le_succ (n := 1) (h := 0)

/-- Inserting a single rectangle stays within the next budget. -/
example :
    (insert Subcube.full (∅ : Finset (Subcube 1))).card ≤ mBound 1 1 := by
  classical
  have hcard : ( (∅ : Finset (Subcube 1)).card ) ≤ mBound 1 0 := by
    simp [mBound]
  have hn : 0 < (1 : ℕ) := by decide
  simpa using
    (card_insert_mBound_succ (n := 1) (h := 0)
      (Rset := (∅ : Finset (Subcube 1))) (R := Subcube.full)
      hcard hn)

/-- Nothing is covered by an empty set of rectangles. -/
example (x : Point 1) :
    Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
  simpa using Cover2.notCovered_empty (n := 1) (x := x)

/-- `NotCovered` is monotone under set inclusion. -/
example (x : Point 1) (R : Subcube 1)
    (hx : Cover2.NotCovered (n := 1) (Rset := {R}) x) :
    Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
  have hsub : (∅ : Finset (Subcube 1)) ⊆ {R} := by
    intro r hr; cases hr
  simpa using
    Cover2.NotCovered.monotone (n := 1) (R₁ := (∅ : Finset (Subcube 1)))
      (R₂ := {R}) hsub hx

/-- A single full rectangle covers all `1`-inputs. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) := by
  exact Cover2.AllOnesCovered.full _

/-- `AllOnesCovered.superset` allows enlarging the rectangle set. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full, Subcube.full} : Finset (Subcube 1)) := by
  classical
  have hcov : Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) :=
    Cover2.AllOnesCovered.full _
  have hsub : ({Subcube.full} : Finset (Subcube 1)) ⊆ {Subcube.full, Subcube.full} := by
    intro R hR
    simp [Finset.mem_insert, Finset.mem_singleton] at hR
    simp [Finset.mem_insert, Finset.mem_singleton, hR]
  exact
    Cover2.AllOnesCovered.superset (F := {(fun _ : Point 1 => true)})
      (R₁ := {Subcube.full}) (R₂ := {Subcube.full, Subcube.full})
      hcov hsub

/-- The union of two covers is again a cover. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} ∪ {Subcube.full} : Finset (Subcube 1)) := by
  classical
  have hcov := Cover2.AllOnesCovered.full
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
  simpa using
    Cover2.AllOnesCovered.union (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (R₁ := {Subcube.full}) (R₂ := {Subcube.full}) hcov hcov

/-- Inserting a rectangle preserves coverage. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (insert Subcube.full {Subcube.full} : Finset (Subcube 1)) := by
  classical
  have hcov := Cover2.AllOnesCovered.full
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
  simpa using
    Cover2.AllOnesCovered.insert (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := {Subcube.full}) (R := Subcube.full) hcov

/-- If all `1`-inputs are covered by a single full rectangle, the uncovered set
is empty. -/
example :
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) = (∅ : Set (Sigma (fun _ => Point 1))) := by
  have hcov := Cover2.AllOnesCovered.full
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
  simpa using
    Cover2.uncovered_eq_empty_of_allCovered
      (n := 1)
      (F := {(fun _ : Point 1 => true)})
      (Rset := {Subcube.full}) hcov

/-- Adding a rectangle cannot create new uncovered pairs (singleton version). -/
example (R : Subcube 1) :
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ((∅ : Finset (Subcube 1)) ∪ {R}) ⊆
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) := by
  classical
  simpa using
    Cover2.uncovered_subset_of_union_singleton
      (n := 1)
      (F := {(fun _ : Point 1 => true)})
      (Rset := (∅ : Finset (Subcube 1))) (R := R)

/-- Adding a set of rectangles cannot create new uncovered pairs. -/
example (R₁ R₂ : Finset (Subcube 1)) :
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (R₁ ∪ R₂) ⊆
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      R₁ := by
  classical
  simpa using
    Cover2.uncovered_subset_of_union
      (n := 1)
      (F := {(fun _ : Point 1 => true)})
      (R₁ := R₁) (R₂ := R₂)

/-- Inserting a rectangle never increases the measure `mu`. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) ≤
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  simpa using
    Cover2.mu_union_singleton_le
      (n := 1)
      (F := {(fun _ : Point 1 => true)})
      (Rset := (∅ : Finset (Subcube 1)))
      (R := Subcube.full) (h := 0)

/-- Adding a rectangle that covers a new input strictly decreases the measure. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) <
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- Build a witness pair covered by `Subcube.full`.
  let f : BFunc 1 := fun _ => true
  let x : Point 1 := fun _ => true
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hxval : f x = true := by simp [f, x]
  have hnc : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
    intro R hR; cases hR
  have hx : ∃ p ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)), p.2 ∈ₛ Subcube.full := by
    refine ⟨⟨f, x⟩, ?_, ?_⟩
    · exact ⟨hf, hxval, hnc⟩
    · simp [x]
  simpa using
    Cover2.mu_union_singleton_lt
      (n := 1) (F := {f})
      (Rset := (∅ : Finset (Subcube 1)))
      (R := Subcube.full) (h := 0) hx

/-- `mu_union_singleton_succ_le` provides a convenient inequality on measures. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) + 1 ≤
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- Reuse the witness from the previous example.
  let f : BFunc 1 := fun _ => true
  let x : Point 1 := fun _ => true
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hxval : f x = true := by simp [f, x]
  have hnc : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
    intro R hR; cases hR
  have hx : ∃ p ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)), p.2 ∈ₛ Subcube.full := by
    refine ⟨⟨f, x⟩, ?_, ?_⟩
    · exact ⟨hf, hxval, hnc⟩
    · simp [x]
  simpa using
    Cover2.mu_union_singleton_succ_le
      (n := 1) (F := {f})
      (Rset := (∅ : Finset (Subcube 1)))
      (R := Subcube.full) (h := 0) hx

/-- `mu_union_singleton_double_lt` specialises the strict inequality to two
distinct uncovered pairs. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) <
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- Two uncovered inputs for the constant-true function.
  let f : BFunc 1 := fun _ => true
  let x₁ : Point 1 := fun _ => true
  let x₂ : Point 1 := fun _ => false
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hnc₁ : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x₁ := by
    intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x₂ := by
    intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) := ⟨hf, hx₂val, hnc₂⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hxne : x₁ ≠ x₂ := by
    intro hx
    have h0 : x₁ 0 = x₂ 0 := congrArg (fun p => p 0) hx
    simpa [x₁, x₂] using h0
  have hne : (⟨f, x₁⟩ : Σ g : BFunc 1, Point 1) ≠ ⟨f, x₂⟩ := by
    intro h; apply hxne; exact congrArg Sigma.snd h
  simpa using
    Cover2.mu_union_singleton_double_lt
      (n := 1) (F := {f}) (Rset := (∅ : Finset (Subcube 1)))
      (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩)
      hp₁ hp₂ hx₁R hx₂R hne

/-- `mu_union_double_succ_le` bounds the measure drop when the covering
rectangle is part of a larger set. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) + 2 ≤
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- Reuse the witnesses from the previous example.
  let f : BFunc 1 := fun _ => true
  let x₁ : Point 1 := fun _ => true
  let x₂ : Point 1 := fun _ => false
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hnc₁ : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x₂ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) := ⟨hf, hx₂val, hnc₂⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hxne : x₁ ≠ x₂ := by
    intro hx; have h0 : x₁ 0 = x₂ 0 := congrArg (fun p => p 0) hx
    simpa [x₁, x₂] using h0
  have hne : (⟨f, x₁⟩ : Σ g : BFunc 1, Point 1) ≠ ⟨f, x₂⟩ := by
    intro h; apply hxne; exact congrArg Sigma.snd h
  have hmem : Subcube.full ∈ ({Subcube.full} : Finset (Subcube 1)) := by simp
  simpa using
    Cover2.mu_union_double_succ_le
      (n := 1) (F := {f}) (R₁ := (∅ : Finset (Subcube 1)))
      (R₂ := {Subcube.full}) (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩)
      hp₁ hp₂ hx₁R hx₂R hne hmem

/-- `mu_union_double_lt` yields a strict inequality for the same setup. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) <
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- Reuse the same witnesses as above.
  let f : BFunc 1 := fun _ => true
  let x₁ : Point 1 := fun _ => true
  let x₂ : Point 1 := fun _ => false
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hnc₁ : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x₂ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) := ⟨hf, hx₂val, hnc₂⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hxne : x₁ ≠ x₂ := by
    intro hx; have h0 : x₁ 0 = x₂ 0 := congrArg (fun p => p 0) hx
    simpa [x₁, x₂] using h0
  have hne : (⟨f, x₁⟩ : Σ g : BFunc 1, Point 1) ≠ ⟨f, x₂⟩ := by
    intro h; apply hxne; exact congrArg Sigma.snd h
  have hmem : Subcube.full ∈ ({Subcube.full} : Finset (Subcube 1)) := by simp
  simpa using
    Cover2.mu_union_double_lt
      (n := 1) (F := {f}) (R₁ := (∅ : Finset (Subcube 1)))
      (R₂ := {Subcube.full}) (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩)
      hp₁ hp₂ hx₁R hx₂R hne hmem

/-- `mu_union_triple_succ_le` bounds the drop when a rectangle from a larger
family covers three distinct uncovered pairs. -/
example :
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 ((
            (∅ : Finset (Subcube 2))
            ) ∪ {Subcube.full}) + 3 ≤
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 (∅ : Finset (Subcube 2)) := by
  classical
  -- Three uncovered inputs for the constant-true function.
  let f : BFunc 2 := fun _ => true
  let x₁ : Point 2 := fun _ => true
  let x₂ : Point 2 := fun
    | 0 => false
    | 1 => true
  let x₃ : Point 2 := fun
    | 0 => true
    | 1 => false
  have hf : f ∈ ({f} : BoolFunc.Family 2) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hx₃val : f x₃ = true := by simp [f, x₃]
  have hnc₁ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₂ :=
    by intro R hR; cases hR
  have hnc₃ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₃ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₂val, hnc₂⟩
  have hp₃ : ⟨f, x₃⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₃val, hnc₃⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hx₃R : x₃ ∈ₛ Subcube.full := by simp [x₃]
  have hne₁₂ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₂⟩ := by
    intro h
    have hx : x₁ = x₂ := congrArg Sigma.snd h
    have hx0 : x₁ 0 = x₂ 0 := congrArg (fun g => g 0) hx
    simp [x₁, x₂] at hx0
  have hne₁₃ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₁ = x₃ := congrArg Sigma.snd h
    have hx0 : x₁ 1 = x₃ 1 := congrArg (fun g => g 1) hx
    simp [x₁, x₃] at hx0
  have hne₂₃ : (⟨f, x₂⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₂ = x₃ := congrArg Sigma.snd h
    have hx0 : x₂ 0 = x₃ 0 := congrArg (fun g => g 0) hx
    simp [x₂, x₃] at hx0
  have hmem : Subcube.full ∈ ({Subcube.full} : Finset (Subcube 2)) := by simp
  simpa using
    Cover2.mu_union_triple_succ_le
      (n := 2) (F := {f}) (R₁ := (∅ : Finset (Subcube 2)))
      (R₂ := {Subcube.full}) (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩) (p₃ := ⟨f, x₃⟩)
      hp₁ hp₂ hp₃ hx₁R hx₂R hx₃R hne₁₂ hne₁₃ hne₂₃ hmem

/-- `mu_union_triple_lt` gives the strict inequality for the same setup. -/
example :
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 ((∅ : Finset (Subcube 2)) ∪ {Subcube.full}) <
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 (∅ : Finset (Subcube 2)) := by
  classical
  -- Reuse the witnesses from the previous example.
  let f : BFunc 2 := fun _ => true
  let x₁ : Point 2 := fun _ => true
  let x₂ : Point 2 := fun
    | 0 => false
    | 1 => true
  let x₃ : Point 2 := fun
    | 0 => true
    | 1 => false
  have hf : f ∈ ({f} : BoolFunc.Family 2) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hx₃val : f x₃ = true := by simp [f, x₃]
  have hnc₁ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₂ :=
    by intro R hR; cases hR
  have hnc₃ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₃ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₂val, hnc₂⟩
  have hp₃ : ⟨f, x₃⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₃val, hnc₃⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hx₃R : x₃ ∈ₛ Subcube.full := by simp [x₃]
  have hne₁₂ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₂⟩ := by
    intro h
    have hx : x₁ = x₂ := congrArg Sigma.snd h
    have hx0 : x₁ 0 = x₂ 0 := congrArg (fun g => g 0) hx
    simp [x₁, x₂] at hx0
  have hne₁₃ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₁ = x₃ := congrArg Sigma.snd h
    have hx0 : x₁ 1 = x₃ 1 := congrArg (fun g => g 1) hx
    simp [x₁, x₃] at hx0
  have hne₂₃ : (⟨f, x₂⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₂ = x₃ := congrArg Sigma.snd h
    have hx0 : x₂ 0 = x₃ 0 := congrArg (fun g => g 0) hx
    simp [x₂, x₃] at hx0
  have hmem : Subcube.full ∈ ({Subcube.full} : Finset (Subcube 2)) := by simp
  simpa using
    Cover2.mu_union_triple_lt
      (n := 2) (F := {f}) (R₁ := (∅ : Finset (Subcube 2)))
      (R₂ := {Subcube.full}) (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩) (p₃ := ⟨f, x₃⟩)
      hp₁ hp₂ hp₃ hx₁R hx₂R hx₃R hne₁₂ hne₁₃ hne₂₃ hmem

/-- `mu_mono_subset` expresses that enlarging the set of rectangles can only
decrease the measure.  We test it on a simple pair of sets. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 {Subcube.full} ≤
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  let Fset : BoolFunc.Family 1 := {(fun _ : Point 1 => true)}
  have hsub : (∅ : Finset (Subcube 1)) ⊆ {Subcube.full} := by
    intro R hR; cases hR
  simpa using
    Cover2.mu_mono_subset
      (F := Fset)
      (R₁ := (∅ : Finset (Subcube 1)))
      (R₂ := {Subcube.full})
      (h := 0)
      (n := 1)
      hsub

/-- `mu_union_singleton_triple_succ_le` ensures a drop of at least three when
three distinct pairs are covered. -/
example :
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 ((∅ : Finset (Subcube 2)) ∪ {Subcube.full}) + 3 ≤
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 (∅ : Finset (Subcube 2)) := by
  classical
  -- Three uncovered inputs for the constant-true function.
  let f : BFunc 2 := fun _ => true
  let x₁ : Point 2 := fun _ => true
  let x₂ : Point 2 := fun
    | 0 => false
    | 1 => true
  let x₃ : Point 2 := fun
    | 0 => true
    | 1 => false
  have hf : f ∈ ({f} : BoolFunc.Family 2) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hx₃val : f x₃ = true := by simp [f, x₃]
  have hnc₁ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₂ :=
    by intro R hR; cases hR
  have hnc₃ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₃ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₂val, hnc₂⟩
  have hp₃ : ⟨f, x₃⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₃val, hnc₃⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hx₃R : x₃ ∈ₛ Subcube.full := by simp [x₃]
  have hne₁₂ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₂⟩ := by
    intro h
    have hx : x₁ = x₂ := congrArg Sigma.snd h
    have hx0 : x₁ 0 = x₂ 0 := congrArg (fun g => g 0) hx
    simp [x₁, x₂] at hx0
  have hne₁₃ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₁ = x₃ := congrArg Sigma.snd h
    have hx0 : x₁ 1 = x₃ 1 := congrArg (fun g => g 1) hx
    simp [x₁, x₃] at hx0
  have hne₂₃ : (⟨f, x₂⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₂ = x₃ := congrArg Sigma.snd h
    have hx0 : x₂ 0 = x₃ 0 := congrArg (fun g => g 0) hx
    simp [x₂, x₃] at hx0
  simpa using
    Cover2.mu_union_singleton_triple_succ_le
      (n := 2) (F := {f}) (Rset := (∅ : Finset (Subcube 2)))
      (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩) (p₃ := ⟨f, x₃⟩)
      hp₁ hp₂ hp₃ hx₁R hx₂R hx₃R hne₁₂ hne₁₃ hne₂₃

/-- `mu_union_singleton_triple_lt` specialises the strict inequality to three
distinct uncovered pairs. -/
example :
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 ((∅ : Finset (Subcube 2)) ∪ {Subcube.full}) <
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 (∅ : Finset (Subcube 2)) := by
  classical
  -- Three uncovered inputs for the constant-true function.
  let f : BFunc 2 := fun _ => true
  let x₁ : Point 2 := fun _ => true
  let x₂ : Point 2 := fun
    | 0 => false
    | 1 => true
  let x₃ : Point 2 := fun
    | 0 => true
    | 1 => false
  have hf : f ∈ ({f} : BoolFunc.Family 2) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hx₃val : f x₃ = true := by simp [f, x₃]
  have hnc₁ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₂ :=
    by intro R hR; cases hR
  have hnc₃ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₃ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₂val, hnc₂⟩
  have hp₃ : ⟨f, x₃⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₃val, hnc₃⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hx₃R : x₃ ∈ₛ Subcube.full := by simp [x₃]
  have hne₁₂ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₂⟩ := by
    intro h
    have hx : x₁ = x₂ := congrArg Sigma.snd h
    have hx0 : x₁ 0 = x₂ 0 := congrArg (fun g => g 0) hx
    simp [x₁, x₂] at hx0
  have hne₁₃ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₁ = x₃ := congrArg Sigma.snd h
    have hx0 : x₁ 1 = x₃ 1 := congrArg (fun g => g 1) hx
    simp [x₁, x₃] at hx0
  have hne₂₃ : (⟨f, x₂⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₂ = x₃ := congrArg Sigma.snd h
    have hx0 : x₂ 0 = x₃ 0 := congrArg (fun g => g 0) hx
    simp [x₂, x₃] at hx0
  simpa using
    Cover2.mu_union_singleton_triple_lt
      (n := 2) (F := {f}) (Rset := (∅ : Finset (Subcube 2)))
      (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩) (p₃ := ⟨f, x₃⟩)
      hp₁ hp₂ hp₃ hx₁R hx₂R hx₃R hne₁₂ hne₁₃ hne₂₃

/-- `mu_union_singleton_quad_succ_le` ensures a drop of at least four when
four distinct pairs are covered. -/
example :
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 ((∅ : Finset (Subcube 2)) ∪ {Subcube.full}) + 4 ≤
    Cover2.mu (n := 2)
        ({(fun _ : Point 2 => true)} : BoolFunc.Family 2)
        0 (∅ : Finset (Subcube 2)) := by
  classical
  -- Four uncovered inputs for the constant-true function.
  let f : BFunc 2 := fun _ => true
  let x₁ : Point 2 := fun _ => true
  let x₂ : Point 2 := fun
    | 0 => false
    | 1 => true
  let x₃ : Point 2 := fun
    | 0 => true
    | 1 => false
  let x₄ : Point 2 := fun _ => false
  have hf : f ∈ ({f} : BoolFunc.Family 2) := by simp
  have hx₁val : f x₁ = true := by simp [f, x₁]
  have hx₂val : f x₂ = true := by simp [f, x₂]
  have hx₃val : f x₃ = true := by simp [f, x₃]
  have hx₄val : f x₄ = true := by simp [f, x₄]
  have hnc₁ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₁ :=
    by intro R hR; cases hR
  have hnc₂ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₂ :=
    by intro R hR; cases hR
  have hnc₃ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₃ :=
    by intro R hR; cases hR
  have hnc₄ : Cover2.NotCovered (n := 2) (Rset := (∅ : Finset (Subcube 2))) x₄ :=
    by intro R hR; cases hR
  have hp₁ : ⟨f, x₁⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₁val, hnc₁⟩
  have hp₂ : ⟨f, x₂⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₂val, hnc₂⟩
  have hp₃ : ⟨f, x₃⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₃val, hnc₃⟩
  have hp₄ : ⟨f, x₄⟩ ∈ Cover2.uncovered (n := 2) ({f} : BoolFunc.Family 2)
        (∅ : Finset (Subcube 2)) := ⟨hf, hx₄val, hnc₄⟩
  have hx₁R : x₁ ∈ₛ Subcube.full := by simp [x₁]
  have hx₂R : x₂ ∈ₛ Subcube.full := by simp [x₂]
  have hx₃R : x₃ ∈ₛ Subcube.full := by simp [x₃]
  have hx₄R : x₄ ∈ₛ Subcube.full := by simp [x₄]
  have hne₁₂ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₂⟩ := by
    intro h
    have hx : x₁ = x₂ := congrArg Sigma.snd h
    have hx0 : x₁ 0 = x₂ 0 := congrArg (fun g => g 0) hx
    simp [x₁, x₂] at hx0
  have hne₁₃ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₁ = x₃ := congrArg Sigma.snd h
    have hx0 : x₁ 1 = x₃ 1 := congrArg (fun g => g 1) hx
    simp [x₁, x₃] at hx0
  have hne₁₄ : (⟨f, x₁⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₄⟩ := by
    intro h
    have hx : x₁ = x₄ := congrArg Sigma.snd h
    have hx0 : x₁ 0 = x₄ 0 := congrArg (fun g => g 0) hx
    simp [x₁, x₄] at hx0
  have hne₂₃ : (⟨f, x₂⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₃⟩ := by
    intro h
    have hx : x₂ = x₃ := congrArg Sigma.snd h
    have hx0 : x₂ 0 = x₃ 0 := congrArg (fun g => g 0) hx
    simp [x₂, x₃] at hx0
  have hne₂₄ : (⟨f, x₂⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₄⟩ := by
    intro h
    have hx : x₂ = x₄ := congrArg Sigma.snd h
    have hx1 : x₂ 1 = x₄ 1 := congrArg (fun g => g 1) hx
    simp [x₂, x₄] at hx1
  have hne₃₄ : (⟨f, x₃⟩ : Σ g : BFunc 2, Point 2) ≠ ⟨f, x₄⟩ := by
    intro h
    have hx : x₃ = x₄ := congrArg Sigma.snd h
    have hx0 : x₃ 0 = x₄ 0 := congrArg (fun g => g 0) hx
    simp [x₃, x₄] at hx0
  simpa using
    Cover2.mu_union_singleton_quad_succ_le
      (n := 2) (F := {f}) (Rset := (∅ : Finset (Subcube 2)))
      (R := Subcube.full) (h := 0)
      (p₁ := ⟨f, x₁⟩) (p₂ := ⟨f, x₂⟩) (p₃ := ⟨f, x₃⟩) (p₄ := ⟨f, x₄⟩)
      hp₁ hp₂ hp₃ hp₄ hx₁R hx₂R hx₃R hx₄R
      hne₁₂ hne₁₃ hne₁₄ hne₂₃ hne₂₄ hne₃₄

end Cover2Test

