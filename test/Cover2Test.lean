import Pnp2.cover2
import Pnp2.Cover.Canonical
import Pnp2.BoolFunc

open Boolcube (Point Subcube)
open BoolFunc (BFunc Family)
open Classical

-- Tests often use `simpa` for readability; suppress related lint warnings.
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Cover2

namespace Cover2Test

/-- `mBound` is computed via the wrapper definition. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- `mBound` is nonnegative for all inputs. -/
example : 0 ≤ mBound 1 0 := by
  exact Cover2.mBound_nonneg (n := 1) (h := 0)

/-- Numeric bound specialised to trivial parameters using the positive version. -/
  example : 2 * 0 + 1 ≤ mBound 1 0 := by
    have hn : 0 < (1 : ℕ) := by decide
    -- Apply the numeric bound directly.
    exact numeric_bound_pos (n := 1) (h := 0) hn

/-- `numeric_bound_pos` also holds when `n` is strictly positive. -/
  example : 2 * 0 + 2 ≤ mBound 2 0 := by
    have hn : 0 < (2 : ℕ) := by decide
    -- Again we apply the lemma directly.
    exact numeric_bound_pos (n := 2) (h := 0) hn

/-- Doubling the bound for a smaller budget stays below the next budget. -/
  example : 2 * mBound 1 0 ≤ mBound 1 1 := by
    -- The statement matches `two_mul_mBound_le_succ` exactly.
    exact two_mul_mBound_le_succ (n := 1) (h := 0)

/-- `pow_le_mBound_simple` for trivial parameters. -/
example : 1 ≤ mBound 1 0 := by
    have hn : 0 < (1 : ℕ) := by decide
    -- Use the lemma directly instead of a `simp` rewrite.
    exact pow_le_mBound_simple (n := 1) (h := 0) hn

/-- Freezing a coordinate with `fromPoint` fixes membership. -/
example :
    (Subcube.fromPoint (n := 1) (fun _ : Fin 1 => true) (∅ : Finset (Fin 1))).Mem
      (fun _ : Fin 1 => true) := by
  simp [Subcube.fromPoint]


/-- `two_le_mBound` verifies the bound is at least `2`. -/
  example : 2 ≤ mBound 1 0 := by
    have hn : 0 < (1 : ℕ) := by decide
    -- Applying `two_le_mBound` directly avoids an unused `simp` argument warning.
    exact two_le_mBound (n := 1) (h := 0) hn

/-- Doubling the bound for `h = 0` stays below the next budget. -/
  example : 2 * mBound 1 0 ≤ mBound 1 1 := by
    -- As before, use the lemma directly.
    exact two_mul_mBound_le_succ (n := 1) (h := 0)

/-- Inserting a single rectangle stays within the next budget. -/
example :
    (insert Subcube.full (∅ : Finset (Subcube 1))).card ≤ mBound 1 1 := by
  classical
  have hcard : ( (∅ : Finset (Subcube 1)).card ) ≤ mBound 1 0 := by
    simp [mBound]
  have hn : 0 < (1 : ℕ) := by decide
  -- The goal matches the lemma exactly, so we can use it directly
  exact
    (card_insert_mBound_succ (n := 1) (h := 0)
      (Rset := (∅ : Finset (Subcube 1))) (R := Subcube.full)
      hcard hn)

/-- Nothing is covered by an empty set of rectangles. -/
example (x : Point 1) :
    Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
  -- Use the lemma directly instead of `simpa`
  exact Cover2.notCovered_empty (n := 1) (x := x)

/-- `NotCovered` is monotone under set inclusion. -/
example (x : Point 1) (R : Subcube 1)
    (hx : Cover2.NotCovered (n := 1) (Rset := {R}) x) :
    Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
  have hsub : (∅ : Finset (Subcube 1)) ⊆ {R} := by
    intro r hr; cases hr
  -- Again the statement coincides with the lemma, so apply it directly
  exact
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
    -- `Finset.mem_insert` is redundant here; removing it avoids an unused simp argument
    simp [Finset.mem_singleton] at hR
    simp [Finset.mem_singleton, hR]
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
    -- Apply the union lemma directly
    exact
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
    -- The goal is exactly the statement of `AllOnesCovered.insert`
    exact
      Cover2.AllOnesCovered.insert (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := {Subcube.full}) (R := Subcube.full) hcov

/-- Coverage by an empty set of rectangles is equivalent to the absence of
`1`‑inputs in the family. -/
  example :
      Cover2.AllOnesCovered (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) ↔
      ∀ f ∈ ({(fun _ : Point 1 => true)} : BoolFunc.Family 1),
          ∀ x, f x = true → False := by
    -- Use the equivalence lemma directly
    exact
      (Cover2.AllOnesCovered.empty
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)))

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

/-- The uncovered set shrinks when enlarging the rectangle collection. -/
example (R₁ R₂ : Finset (Subcube 1))
    (hsub : R₁ ⊆ R₂) :
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) R₂ ⊆
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) R₁ := by
  classical
  exact
    Cover2.uncovered_subset
      (n := 1)
      (F := {(fun _ : Point 1 => true)})
      (R₁ := R₁) (R₂ := R₂) hsub

/-- The coarse cardinality bound on uncovered pairs. -/
example :
    (Cover2.uncovered (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1))).toFinset.card ≤
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1).card * 2 ^ 1 := by
  classical
  simpa using
    Cover2.uncovered_card_bound
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1)))

/-- Coarse bound specialised to the initial uncovered set. -/
example :
    (Cover2.uncovered (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1))).toFinset.card ≤
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1).card * 2 ^ 1 := by
  classical
  simpa using
    (Cover2.uncovered_init_coarse_bound
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)))

/-- If the family is empty, the initial uncovered set is empty as well. -/
example :
    (Cover2.uncovered (n := 1) (∅ : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1))).toFinset.card ≤ 1 := by
  -- Direct application of the bound for the empty family
  exact
    Cover2.uncovered_init_bound_empty
      (n := 1) (F := (∅ : BoolFunc.Family 1)) (hF := rfl)

/-- `firstUncovered` returns `none` precisely when the uncovered set is empty. -/
example :
    Cover2.firstUncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) = none ↔
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) =
        (∅ : Set (Sigma (fun _ => Point 1))) := by
  -- Apply the characterisation of `firstUncovered` directly
  exact
    (Cover2.firstUncovered_none_iff
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (R := (∅ : Finset (Subcube 1))))

/-- `firstUncovered` returns `none` exactly when every `1`‑input is covered. -/
example :
    Cover2.firstUncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) = none ↔
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) := by
  -- The dedicated lemma proves the equivalence directly.
  exact
    (Cover2.firstUncovered_none_iff_AllOnesCovered
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := ({Subcube.full} : Finset (Subcube 1))))

/-- If `firstUncovered` yields a witness, that witness lies in the uncovered set. -/
example (F : BoolFunc.Family 1) (R : Finset (Subcube 1))
    {p : Sigma (fun _ => Point 1)}
    (hp : Cover2.firstUncovered (n := 1) F R = some p) :
    p ∈ Cover2.uncovered (n := 1) F R :=
  Cover2.mem_uncovered_of_firstUncovered_some (n := 1) (F := F) (R := R) hp

/-- Two-bit `AND` and `OR` functions forming a tiny family. -/
def and2 : BoolFunc.BFunc 2 :=
  fun x => x ⟨0, by decide⟩ && x ⟨1, by decide⟩

def or2 : BoolFunc.BFunc 2 :=
  fun x => x ⟨0, by decide⟩ || x ⟨1, by decide⟩

/-- Family containing only `and2`, used for the coverage tests below. -/
def F₂ : BoolFunc.Family 2 := ({and2} : Finset (BoolFunc.BFunc 2))

/-- Point with both coordinates set to `true`. -/
def x11 : Boolcube.Point 2 := fun _ => true

/-- With no rectangles, `firstUncovered` finds a witness. -/
example :
    Cover2.firstUncovered (n := 2) F₂ (∅ : Finset (Boolcube.Subcube 2)) ≠ none := by
  classical
  intro hnone
  have hcov :=
    (Cover2.firstUncovered_none_iff_AllOnesCovered
      (n := 2) (F := F₂) (Rset := (∅ : Finset (Boolcube.Subcube 2)))).1 hnone
  have hf : and2 ∈ F₂ := by simp [F₂]
  have hx : and2 x11 = true := by
    simp [and2, x11]
  have hcontr := hcov and2 hf x11 hx
  rcases hcontr with ⟨R, hR, _⟩
  simpa using hR

/-- Covering the uncovered point removes all witnesses. -/
example :
    Cover2.firstUncovered (n := 2) F₂
        ({Boolcube.Subcube.point (n := 2) x11} : Finset (Boolcube.Subcube 2)) =
      none := by
  classical
  have hcov : Cover2.AllOnesCovered (n := 2) F₂
      ({Boolcube.Subcube.point (n := 2) x11} : Finset (Boolcube.Subcube 2)) := by
    intro f hf x hx
    have hf' : f = and2 := by simpa [F₂] using hf
    subst hf'
    have hx_bits :
        x ⟨0, by decide⟩ = true ∧ x ⟨1, by decide⟩ = true := by
      simpa [and2] using hx
    have hx_eq : x = x11 := by
      ext i
      fin_cases i
      · simpa [x11] using hx_bits.1
      · simpa [x11] using hx_bits.2
    subst hx_eq
    refine ⟨Boolcube.Subcube.point (n := 2) x11, by simp, ?_⟩
    simp
  exact
    (Cover2.firstUncovered_none_iff_AllOnesCovered
      (n := 2) (F := F₂)
      (Rset := {Boolcube.Subcube.point (n := 2) x11})).2 hcov

/-- If `firstUncovered` returns `none`, all `1`‑inputs are covered. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) := by
  classical
  -- The uncovered set is empty since the function has no `1`-inputs.
  have hcov : Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) := by
    -- Use the lemma; `simpa` handles the trivial right-hand side
    simpa using
      (Cover2.AllOnesCovered.empty
        (n := 1)
        (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)))
  have huncov : Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) =
      (∅ : Set (Sigma (fun _ => Point 1))) :=
    Cover2.uncovered_eq_empty_of_allCovered
      (n := 1) (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1))) hcov
  have hfu :
      Cover2.firstUncovered (n := 1)
        ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) = none := by
    exact
      (Cover2.firstUncovered_none_iff
        (n := 1)
        (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
        (R := (∅ : Finset (Subcube 1)))).2 huncov
  -- Invoke the main lemma directly.
  exact
    (Cover2.allOnesCovered_of_firstUncovered_none
      (n := 1)
      (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1))) hfu)

/-- If all `1`-inputs are covered, the measure collapses to `2 * h`. -/
example :
    Cover2.mu (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      0 ({Subcube.full} : Finset (Subcube 1)) = 2 * 0 := by
  have hcov : Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) :=
    Cover2.AllOnesCovered.full _
  -- Apply the lemma directly without `simpa`
  exact
    Cover2.mu_of_allCovered
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := ({Subcube.full} : Finset (Subcube 1)))
      (h := 0) hcov

/-- `allOnesCovered_of_mu_eq` infers coverage from a collapsed measure. -/
example :
    Cover2.AllOnesCovered (n := 1)
      (F := (∅ : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1))) := by
  have hmu :
      Cover2.mu (n := 1)
        (F := (∅ : BoolFunc.Family 1))
        0 (Rset := (∅ : Finset (Subcube 1))) = 2 * 0 := by
    simp [Cover2.mu, Cover2.uncovered, Cover2.NotCovered]
  -- Invoke the converse lemma directly
  exact
    Cover2.allOnesCovered_of_mu_eq
      (n := 1)
      (F := (∅ : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1)))
      (h := 0) hmu

/-- `μ` is nonnegative by construction. -/
  example :
      0 ≤ Cover2.mu (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          0 (∅ : Finset (Subcube 1)) := by
    -- Nonnegativity follows directly from the lemma `mu_nonneg`
    exact
      Cover2.mu_nonneg
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1))) (h := 0)

/-- `μ` always dominates the entropy budget. -/
  example :
      2 * 0 ≤ Cover2.mu (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          0 (∅ : Finset (Subcube 1)) := by
    -- Apply the lower bound lemma directly
    exact
      Cover2.mu_lower_bound
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1))) (h := 0)

/-- Increasing the entropy budget can only increase `μ`. -/
  example :
      Cover2.mu (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          0 (∅ : Finset (Subcube 1)) ≤
      Cover2.mu (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          1 (∅ : Finset (Subcube 1)) := by
    -- Monotonicity in the entropy budget
    exact
      Cover2.mu_mono_h
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1)))
        (h₁ := 0) (h₂ := 1) (by decide)

/-- Inserting a rectangle never increases the measure `mu`. -/
  example :
      Cover2.mu (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) ≤
      Cover2.mu (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          0 (∅ : Finset (Subcube 1)) := by
    classical
    -- Direct application of the measure monotonicity lemma
    exact
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

/-- `mu_union_lt` strictly decreases the measure when a rectangle from `R₂`
covers an uncovered pair of `R₁`. -/
example :
    Cover2.mu (n := 1)
        ({(fun x : Point 1 => x 0)} : BoolFunc.Family 1)
        0 ((∅ : Finset (Subcube 1)) ∪ {Subcube.full}) <
    Cover2.mu (n := 1)
        ({(fun x : Point 1 => x 0)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- A single uncovered input for the projection function.
  let f : BFunc 1 := fun x => x 0
  let x : Point 1 := fun _ => true
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hxval : f x = true := by simp [f, x]
  have hnc : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
    intro R hR; cases hR
  have hx :
      ∃ p, p ∈ Cover2.uncovered (n := 1) ({f} : BoolFunc.Family 1)
            (∅ : Finset (Subcube 1)) ∧
          ∃ R, R ∈ ({Subcube.full (n := 1)} : Finset (Subcube 1)) ∧
            Boolcube.Subcube.Mem R (p.2) := by
    refine ⟨⟨f, x⟩, ?_, ?_⟩
    · exact ⟨hf, hxval, hnc⟩
    · refine ⟨Subcube.full (n := 1), ?_, ?_⟩
      · simp
      · simp [x]
  simpa using
    Cover2.mu_union_lt
      (n := 1) (F := {f})
      (R₁ := (∅ : Finset (Subcube 1)))
      (R₂ := {Subcube.full}) (h := 0) hx

/-- `mu_gt_of_firstUncovered_some` detects progress when an uncovered pair exists. -/
example :
    2 * 0 < Cover2.mu (n := 1)
        ({(fun x : Point 1 => x 0)} : BoolFunc.Family 1)
        0 (∅ : Finset (Subcube 1)) := by
  classical
  -- The projection function has the point `x` with value `1` uncovered.
  let f : BFunc 1 := fun x => x 0
  let x : Point 1 := fun _ => true
  have hf : f ∈ ({f} : BoolFunc.Family 1) := by simp
  have hxval : f x = true := by simp [f, x]
  have hnc : Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
    intro R hR; cases hR
  have hx : (Cover2.uncovered (n := 1) {f} (∅ : Finset (Subcube 1))).Nonempty :=
    ⟨⟨f, x⟩, ⟨hf, hxval, hnc⟩⟩
  have hfu : Cover2.firstUncovered (n := 1) {f} (∅ : Finset (Subcube 1)) ≠ none := by
    intro hnone
    have hxne :
        Cover2.uncovered (n := 1) {f} (∅ : Finset (Subcube 1)) ≠
          (∅ : Set (Sigma (fun _ : BFunc 1 => Point 1))) :=
      Set.nonempty_iff_ne_empty.mp hx
    have hempty :=
      (Cover2.firstUncovered_none_iff (n := 1) (F := {f})
        (R := (∅ : Finset (Subcube 1)))).1 hnone
    exact hxne hempty
  simpa using
    Cover2.mu_gt_of_firstUncovered_some
      (n := 1) (F := {f}) (Rset := (∅ : Finset (Subcube 1))) (h := 0) hfu

/-- If `firstUncovered` returns `none`, the measure collapses to `2 * h`. -/
example :
    Cover2.mu (n := 1) (F := (∅ : BoolFunc.Family 1)) 0
        (∅ : Finset (Subcube 1)) = 0 := by
  classical
  -- With an empty family the uncovered set is empty.
  have hempty :
      Cover2.uncovered (n := 1) (F := (∅ : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1))) =
        (∅ : Set (Sigma fun _ : BFunc 1 => Point 1)) := by
    ext p; constructor
    · intro hp; cases hp.1
    · intro hp; cases hp
  -- Hence `firstUncovered` yields `none`.
  have hfu : Cover2.firstUncovered (n := 1)
      (F := (∅ : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1))) = none :=
    (Cover2.firstUncovered_none_iff (n := 1)
        (F := (∅ : BoolFunc.Family 1))
        (R := (∅ : Finset (Subcube 1)))).2 hempty
  -- Applying the lemma collapses `μ` to `2 * h`.
  simpa using
    (Cover2.mu_of_firstUncovered_none (n := 1)
        (F := (∅ : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1)))
        (h := 0) hfu)

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

/-/ A single full rectangle still respects the universal cover bound. -/
/-- `extendCover` inserts the full subcube for a constant-`true` family. -/
example :
    extendCover (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) =
    {Subcube.full} := by
  classical
  -- Exhibit an uncovered witness pair to show that `firstUncovered` is `some _`.
  let f : BFunc 1 := fun _ => true
  let x : Point 1 := fun _ => false
  have hf : f ∈ ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) := by
    simp [f]
  have hxval : f x = true := by simp [f, x]
  have hnc : Cover2.NotCovered (n := 1)
      (Rset := (∅ : Finset (Subcube 1))) x := by
    intro R hR; cases hR
  have hcov_false : ¬ Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (∅ : Finset (Subcube 1)) := by
    intro hcov
    have hcontr := hcov f hf x hxval
    rcases hcontr with ⟨R, hR, _⟩
    simpa using hR
  have hfu_ne :
      Cover2.firstUncovered (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          (∅ : Finset (Subcube 1)) ≠ none := by
    intro hnone
    have hcov :=
      (Cover2.firstUncovered_none_iff_AllOnesCovered
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1)))).1 hnone
    exact hcov_false hcov
  -- Evaluate `extendCover` in the successful branch.
  cases hfu :
      Cover2.firstUncovered (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) with
  | none => cases (hfu_ne hfu)
  | some p =>
      -- The coordinate filter is empty, yielding the full subcube.
      -- `supportUnion` for the constant-`true` family is empty.
      have hsup : Cover2.supportUnion
          (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)) =
          (∅ : Finset (Fin 1)) := by
        ext i; simp [Cover2.supportUnion]
      simp [Cover2.extendCover, hfu, hsup, Boolcube.Subcube.fromPoint,
        Boolcube.Subcube.full]

/-- When all `1`‑inputs are already covered, `extendCover` is the identity. -/
example :
    extendCover (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
        ({Subcube.full} : Finset (Subcube 1)) =
    {Subcube.full} := by
  classical
  have hcov : Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) :=
    Cover2.AllOnesCovered.full _
  have hfu :
      Cover2.firstUncovered (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          ({Subcube.full} : Finset (Subcube 1)) = none := by
    simpa using
      (Cover2.firstUncovered_none_iff_AllOnesCovered
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := ({Subcube.full} : Finset (Subcube 1)))).2 hcov
  simpa using
    (Cover2.extendCover_none
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := ({Subcube.full} : Finset (Subcube 1))) hfu)

/-- `extendCover` never increases the termination measure `μ`. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) 0
        (extendCover (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          (∅ : Finset (Subcube 1))) ≤
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) 0
        (∅ : Finset (Subcube 1)) := by
  classical
  simpa using
      Cover2.mu_extendCover_le
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1))) (h := 0)

/-- If an uncovered pair exists, `extendCover` strictly decreases the
termination measure `μ`. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) 0
        (extendCover (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          (∅ : Finset (Subcube 1))) <
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) 0
        (∅ : Finset (Subcube 1)) := by
  classical
  -- Show that `firstUncovered` actually finds a witness pair.
  have hfu_ne :
      Cover2.firstUncovered (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          (∅ : Finset (Subcube 1)) ≠ none := by
    -- The constant-`true` function evaluated at `x` remains uncovered.
    let f : BFunc 1 := fun _ => true
    let x : Point 1 := fun _ => false
    have hf : f ∈ ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) := by
      simp [f]
    have hxval : f x = true := by simp [f, x]
    intro hnone
    -- From `firstUncovered = none` we obtain full coverage, contradicting `x`.
    have hcov :=
      (Cover2.firstUncovered_none_iff_AllOnesCovered
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1)))).1 hnone
    have hcontr := hcov f hf x hxval
    rcases hcontr with ⟨R, hR, _⟩
    simpa using hR
  -- Apply the strict decrease lemma.
  simpa using
    Cover2.mu_extendCover_lt
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1))) (h := 0) hfu_ne

/-- Running `buildCover` strictly reduces the measure for the simple
singleton family consisting of the constant-`true` function.  This mirrors the
behaviour of `extendCover` since `buildCover` currently performs exactly one
covering step. -/
example :
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) 0
        (Cover2.buildCover (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          (h := 0)
          (by
            -- Collision entropy of a singleton family is zero.
            have hcard : ({(fun _ : Point 1 => true)} : BoolFunc.Family 1).card = 1 := by
              simp
            have hH₂ := BoolFunc.H₂_card_one
                (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)) hcard
            simpa [hH₂]))
        <
    Cover2.mu (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) 0
        (∅ : Finset (Subcube 1)) := by
  classical
  -- `firstUncovered` locates an uncovered witness pair as in the previous test.
  have hfu_ne :
      Cover2.firstUncovered (n := 1)
          ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
          (∅ : Finset (Subcube 1)) ≠ none := by
    -- The constant-`true` function evaluated at `x` remains uncovered.
    let f : BFunc 1 := fun _ => true
    let x : Point 1 := fun _ => false
    have hf : f ∈ ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) := by
      simp [f]
    have hxval : f x = true := by simp [f, x]
    intro hnone
    -- From `firstUncovered = none` we obtain full coverage, contradicting `x`.
    have hcov :=
      (Cover2.firstUncovered_none_iff_AllOnesCovered
        (n := 1)
        (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1)))).1 hnone
    have hcontr := hcov f hf x hxval
    rcases hcontr with ⟨R, hR, _⟩
    simpa using hR
  -- Apply the strict decrease lemma for a single extension step.
  have hdrop :=
    Cover2.mu_extendCover_lt
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := (∅ : Finset (Subcube 1)))
      (h := 0) hfu_ne
  simpa using hdrop

/-- When `firstUncovered` fails to find a witness, `buildCoverAux` returns the
input rectangle set unchanged.  We verify this behaviour for the trivial
constant-`false` family, where no `1`-inputs exist. -/
example :
    Cover2.buildCoverAux (n := 1)
        (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
        (h := 0)
        (by
          -- Entropy of a singleton family is `0`.
          have hcard : ({(fun _ : Point 1 => false)} : BoolFunc.Family 1).card = 1 := by
            simp
          have hH₂ := BoolFunc.H₂_card_one
              (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)) hcard
          simpa [hH₂])
        (∅ : Finset (Subcube 1))
      = (∅ : Finset (Subcube 1)) := by
  classical
  -- The family has no `1`-inputs, hence the uncovered set is empty.
  have hfu :
      Cover2.firstUncovered (n := 1)
        ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)
        (∅ : Finset (Subcube 1)) = none := by
    -- Coverage by the empty rectangle set holds trivially.
    have hcov :
        Cover2.AllOnesCovered (n := 1)
          ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)
          (∅ : Finset (Subcube 1)) := by
      simpa using
        (Cover2.AllOnesCovered.empty
          (n := 1)
          (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)))
    -- Translate coverage into absence of witnesses.
    exact
      (Cover2.firstUncovered_none_iff_AllOnesCovered
        (n := 1)
        (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
        (Rset := (∅ : Finset (Subcube 1)))).2 hcov
  -- Apply the unfolding lemma.
  simpa using
    Cover2.buildCoverAux_none
      (n := 1)
      (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
      (h := 0)
      (hH := by
        have hcard : ({(fun _ : Point 1 => false)} : BoolFunc.Family 1).card = 1 := by
          simp
        have hH₂ := BoolFunc.H₂_card_one
            (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)) hcard
        simpa [hH₂])
      (Rset := (∅ : Finset (Subcube 1)))
      hfu

/-- The rectangles produced by `buildCover` are pointwise monochromatic for a
constant-`true` family. -/
example :
    ∀ R ∈ Cover2.buildCover (n := 1)
        ({(fun _ : Point 1 => true)} : BoolFunc.Family 1) (h := 0)
        (by
          -- Collision entropy of a singleton family is `0`.
          have hcard : ({(fun _ : Point 1 => true)} : BoolFunc.Family 1).card = 1 := by
            simp
          have hH₂ := BoolFunc.H₂_card_one
              (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)) hcard
          simpa [hH₂]) ,
      ∀ g ∈ ({(fun _ : Point 1 => true)} : BoolFunc.Family 1),
        Boolcube.Subcube.monochromaticFor R g := by
  classical
  intro R hR g hg
  -- Invoke the pointwise monochromaticity lemma for `buildCover`.
  exact
    Cover2.buildCover_pointwiseMono
      (n := 1)
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (h := 0)
      (hH :=
        by
          have hcard : ({(fun _ : Point 1 => true)} : BoolFunc.Family 1).card = 1 := by
            simp
          have hH₂ := BoolFunc.H₂_card_one
              (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)) hcard
          simpa [hH₂])
      R hR g hg

/-- For a constant-`false` family the cover is empty and trivially pointwise
monochromatic. -/
example :
    ∀ R ∈ Cover2.buildCover (n := 1)
        ({(fun _ : Point 1 => false)} : BoolFunc.Family 1) (h := 0)
        (by
          -- The collision entropy is again `0` for the singleton family.
          have hcard : ({(fun _ : Point 1 => false)} : BoolFunc.Family 1).card = 1 := by
            simp
          have hH₂ := BoolFunc.H₂_card_one
              (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)) hcard
          simpa [hH₂]) ,
      ∀ g ∈ ({(fun _ : Point 1 => false)} : BoolFunc.Family 1),
        Boolcube.Subcube.monochromaticFor R g := by
  classical
  intro R hR g hg
  -- The result set is empty, hence the property holds vacuously.
  exact
    Cover2.buildCover_pointwiseMono
      (n := 1)
      (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1))
      (h := 0)
      (hH :=
        by
          have hcard : ({(fun _ : Point 1 => false)} : BoolFunc.Family 1).card = 1 := by
            simp
          have hH₂ := BoolFunc.H₂_card_one
              (F := ({(fun _ : Point 1 => false)} : BoolFunc.Family 1)) hcard
          simpa [hH₂])
      R hR g hg

