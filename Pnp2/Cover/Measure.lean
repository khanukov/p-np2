import Pnp2.Cover.Uncovered
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

-- Disable style linting that is not important for the measure machinery.
set_option linter.unnecessarySimpa false

namespace Cover2

/-!
### Termination measure

This file contains the definition of the simple measure `μ` used in the
covering construction.  The measure keeps track of two pieces of
information:

* the remaining entropy budget `h`, doubled to emphasise its numeric
  contribution, and
* the number of currently uncovered pairs of functions and points.

The combination `2 * h + #uncovered` decreases whenever we add rectangles
that cover new pairs.  The lemmas in this file provide a basic API for
reasoning about this measure in isolation from the rest of the cover
logic.
-/

variable {n h : ℕ} (F : Family n)

/--
The termination measure `μ`.  It consists of twice the entropy budget `h`
plus the cardinality of the set of uncovered pairs.

The measure is noncomputable because the set of uncovered pairs is defined
using choice to pick witnesses; nevertheless it suffices for reasoning
about termination and progress of the cover construction.
-/
noncomputable def mu (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) : ℕ :=
  2 * h + (uncovered (n := n) F Rset).toFinset.card

/-!
### Basic characterisations

The following lemmas connect `μ` with coverage properties of the rectangle
set.  They are frequently used to transition between statements about the
measure and statements about the uncovered set.
-/

/--
If all `1`‑inputs of `F` already lie inside some rectangle of `Rset`, then
the uncovered set is empty and the measure collapses to `2 * h`.
-/
lemma mu_of_allCovered {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
    (hcov : AllOnesCovered (n := n) F Rset) :
    mu (n := n) F h Rset = 2 * h := by
  classical
  -- Replace the uncovered set by `∅` using the coverage assumption.
  have hzero :
      uncovered (n := n) F Rset =
        (∅ : Set (Σ _ : BFunc n, Point n)) :=
    uncovered_eq_empty_of_allCovered
      (n := n) (F := F) (Rset := Rset) hcov
  -- Unfold `μ` and simplify using the empty uncovered set.
  calc
    mu (n := n) F h Rset
        = 2 * h + (uncovered (n := n) F Rset).toFinset.card := rfl
    _ = 2 * h + (∅ : Set (Σ _ : BFunc n, Point n)).toFinset.card := by
        -- Apply `congrArg` to rewrite the uncovered set using `hzero`.
        have := congrArg
          (fun s : Set (Σ _ : BFunc n, Point n) => 2 * h + s.toFinset.card)
          hzero
        simpa using this
    _ = 2 * h + 0 := by simp
    _ = 2 * h := by simp

/--
`firstUncovered` returns `none` exactly when all `1`‑inputs are covered.
In this case `μ` again collapses to `2 * h`.
-/
lemma mu_of_firstUncovered_none {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hfu : firstUncovered (n := n) F Rset = none) :
    mu (n := n) F h Rset = 2 * h := by
  have hcov : AllOnesCovered (n := n) F Rset :=
    allOnesCovered_of_firstUncovered_none (n := n) (F := F)
      (Rset := Rset) hfu
  simpa using
    (mu_of_allCovered (n := n) (F := F) (Rset := Rset) (h := h) hcov)

/--
Conversely, if the measure `μ` equals `2 * h`, then no uncovered pairs
remain.  Consequently all `1`‑inputs of `F` must already be covered by
`Rset`.
-/
lemma allOnesCovered_of_mu_eq {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hμ : mu (n := n) F h Rset = 2 * h) :
    AllOnesCovered (n := n) F Rset := by
  classical
  -- From the equality on `μ` we deduce that the uncovered set has
  -- cardinality `0`.
  have hμ' : 2 * h + (uncovered (n := n) F Rset).toFinset.card =
      2 * h + 0 := by
    simpa [mu] using hμ
  have hcard0 : (uncovered (n := n) F Rset).toFinset.card = 0 :=
    Nat.add_left_cancel hμ'
  -- Hence the uncovered set itself is empty.
  have hset : uncovered (n := n) F Rset =
      (∅ : Set (Σ _ : BFunc n, Point n)) := by
    classical
    -- Convert cardinality information into emptiness of the uncovered set.
    have hfin :
        (uncovered (n := n) F Rset).toFinset =
          (∅ : Finset (Σ _ : BFunc n, Point n)) :=
      Finset.card_eq_zero.mp hcard0
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    -- Membership in the set contradicts the finset being empty.
    have hpFin : p ∈ (uncovered (n := n) F Rset).toFinset :=
      Set.mem_toFinset.mpr hp
    -- Rewrite using `hfin` and derive a contradiction.
    rw [hfin] at hpFin
    cases hpFin
  -- Conclude by converting the empty uncovered set into coverage.
  have hfu : firstUncovered (n := n) F Rset = none :=
    (firstUncovered_none_iff (n := n) (F := F) (R := Rset)).2
      (by simpa using hset)
  exact allOnesCovered_of_firstUncovered_none
      (F := F) (Rset := Rset) hfu

/-!
### Numerical bounds and monotonicity

The next group of lemmas collects simple inequalities about `μ`.  They are
useful when arguing that a cover construction makes progress.
-/

/-- The measure is always nonnegative. -/
lemma mu_nonneg {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    0 ≤ mu (n := n) F h Rset := by
  -- Since `μ` is a natural number, nonnegativity is immediate.
  exact Nat.zero_le _

/-- Adding rectangles cannot decrease the `2 * h` part of the measure. -/
lemma mu_lower_bound {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    2 * h ≤ mu (n := n) F h Rset := by
  -- The uncovered cardinality is nonnegative, so `μ` is at least `2 * h`.
    -- `simp` proves the inequality after unfolding `μ`.
    simp [mu]

/-- `μ` is monotone in the entropy budget `h`. -/
lemma mu_mono_h {F : Family n} {Rset : Finset (Subcube n)}
    {h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) :
    mu (n := n) F h₁ Rset ≤ mu (n := n) F h₂ Rset := by
  -- Increasing the entropy budget can only increase the measure.
  dsimp [mu]
  exact add_le_add (Nat.mul_le_mul_left _ hh) le_rfl

/-- Adding a rectangle can only shrink the set of uncovered pairs. -/
lemma mu_union_singleton_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ} :
    mu (n := n) F h (Rset ∪ {R}) ≤ mu (n := n) F h Rset := by
  classical
  -- Adding a rectangle can only reduce the uncovered set.
  have hsub : uncovered (n := n) F (Rset ∪ {R}) ⊆
      uncovered (n := n) F Rset :=
    uncovered_subset_of_union_singleton
      (F := F) (Rset := Rset) (R := R)
  -- Convert the set inclusion into a finset inclusion on cardinals.
  have hsubF : (uncovered (n := n) F (Rset ∪ {R})).toFinset ⊆
        (uncovered (n := n) F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered (n := n) F Rset := hsub hx'
    simpa using hx''
  -- Cardinalities respect inclusion.
  have hcard := Finset.card_le_card hsubF
  -- Add the entropy contribution to both sides.
  have := add_le_add_left hcard (2 * h)
  simpa [mu] using this

/-!
Adding a rectangle that covers at least one previously uncovered pair
strictly decreases the measure.  This lemma will be useful when reasoning
about progress of the cover construction.
-/
lemma mu_union_singleton_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  rcases hx with ⟨p, hpU, hpR⟩
  have hp_not : p ∉ uncovered (n := n) F (Rset ∪ {R}) := by
    rcases hpU with ⟨hf, hx, hnc⟩
    intro hp'
    rcases hp' with ⟨hf', hx', hnc'⟩
    have := hnc' R (by simp) hpR
    exact this
  have hsub : (uncovered (n := n) F (Rset ∪ {R})).toFinset ⊆
      (uncovered (n := n) F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton
        (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  have hproper : ¬((uncovered (n := n) F Rset).toFinset ⊆
        (uncovered (n := n) F (Rset ∪ {R})).toFinset) := by
    intro hsubset
    have hpFin : p ∈ (uncovered (n := n) F Rset).toFinset := by simpa using hpU
    have := hsubset hpFin
    exact hp_not (by simpa using this)
  have hcard := Finset.card_lt_card ⟨hsub, hproper⟩
  have := Nat.add_lt_add_left hcard (2 * h)
  simpa [mu] using this

/-!
A convenient corollary of `mu_union_singleton_lt`: if at least one new
pair becomes covered, the measure decreases by one.  This quantified
version is occasionally handy for numeric estimates.
-/
lemma mu_union_singleton_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R) :
    mu (n := n) F h (Rset ∪ {R}) + 1 ≤ mu (n := n) F h Rset := by
  classical
  have hlt :=
    mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx
  exact Nat.succ_le_of_lt hlt

/--
If `firstUncovered` produces a witness `p`, inserting the point subcube
obtained by freezing all coordinates of `p.2` strictly decreases the measure.
This is a specialised convenience lemma for constructing covers one uncovered
pair at a time.
-/
lemma mu_union_firstUncovered_singleton_lt {F : Family n}
    {Rset : Finset (Subcube n)} {h : ℕ}
    {p : Σ _ : BFunc n, Point n}
    (hp : firstUncovered (n := n) F Rset = some p) :
    mu (n := n) F h
        (Rset ∪
          {Boolcube.Subcube.fromPoint (n := n) p.2
              (Finset.univ : Finset (Fin n))}) <
      mu (n := n) F h Rset := by
  classical
  -- The returned pair is indeed uncovered.
  have hpU :=
    mem_uncovered_of_firstUncovered_some (n := n)
      (F := F) (R := Rset) (p := p) hp
  -- The point `p.2` obviously lies in the singleton subcube we insert.
  have hpR : p.2 ∈ₛ
      Boolcube.Subcube.fromPoint (n := n) p.2 (Finset.univ : Finset (Fin n)) := by
    simpa using
      (Boolcube.Subcube.self_mem_fromPoint (n := n)
        (x := p.2) (K := (Finset.univ : Finset (Fin n))))
  -- Package the witness to apply `mu_union_singleton_lt`.
  have hx : ∃ q ∈ uncovered (n := n) F Rset,
      q.2 ∈ₛ Boolcube.Subcube.fromPoint (n := n) p.2
        (Finset.univ : Finset (Fin n)) := ⟨p, hpU, hpR⟩
  -- Adding this singleton subcube strictly reduces the measure.
  simpa using
    (mu_union_singleton_lt (n := n) (F := F) (Rset := Rset)
      (R := Boolcube.Subcube.fromPoint (n := n) p.2
          (Finset.univ : Finset (Fin n))) (h := h) hx)

/--
If `firstUncovered` produces a witness `p`, inserting the corresponding point
subcube decreases the measure by at least one.  This quantified variant of
`mu_union_firstUncovered_singleton_lt` is convenient when only an inequality is
required.
-/
lemma mu_union_firstUncovered_singleton_succ_le {F : Family n}
    {Rset : Finset (Subcube n)} {h : ℕ}
    {p : Σ _ : BFunc n, Point n}
    (hp : firstUncovered (n := n) F Rset = some p) :
    mu (n := n) F h
        (Rset ∪
          {Boolcube.Subcube.fromPoint (n := n) p.2
              (Finset.univ : Finset (Fin n))}) + 1 ≤
      mu (n := n) F h Rset := by
  classical
  -- The pair returned by `firstUncovered` is uncovered and lies inside the
  -- inserted point subcube.
  have hpU :=
    mem_uncovered_of_firstUncovered_some (n := n)
      (F := F) (R := Rset) (p := p) hp
  have hpR : p.2 ∈ₛ
      Boolcube.Subcube.fromPoint (n := n) p.2 (Finset.univ : Finset (Fin n)) := by
    simpa using
      (Boolcube.Subcube.self_mem_fromPoint (n := n)
        (x := p.2) (K := (Finset.univ : Finset (Fin n))))
  -- Package the witness and apply the general estimate.
  have hx : ∃ q ∈ uncovered (n := n) F Rset,
      q.2 ∈ₛ Boolcube.Subcube.fromPoint (n := n) p.2
        (Finset.univ : Finset (Fin n)) := ⟨p, hpU, hpR⟩
  exact
    mu_union_singleton_succ_le (n := n) (F := F) (Rset := Rset)
      (R := Boolcube.Subcube.fromPoint (n := n) p.2
        (Finset.univ : Finset (Fin n))) (h := h) hx

/--
`extendCover` performs a single covering step.  When `firstUncovered` locates a
pair `(f, x)` that is not yet covered by `Rset` we add the largest subcube
around `x` on which every function in `F` is constant.  Coordinates that affect
any function are frozen while the remaining coordinates stay free.  If no
uncovered pair exists, `Rset` is returned unchanged.
-/
noncomputable def extendCover {n : ℕ} (F : Family n)
    (Rset : Finset (Subcube n)) : Finset (Subcube n) :=
  match firstUncovered (n := n) F Rset with
  | none => Rset
  | some p =>
      let K : Finset (Fin n) :=
        Finset.univ.filter fun i : Fin n =>
          ∃ g ∈ F,
            g p.2 ≠ g (BoolFunc.Point.update (n := n) p.2 i (!(p.2 i)))
      Rset ∪ {Boolcube.Subcube.fromPoint (n := n) p.2 K}

/--
If `firstUncovered` finds an uncovered pair, `extendCover` inserts the
corresponding point subcube and the measure drops by at least one.
-/
lemma mu_extendCover_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ}
    (hfu : firstUncovered (n := n) F Rset ≠ none) :
    mu (n := n) F h (extendCover (n := n) F Rset) + 1 ≤
      mu (n := n) F h Rset := by
  classical
  -- Analyse the outcome of `firstUncovered`.
  cases hfu' : firstUncovered (n := n) F Rset with
  | none =>
      -- Contradiction: `firstUncovered` yielded `none`.
      exact (hfu hfu').elim
  | some p =>
      -- The pair returned by `firstUncovered` is uncovered.
      have hpU :=
        mem_uncovered_of_firstUncovered_some (n := n)
          (F := F) (R := Rset) (p := p) hfu'
      -- The point lies in the newly created subcube.
      have hpR : p.2 ∈ₛ Boolcube.Subcube.fromPoint (n := n) p.2
          (Finset.univ.filter fun i : Fin n =>
            ∃ g ∈ F,
              g p.2 ≠
                g (BoolFunc.Point.update (n := n) p.2 i (!(p.2 i)))) := by
        have :=
          Boolcube.Subcube.self_mem_fromPoint (n := n) (x := p.2)
            (K :=
              Finset.univ.filter fun i : Fin n =>
                ∃ g ∈ F,
                  g p.2 ≠
                    g (BoolFunc.Point.update (n := n) p.2 i (!(p.2 i))))
        simpa using this
      -- Package the witness for `mu_union_singleton_succ_le`.
      have hx : ∃ q ∈ uncovered (n := n) F Rset, q.2 ∈ₛ
          Boolcube.Subcube.fromPoint (n := n) p.2
            (Finset.univ.filter fun i : Fin n =>
              ∃ g ∈ F,
                g p.2 ≠
                  g (BoolFunc.Point.update (n := n) p.2 i (!(p.2 i)))) :=
        ⟨p, hpU, hpR⟩
      have hdrop :=
        mu_union_singleton_succ_le (n := n) (F := F) (Rset := Rset)
          (R := Boolcube.Subcube.fromPoint (n := n) p.2
            (Finset.univ.filter fun i : Fin n =>
              ∃ g ∈ F,
                g p.2 ≠
                  g (BoolFunc.Point.update (n := n) p.2 i (!(p.2 i)))))
          (h := h) hx
      simpa [extendCover, hfu'] using hdrop

/--
If the search for an uncovered pair fails, `extendCover` leaves the set of
rectangles unchanged.  This lemma exposes that behaviour for convenient
rewriting in subsequent proofs.
-/
@[simp] lemma extendCover_none {F : Family n} {Rset : Finset (Subcube n)}
    (hfu : firstUncovered (n := n) F Rset = none) :
    extendCover (n := n) F Rset = Rset := by
  classical
  simp [extendCover, hfu]

/--
Applying `extendCover` never increases the termination measure `μ`.  If a new
rectangle is inserted the measure drops by at least one, otherwise it remains
unchanged.
-/
lemma mu_extendCover_le {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    mu (n := n) F h (extendCover (n := n) F Rset) ≤
      mu (n := n) F h Rset := by
  classical
  -- Inspect the outcome of `firstUncovered`.
  cases hfu : firstUncovered (n := n) F Rset with
  | none =>
      -- No uncovered pairs remain; `extendCover` is the identity.
      simpa [extendCover, hfu]
  | some p =>
      -- A new rectangle gets inserted and the measure decreases.
      have hfu' : firstUncovered (n := n) F Rset ≠ none := by
        simpa [hfu]
      have hdrop :=
        mu_extendCover_succ_le (n := n) (F := F) (Rset := Rset)
          (h := h) hfu'
      -- Turn the quantified drop by one into a plain inequality.
      have := Nat.le_trans (Nat.le_succ _)
        (by simpa [extendCover, hfu] using hdrop)
      simpa [extendCover, hfu] using this

/--
If a rectangle covers two distinct uncovered pairs, the measure drops
strictly after inserting this rectangle.
-/
lemma mu_union_singleton_double_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
      {p₁ p₂ : Σ _ : BFunc n, Point n}
      (hp₁ : p₁ ∈ uncovered (n := n) F Rset)
      (_hp₂ : p₂ ∈ uncovered (n := n) F Rset)
      (hp₁R : p₁.2 ∈ₛ R) (_hp₂R : p₂.2 ∈ₛ R)
      (_hne : p₁ ≠ p₂) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  -- It suffices to cover one of the two pairs.
  have hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R := ⟨p₁, hp₁, hp₁R⟩
  -- Apply the basic inequality for a newly covered pair.
  exact mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx

/--
If a rectangle covers two distinct uncovered pairs, the measure drops by at
least two after inserting this rectangle.  This mirrors the bookkeeping
argument from the original `cover` module.
-/
lemma mu_union_singleton_double_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F Rset) (hp₂ : p₂ ∈ uncovered (n := n) F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂) :
    mu (n := n) F h (Rset ∪ {R}) + 2 ≤ mu (n := n) F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F Rset).toFinset
  let T : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hxT
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton
        (F := F) (Rset := Rset) (R := R) hx'
    simpa [S] using hx''
  -- Membership facts for the two pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  -- After adding `R`, the pairs `p₁` and `p₂` are no longer uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂`.
  have hsub2 : T ⊆ (S.erase p₁).erase p₂ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq
      have : p₁ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq
      have : p₂ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₂T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    exact Finset.mem_erase.mpr ⟨hxne2, hx1⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne.symm, hp₂S⟩
  have hcard_le : T.card ≤ ((S.erase p₁).erase p₂).card :=
    Finset.card_le_card hsub2
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard_final : T.card ≤ S.card - 2 := by
    have := hcard_le
    simpa [hcard1, hcard2] using this
  -- `S` contains both `p₁` and `p₂`, so its cardinality is at least two.
  have htwo : 2 ≤ S.card := by
    classical
    have hsub_pair : ({p₁, p₂} : Finset _) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hp₁S
      · have hx' := Finset.mem_singleton.mp hx; simpa [hx'] using hp₂S
    have hcard_pair : ({p₁, p₂} : Finset _).card = 2 := by
      classical
      -- Use the dedicated lemma for the cardinality of a pair.
      exact Finset.card_pair (a := p₁) (b := p₂) hne
    have htwo_aux : 2 ≤ ({p₁, p₂} : Finset _).card := by
      -- Rewrite using the computed cardinality.
      simp [hcard_pair]
    exact le_trans htwo_aux (Finset.card_le_card hsub_pair)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le htwo).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/--
If a rectangle covers three distinct uncovered pairs, the measure drops
strictly after inserting this rectangle.
-/
lemma mu_union_singleton_triple_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
      {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
      (hp₁ : p₁ ∈ uncovered (n := n) F Rset)
      (_hp₂ : p₂ ∈ uncovered (n := n) F Rset)
      (_hp₃ : p₃ ∈ uncovered (n := n) F Rset)
      (hp₁R : p₁.2 ∈ₛ R)
      (_hp₂R : p₂.2 ∈ₛ R) (_hp₃R : p₃.2 ∈ₛ R)
      (_hne₁₂ : p₁ ≠ p₂) (_hne₁₃ : p₁ ≠ p₃) (_hne₂₃ : p₂ ≠ p₃) :
    mu (n := n) F h (Rset ∪ {R}) < mu (n := n) F h Rset := by
  classical
  -- It suffices to cover one of the three pairs.
  have hx : ∃ p ∈ uncovered (n := n) F Rset, p.2 ∈ₛ R := ⟨p₁, hp₁, hp₁R⟩
  exact mu_union_singleton_lt (F := F) (Rset := Rset) (R := R) (h := h) hx

/--
If a rectangle covers three distinct uncovered pairs, the measure drops by
at least three after inserting this rectangle.
-/
lemma mu_union_singleton_triple_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F Rset) (hp₂ : p₂ ∈ uncovered (n := n) F Rset)
    (hp₃ : p₃ ∈ uncovered (n := n) F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃) :
    mu (n := n) F h (Rset ∪ {R}) + 3 ≤ mu (n := n) F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F Rset).toFinset
  let T : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hxT
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa [S] using hx''
  -- Membership facts for the three pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  have hp₃S : p₃ ∈ S := by simpa [S] using hp₃
  -- After adding `R`, none of the pairs remain uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  have hp₃T : p₃ ∉ T := by
    intro hx
    have hx' : p₃ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₃R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂.erase p₃`.
  have hsub3 : T ⊆ ((S.erase p₁).erase p₂).erase p₃ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq
      have : p₁ ∈ T := by
        simpa [T, hxEq] using hxT
      exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq
      have : p₂ ∈ T := by
        simpa [T, hxEq] using hxT
      exact hp₂T this
    have hxne3 : x ≠ p₃ := by
      intro hxEq
      have : p₃ ∈ T := by
        simpa [T, hxEq] using hxT
      exact hp₃T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    have hx2 : x ∈ (S.erase p₁).erase p₂ := Finset.mem_erase.mpr ⟨hxne2, hx1⟩
    exact Finset.mem_erase.mpr ⟨hxne3, hx2⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne₁₂.symm, hp₂S⟩
  have hp₃_in_erase2 : p₃ ∈ (S.erase p₁).erase p₂ := by
    have hp₃_in_erase1 : p₃ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₃.symm, hp₃S⟩
    exact Finset.mem_erase.mpr ⟨hne₂₃.symm, hp₃_in_erase1⟩
  have hcard_le : T.card ≤ (((S.erase p₁).erase p₂).erase p₃).card :=
    Finset.card_le_card hsub3
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 : ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard3 : (((S.erase p₁).erase p₂).erase p₃).card =
      ((S.erase p₁).erase p₂).card - 1 :=
    Finset.card_erase_of_mem hp₃_in_erase2
  have hcard_final : T.card ≤ S.card - 3 := by
    have := hcard_le
    simpa [hcard1, hcard2, hcard3] using this
  -- `S` contains the three distinct pairs, so its cardinality is at least three.
  have hthree : 3 ≤ S.card := by
    classical
      have hsub_trip : ({p₁, p₂, p₃} : Finset _) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hx₁ | hxrest
        · simpa [hx₁] using hp₁S
        rcases Finset.mem_insert.mp hxrest with hx₂ | hx₃
        · subst hx₂
          simpa using hp₂S
        · have hx' := Finset.mem_singleton.mp hx₃
          simpa [hx'] using hp₃S
    have hcard_trip : ({p₁, p₂, p₃} : Finset _).card = 3 := by
      classical
      have hnot12 : p₁ ≠ p₂ := hne₁₂
      have hnot13 : p₁ ≠ p₃ := hne₁₃
      have hnot23 : p₂ ≠ p₃ := hne₂₃
      -- Remove the unused lemma and simplify.
      simp [Finset.card_insert_of_notMem, hnot12, hnot13, hnot23]
    have hthree_aux : 3 ≤ ({p₁, p₂, p₃} : Finset _).card := by
      -- Simplify using the computed cardinality.
      simp [hcard_trip]
    exact hthree_aux.trans (Finset.card_le_card hsub_trip)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le hthree).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/--
Adding a rectangle that covers four distinct uncovered pairs decreases the
measure by at least four.  This variant is occasionally useful for sharp
numerical bounds.
-/
lemma mu_union_singleton_quad_succ_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ p₄ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F Rset)
    (hp₂ : p₂ ∈ uncovered (n := n) F Rset)
    (hp₃ : p₃ ∈ uncovered (n := n) F Rset)
    (hp₄ : p₄ ∈ uncovered (n := n) F Rset)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R)
    (hp₃R : p₃.2 ∈ₛ R) (hp₄R : p₄.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₁₄ : p₁ ≠ p₄)
    (hne₂₃ : p₂ ≠ p₃) (hne₂₄ : p₂ ≠ p₄) (hne₃₄ : p₃ ≠ p₄) :
    mu (n := n) F h (Rset ∪ {R}) + 4 ≤ mu (n := n) F h Rset := by
  classical
  -- Abbreviations for the uncovered sets before and after inserting `R`.
  let S : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F Rset).toFinset
  let T : Finset (Σ _ : BFunc n, Point n) :=
    (uncovered (n := n) F (Rset ∪ {R})).toFinset
  -- Adding a rectangle cannot create new uncovered pairs.
  have hsub_main : T ⊆ S := by
    intro x hxT
    have hx' : x ∈ uncovered (n := n) F (Rset ∪ {R}) := by
      simpa [T] using hxT
    have hx'' : x ∈ uncovered (n := n) F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa [S] using hx''
  -- Membership facts for the four pairs.
  have hp₁S : p₁ ∈ S := by simpa [S] using hp₁
  have hp₂S : p₂ ∈ S := by simpa [S] using hp₂
  have hp₃S : p₃ ∈ S := by simpa [S] using hp₃
  have hp₄S : p₄ ∈ S := by simpa [S] using hp₄
  -- After inserting `R`, none of the pairs remain uncovered.
  have hp₁T : p₁ ∉ T := by
    intro hx
    have hx' : p₁ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₁R
  have hp₂T : p₂ ∉ T := by
    intro hx
    have hx' : p₂ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₂R
  have hp₃T : p₃ ∉ T := by
    intro hx
    have hx' : p₃ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₃R
  have hp₄T : p₄ ∉ T := by
    intro hx
    have hx' : p₄ ∈ uncovered (n := n) F (Rset ∪ {R}) := by simpa [T] using hx
    rcases hx' with ⟨_, _, hnc⟩
    exact hnc R (by simp) hp₄R
  -- The new uncovered set is contained in `S.erase p₁.erase p₂.erase p₃.erase p₄`.
  have hsub4 :
      T ⊆ (((S.erase p₁).erase p₂).erase p₃).erase p₄ := by
    intro x hxT
    have hxS : x ∈ S := hsub_main hxT
    have hxne1 : x ≠ p₁ := by
      intro hxEq
      have : p₁ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₁T this
    have hxne2 : x ≠ p₂ := by
      intro hxEq
      have : p₂ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₂T this
    have hxne3 : x ≠ p₃ := by
      intro hxEq
      have : p₃ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₃T this
    have hxne4 : x ≠ p₄ := by
      intro hxEq
      have : p₄ ∈ T := by simpa [T, hxEq] using hxT
      exact hp₄T this
    have hx1 : x ∈ S.erase p₁ := Finset.mem_erase.mpr ⟨hxne1, hxS⟩
    have hx2 : x ∈ (S.erase p₁).erase p₂ :=
      Finset.mem_erase.mpr ⟨hxne2, hx1⟩
    have hx3 : x ∈ ((S.erase p₁).erase p₂).erase p₃ :=
      Finset.mem_erase.mpr ⟨hxne3, hx2⟩
    exact Finset.mem_erase.mpr ⟨hxne4, hx3⟩
  -- Cardinalities of the intermediate sets.
  have hp₂_in_erase1 : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨hne₁₂.symm, hp₂S⟩
  have hp₃_in_erase2 : p₃ ∈ (S.erase p₁).erase p₂ := by
    have hp₃_in_erase1 : p₃ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₃.symm, hp₃S⟩
    exact Finset.mem_erase.mpr ⟨hne₂₃.symm, hp₃_in_erase1⟩
  have hp₄_in_erase3 : p₄ ∈ ((S.erase p₁).erase p₂).erase p₃ := by
    have hp₄_in_erase1 : p₄ ∈ S.erase p₁ :=
      Finset.mem_erase.mpr ⟨hne₁₄.symm, hp₄S⟩
    have hp₄_in_erase2 : p₄ ∈ (S.erase p₁).erase p₂ :=
      Finset.mem_erase.mpr ⟨hne₂₄.symm, hp₄_in_erase1⟩
    exact Finset.mem_erase.mpr ⟨hne₃₄.symm, hp₄_in_erase2⟩
  have hcard_le :
      T.card ≤ ((((S.erase p₁).erase p₂).erase p₃).erase p₄).card :=
    Finset.card_le_card hsub4
  have hcard1 : (S.erase p₁).card = S.card - 1 :=
    Finset.card_erase_of_mem hp₁S
  have hcard2 :
      ((S.erase p₁).erase p₂).card = (S.erase p₁).card - 1 :=
    Finset.card_erase_of_mem hp₂_in_erase1
  have hcard3 :
      (((S.erase p₁).erase p₂).erase p₃).card =
        ((S.erase p₁).erase p₂).card - 1 :=
    Finset.card_erase_of_mem hp₃_in_erase2
  have hcard4 :
      ((((S.erase p₁).erase p₂).erase p₃).erase p₄).card =
        (((S.erase p₁).erase p₂).erase p₃).card - 1 :=
    Finset.card_erase_of_mem hp₄_in_erase3
  have hcard_final : T.card ≤ S.card - 4 := by
    have := hcard_le
    simpa [hcard1, hcard2, hcard3, hcard4] using this
  -- `S` contains the four distinct pairs, so its cardinality is at least four.
  have hfour : 4 ≤ S.card := by
    classical
    have hsub_quad : ({p₁, p₂, p₃, p₄} : Finset _) ⊆ S := by
      intro x hx
      have hx' : x = p₁ ∨ x = p₂ ∨ x = p₃ ∨ x = p₄ := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_assoc, or_left_comm,
              or_comm] using hx
      rcases hx' with h₁ | hx'
      · subst h₁; simpa using hp₁S
      rcases hx' with h₂ | hx'
      · subst h₂; simpa using hp₂S
      rcases hx' with h₃ | h₄
      · subst h₃; simpa using hp₃S
      · subst h₄; simpa using hp₄S
    have hcard_quad : ({p₁, p₂, p₃, p₄} : Finset _).card = 4 := by
      classical
      have hnot12 : p₁ ≠ p₂ := hne₁₂
      have hnot13 : p₁ ≠ p₃ := hne₁₃
      have hnot14 : p₁ ≠ p₄ := hne₁₄
      have hnot23 : p₂ ≠ p₃ := hne₂₃
      have hnot24 : p₂ ≠ p₄ := hne₂₄
      have hnot34 : p₃ ≠ p₄ := hne₃₄
      -- Omit the unused lemma and simplify.
      simp [Finset.card_insert_of_notMem,
            hnot12, hnot13, hnot14, hnot23, hnot24, hnot34]
    have hfour_aux : 4 ≤ ({p₁, p₂, p₃, p₄} : Finset _).card := by
      -- Simplify using the established cardinality.
      simp [hcard_quad]
    exact hfour_aux.trans (Finset.card_le_card hsub_quad)
  -- Convert the difference bound into the desired inequality.
  have hdiff := (Nat.le_sub_iff_add_le hfour).mp hcard_final
  -- Add the `2 * h` entropy contribution to both sides.
  have := Nat.add_le_add_left hdiff (2 * h)
  -- Rewrite everything in terms of `μ`.
  simpa [mu, S, T, add_comm, add_left_comm, add_assoc] using this

/-!
### Behaviour under unions

The remaining lemmas establish how `μ` changes when we take unions of
different rectangle collections.  These results are the workhorses in the
termination argument for the cover construction.
-/

/-- Taking the union of two rectangle sets cannot increase the measure. -/
lemma mu_union_le {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ} :
    mu (n := n) F h (R₁ ∪ R₂) ≤ mu (n := n) F h R₁ := by
  classical
  -- We induct over `R₂`, inserting one rectangle at a time.
  refine Finset.induction_on R₂ ?base ?step
  · -- Base case: union with the empty set has no effect.
    simp [mu]
  · -- Induction step: insert a rectangle `R` into the growing set `S`.
    intro R S hR hIH
    -- First bound the union with `R` using the single-rectangle lemma.
    have hstep :=
      mu_union_singleton_le (F := F) (Rset := R₁ ∪ S) (R := R) (h := h)
    -- Combine with the induction hypothesis.
    have hcomb := le_trans hstep hIH
    -- Reassociate unions to match the induction hypothesis.
    have : R₁ ∪ insert R S = (R₁ ∪ S) ∪ {R} := by
      ext x; by_cases hx : x = R
      · subst hx; simp [hR]
      · simp [Finset.mem_insert, hx]
    simpa [this, Finset.union_assoc] using hcomb

/-- If `R₁ ⊆ R₂`, then the measure for `R₂` is bounded by that for `R₁`. -/
lemma mu_mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hsub : R₁ ⊆ R₂) :
    mu (n := n) F h R₂ ≤ mu (n := n) F h R₁ := by
  classical
  -- Express `R₂` as `R₁ ∪ (R₂ \ R₁)` and apply `mu_union_le`.
  have hunion : R₂ = R₁ ∪ (R₂ \ R₁) := by
    ext x; by_cases hx : x ∈ R₁
    · constructor
      · intro _; exact Finset.mem_union.mpr <| Or.inl hx
      · intro _; exact hsub hx
    · constructor
      · intro hxR2
        have hxRdiff : x ∈ R₂ \ R₁ :=
          -- Rewrite membership in the difference using `simp`.
          Finset.mem_sdiff.mpr ⟨hxR2, by simp [hx]⟩
        exact Finset.mem_union.mpr <| Or.inr hxRdiff
      · intro hxUnion
        rcases Finset.mem_union.mp hxUnion with hx₁ | hx₂
        · exact hsub hx₁
        · exact (Finset.mem_sdiff.mp hx₂).1
  have hmain := mu_union_le (n := n) (F := F) (h := h)
      (R₁ := R₁) (R₂ := R₂ \ R₁)
  have hrewrite :
      mu (n := n) F h R₂ = mu (n := n) F h (R₁ ∪ (R₂ \ R₁)) :=
    congrArg (fun S => mu (n := n) F h S) hunion
  have := hrewrite ▸ hmain
  simpa using this

/--
If some uncovered pair of `R₁` is covered by a rectangle from `R₂`, then
`μ` strictly decreases after taking the union.
-/
lemma mu_union_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hx : ∃ p ∈ uncovered (n := n) F R₁, ∃ R ∈ R₂, p.2 ∈ₛ R) :
    mu (n := n) F h (R₁ ∪ R₂) < mu (n := n) F h R₁ := by
  classical
  rcases hx with ⟨p, hpU, R, hR, hpR⟩
  -- First insert the specific rectangle that covers `p`.
  have hx_singleton : ∃ q ∈ uncovered (n := n) F R₁, q.2 ∈ₛ R :=
    ⟨p, hpU, hpR⟩
  have hstep :=
    mu_union_singleton_lt (F := F) (Rset := R₁) (R := R)
      (h := h) hx_singleton
  -- Adding more rectangles cannot increase the measure.
  have hsubset : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx'
    rcases Finset.mem_union.mp hx' with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hR
  have hmono :=
    mu_mono_subset (F := F) (h := h)
      (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsubset
  exact lt_of_le_of_lt hmono hstep

/-- `mu_union_double_succ_le` combines the single-rectangle estimate with
monotonicity.  If some rectangle in `R₂` covers two distinct uncovered
pairs of `R₁`, then the measure drops by at least two after taking the
union. -/
lemma mu_union_double_succ_le {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁) (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) + 2 ≤ mu (n := n) F h R₁ := by
  classical
  -- Adding additional rectangles can only decrease the measure.
  have hsub : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hmem
  have hmono := mu_mono_subset (F := F) (h := h)
      (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsub
  have hdouble := mu_union_singleton_double_succ_le
      (F := F) (Rset := R₁) (R := R) (h := h)
      hp₁ hp₂ hp₁R hp₂R hne
  have := add_le_add_right hmono 2
  exact le_trans this hdouble

/-- `mu_union_double_lt` is the strict version of `mu_union_double_succ_le`. -/
lemma mu_union_double_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁) (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hne : p₁ ≠ p₂)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) < mu (n := n) F h R₁ := by
  classical
  have hdrop :=
    mu_union_double_succ_le (F := F) (R₁ := R₁) (R₂ := R₂)
      (R := R) (h := h) hp₁ hp₂ hp₁R hp₂R hne hmem
  have hsucc : mu (n := n) F h (R₁ ∪ R₂) + 1 ≤ mu (n := n) F h R₁ := by
    have hstep : (1 : ℕ) ≤ 2 := by decide
    have := Nat.add_le_add_left hstep (mu (n := n) F h (R₁ ∪ R₂))
    exact this.trans hdrop
  exact Nat.lt_of_succ_le hsucc

/--
`mu_union_triple_succ_le` extends `mu_union_double_succ_le` to three
pairs.  If some rectangle in `R₂` covers all three uncovered pairs of
`R₁`, then taking the union with `R₂` decreases the measure by at least
three.
-/
lemma mu_union_triple_succ_le {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁)
    (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₃ : p₃ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) + 3 ≤ mu (n := n) F h R₁ := by
  classical
  -- Taking the union with a larger set can only reduce the measure.
  have hsub : R₁ ∪ {R} ⊆ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact Finset.mem_union.mpr <| Or.inl hx₁
    · rcases Finset.mem_singleton.mp hx₂ with rfl
      exact Finset.mem_union.mpr <| Or.inr hmem
  have hmono :=
    mu_mono_subset (F := F) (h := h) (R₁ := R₁ ∪ {R}) (R₂ := R₁ ∪ R₂) hsub
  -- Covering the three pairs with `R` yields a drop of at least three.
  have htriple :=
    mu_union_singleton_triple_succ_le (F := F) (Rset := R₁) (R := R) (h := h)
      hp₁ hp₂ hp₃ hp₁R hp₂R hp₃R hne₁₂ hne₁₃ hne₂₃
  have := add_le_add_right hmono 3
  exact le_trans this htriple

/-- `mu_union_triple_lt` is the strict version of `mu_union_triple_succ_le`. -/
lemma mu_union_triple_lt {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    {p₁ p₂ p₃ : Σ _ : BFunc n, Point n}
    (hp₁ : p₁ ∈ uncovered (n := n) F R₁)
    (hp₂ : p₂ ∈ uncovered (n := n) F R₁)
    (hp₃ : p₃ ∈ uncovered (n := n) F R₁)
    (hp₁R : p₁.2 ∈ₛ R) (hp₂R : p₂.2 ∈ₛ R) (hp₃R : p₃.2 ∈ₛ R)
    (hne₁₂ : p₁ ≠ p₂) (hne₁₃ : p₁ ≠ p₃) (hne₂₃ : p₂ ≠ p₃)
    (hmem : R ∈ R₂) :
    mu (n := n) F h (R₁ ∪ R₂) < mu (n := n) F h R₁ := by
  classical
  -- First obtain the additive inequality dropping by three.
  have hdrop :=
    mu_union_triple_succ_le (F := F) (R₁ := R₁) (R₂ := R₂)
      (R := R) (h := h) hp₁ hp₂ hp₃ hp₁R hp₂R hp₃R
      hne₁₂ hne₁₃ hne₂₃ hmem
  -- Convert it into a strict inequality.
  have hsucc : mu (n := n) F h (R₁ ∪ R₂) + 1 ≤ mu (n := n) F h R₁ := by
    have hstep : (1 : ℕ) ≤ 3 := by decide
    have := Nat.add_le_add_left hstep (mu (n := n) F h (R₁ ∪ R₂))
    exact this.trans hdrop
  exact Nat.lt_of_succ_le hsucc

/-!
### Detecting progress

If `firstUncovered` returns some pair, then the measure exceeds `2 * h`.
This witness guarantees that the uncovered set has positive cardinality.
-/
lemma mu_gt_of_firstUncovered_some {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hfu : firstUncovered (n := n) F Rset ≠ none) :
    2 * h < mu (n := n) F h Rset := by
  classical
  -- If `firstUncovered` is nonempty, the uncovered set cannot be empty.
  have hne : uncovered (n := n) F Rset ≠
      (∅ : Set (Σ _ : BFunc n, Point n)) := by
    intro hempty
    have := (firstUncovered_none_iff (n := n) (F := F) (R := Rset)).2 hempty
    exact hfu this
  -- Obtain an explicit witness from the nonempty uncovered set.
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- This ensures the cardinality of the finset is positive.
  have hpos : 0 < (uncovered (n := n) F Rset).toFinset.card :=
    Finset.card_pos.mpr ⟨p, by simpa using hp⟩
  -- Conclude that `μ` exceeds `2 * h` by at least one.
  have := Nat.lt_add_of_pos_right (n := 2 * h) hpos
  simpa [mu] using this

end Cover2
