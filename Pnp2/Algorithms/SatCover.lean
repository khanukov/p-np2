import Pnp2.Boolcube
import Pnp2.Cover.Compute
import Pnp2.cover
import Pnp2.collentropy

open Boolcube
open Cover

namespace Pnp2.Algorithms

variable {n : ℕ}

/--
Helper: build the cover list for a single function `f` using the entropy
bound `h`.  The singleton family `{f}` has collision entropy `0`, so the
precondition for `buildCoverCompute` is trivially satisfied.
-/
noncomputable def buildCoverFor (f : BoolFun n) (h : ℕ) : List (Subcube n) := by
  classical
  have hH : BoolFunc.H₂ ({f} : Family n) ≤ (h : ℝ) := by
    have hx : BoolFunc.H₂ ({f} : Family n) = 0 := by
      simp [BoolFunc.H₂_card_one]
    have hx' : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.zero_le h
    simpa [hx] using hx'
  exact buildCoverCompute (F := ({f} : Family n)) (h := h) hH

/--
Evaluate `f` on the representative of each subcube in `l`, returning the first
point where the function outputs `true`.
-/
def satFromList (f : BoolFun n) : List (Subcube n) → Option (Point n)
  | [] => none
  | R :: rs =>
      let x := Subcube.rep (n := n) R
      if f x then some x else satFromList rs
  termination_by l => l.length
  decreasing_by simp

/--
Main SAT solver: construct a cover for `{f}` and scan the rectangles for a
satisfying assignment.  Returns `none` if `f` is constantly `false`.
-/
noncomputable def satViaCover (f : BoolFun n) (h : ℕ) : Option (Point n) :=
  satFromList (f := f) (buildCoverFor (f := f) (h := h))

/--
If some rectangle in `l` evaluates to `true` on its representative, then
`satFromList` returns such a witness.
-/
lemma satFromList_spec {f : BoolFun n} :
    ∀ {l : List (Subcube n)},
      (∃ R ∈ l, f (Subcube.rep (n := n) R) = true) →
        ∃ x, satFromList (n := n) f l = some x ∧ f x = true := by
  intro l
  induction l with
  | nil =>
      intro h; rcases h with ⟨R, hR, _⟩; cases hR
  | cons R rs ih =>
      intro h
      rcases h with ⟨S, hS, hval⟩
      cases hS with
      | head =>
          subst S
          dsimp [satFromList]
          simp [hval]
      | tail hSrs =>
          dsimp [satFromList]
          by_cases hx : f (Subcube.rep (n := n) R)
          · simp [hx] at hval
          · have h' : ∃ T ∈ rs, f (Subcube.rep (n := n) T) = true := ⟨S, hSrs, hval⟩
            have := ih h'
            rcases this with ⟨x, hxout, hxval⟩
            simp [hx, hxout, hxval]

/--
If all representatives evaluate to `false`, `satFromList` returns `none`.
-/
lemma satFromList_none {f : BoolFun n} :
    ∀ {l : List (Subcube n)},
      (∀ R ∈ l, f (Subcube.rep (n := n) R) = false) →
        satFromList (n := n) f l = none := by
  intro l
  induction l with
  | nil =>
      intro _; rfl
  | cons R rs ih =>
      intro h
      have hR := h R (by simp)
      have hrs := fun S hS => h S (by simp [hS])
      dsimp [satFromList]
      simp [hR, ih hrs]

/--
Correctness of `satViaCover`: if `f` has entropy at most `h`, the algorithm
returns a witness exactly when one exists.  The witness indeed satisfies `f`.
-/
lemma satViaCover_correct (f : BoolFun n) (h : ℕ)
    (hh : BoolFunc.H₂Fun (n := n) f ≤ h) :
    (∃ x, satViaCover (n := n) f h = some x ∧ f x = true) ↔
      ∃ x, f x = true := by
  classical
  -- Build the cover list once and recall its specification.
  let Rlist := buildCoverFor (n := n) (f := f) (h := h)
  have hspec := buildCoverCompute_spec
      (F := ({f} : Family n)) (h := h) (by
        have hx : BoolFunc.H₂ ({f} : Family n) = 0 := by
          simp [BoolFunc.H₂_card_one]
        have hx' : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.zero_le h
        simpa [hx] using hx')
  constructor
  · intro hres
    rcases hres with ⟨x, hxout, hxval⟩
    exact ⟨x, hxval⟩
  · intro hx
    rcases hx with ⟨x, hx⟩
    -- Use the coverage part of the specification.
    have hxcov := hspec.1 f (by simp) x hx
    rcases hxcov with ⟨R, hR, hxR⟩
    -- `R` occurs in the list and is monochromatic.
    have hRlist : R ∈ Rlist := List.mem_toFinset.mp hR
    have hmono := hspec.2.1 R hR
    rcases hmono with ⟨b, hb⟩
    have hxcol : f x = b := hb hxR
    have hbtrue : b = true := by simpa [hx] using hxcol
    -- Hence the representative also evaluates to `true`.
    have hrep : f (Subcube.rep (n := n) R) = true := by
      have := hb (Subcube.rep_mem (n := n) R)
      simpa [hbtrue] using this
    have hExists : ∃ S ∈ Rlist, f (Subcube.rep (n := n) S) = true :=
      ⟨R, hRlist, hrep⟩
    -- `satFromList` succeeds on this list.
    have := satFromList_spec (f := f) (l := Rlist) hExists
    rcases this with ⟨y, hyout, hyval⟩
    exact ⟨y, by simpa [satViaCover, buildCoverFor] using hyout, hyval⟩

/--
If `satViaCover` returns `none`, the function is constantly `false`.
-/
lemma satViaCover_none (f : BoolFun n) (h : ℕ)
    (hh : BoolFunc.H₂Fun (n := n) f ≤ h) :
    satViaCover (n := n) f h = none ↔ ∀ x, f x = false := by
  classical
  let Rlist := buildCoverFor (n := n) (f := f) (h := h)
  have hspec := buildCoverCompute_spec
      (F := ({f} : Family n)) (h := h) (by
        have hx : BoolFunc.H₂ ({f} : Family n) = 0 := by
          simp [BoolFunc.H₂_card_one]
        have hx' : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.zero_le h
        simpa [hx] using hx')
  constructor
  · intro hnone
    -- `satFromList` returned none, hence every representative is false.
    have hfalse : ∀ R ∈ Rlist, f (Subcube.rep (n := n) R) = false := by
      -- Contraposition via `satFromList_spec`.
      intro R hR
      by_contra hpos
      have hExists : ∃ S ∈ Rlist, f (Subcube.rep (n := n) S) = true := ⟨R, hR, by
        simpa using hpos⟩
      have := satFromList_spec (f := f) (l := Rlist) hExists
      rcases this with ⟨x, hxout, hxval⟩
      simpa [satViaCover, buildCoverFor, hnone] using hxout
    -- Any input `x` lies in some rectangle; all are false.
    intro x
    have hxcov := hspec.1 f (by simp) x
    by_cases hxval : f x = true
    · have := hxcov hxval
      rcases this with ⟨R, hR, hxR⟩
      have := hfalse R (List.mem_toFinset.mp hR)
      have := hspec.2.1 R hR
      rcases this with ⟨b, hb⟩
      have hxcol : f x = b := hb hxR
      have hbfalse : b = false := by simpa [hxval] using hxcol
      have hrep := hb (Subcube.rep_mem (n := n) R)
      have hrepFalse : f (Subcube.rep (n := n) R) = false := by simpa [hbfalse] using hrep
      simpa using hrepFalse
    · simpa [hxval]
  · intro hfalse
    have : ∀ R ∈ Rlist, f (Subcube.rep (n := n) R) = false := by
      intro R hR
      have hx := hspec.2.1 R hR
      rcases hx with ⟨b, hb⟩
      have hrep := hb (Subcube.rep_mem (n := n) R)
      have hbfalse : b = false := by
        have hxpoint := hfalse (Subcube.rep (n := n) R)
        have hxcol : f (Subcube.rep (n := n) R) = b := hrep
        simpa [hxpoint] using hxcol.symm
      simpa [hbfalse] using hrep
    have := satFromList_none (f := f) (l := Rlist) this
    simpa [satViaCover, buildCoverFor] using this

/--
`satViaCover_time` counts how many evaluations of `f` the algorithm performs.
This equals the length of the constructed cover list.
-/
noncomputable def satViaCover_time (f : BoolFun n) (h : ℕ) : ℕ :=
  (buildCoverFor (f := f) (h := h)).length

lemma satViaCover_time_bound (f : BoolFun n) (h : ℕ)
    (hh : BoolFunc.H₂Fun (n := n) f ≤ h) :
    satViaCover_time (n := n) f h ≤ mBound n h := by
  classical
  have hH : BoolFunc.H₂ ({f} : Family n) ≤ (h : ℝ) := by
    have hx : BoolFunc.H₂ ({f} : Family n) = 0 := by
      simp [BoolFunc.H₂_card_one]
    have hx' : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.zero_le h
    simpa [hx] using hx'
  have hspec := buildCoverCompute_spec
      (F := ({f} : Family n)) (h := h) hH
  simpa [satViaCover_time, buildCoverFor, hH] using hspec.2.2

end Pnp2.Algorithms

