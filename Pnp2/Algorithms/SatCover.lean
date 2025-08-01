import Pnp2.Boolcube
import Pnp2.Cover.Compute
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

open Boolcube
open Cover

namespace Pnp2.Algorithms

variable {n : ℕ}

/--
`satViaCover` searches for a satisfying assignment of `f`.  The current
implementation simply returns an arbitrary witness using classical
choice whenever one exists.  The parameter `h` is reserved for future
complexity bounds and is presently ignored.
-/
noncomputable def satViaCover (f : BoolFun n) (_h : ℕ) : Option (Point n) :=
  if hx : ∃ x, f x = true then
    some (Classical.choose hx)
  else
    none

lemma satViaCover_correct (f : BoolFun n) (h : ℕ) :
    (∃ x, satViaCover (n:=n) f h = some x ∧ f x = true) ↔ ∃ x, f x = true := by
  classical
  unfold satViaCover
  by_cases hx : ∃ x, f x = true
  · have hxval := Classical.choose_spec hx
    constructor
    · intro hres
      rcases hres with ⟨x, _, hxtrue⟩
      exact ⟨x, hxtrue⟩
    · intro _
      refine ⟨Classical.choose hx, ?_, hxval⟩
      simp [hx]
  · constructor
    · intro hres
      rcases hres with ⟨x, hxres, _⟩
      simp [hx] at hxres
    · intro h
      rcases h with ⟨x, hxtrue⟩
      exact False.elim (hx ⟨x, hxtrue⟩)

lemma satViaCover_none (f : BoolFun n) (h : ℕ) :
    satViaCover (n:=n) f h = none ↔ ∀ x, f x = false := by
  classical
  unfold satViaCover
  by_cases hx : ∃ x, f x = true
  · have hxfalse : ¬ ∀ x, f x = false := by
      rcases hx with ⟨x, hxtrue⟩
      intro h'
      have := h' x
      simp [hxtrue] at this
    simp [hx]
  · have hxforall : ∀ x, f x = false := by
      intro x
      by_contra hxtrue
      exact hx ⟨x, by simpa using hxtrue⟩
    constructor
    · intro _; exact hxforall
    · intro _; simp [hx]

noncomputable def satViaCover_time (f : BoolFun n) (h : ℕ) : ℕ :=
  let _ := h -- retain parameter for future complexity bounds
  (Finset.univ.filter fun x : Point n => f x = true).card

lemma satViaCover_time_le_pow (f : BoolFun n) (h : ℕ) :
    satViaCover_time (n:=n) f h ≤ 2 ^ n := by
  classical
  unfold satViaCover_time
  have hle := Finset.card_filter_le (s := Finset.univ)
      (p := fun x : Point n => f x = true)
  have hcard : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
    simp
  simpa [hcard] using hle

lemma satViaCover_time_bound (f : BoolFun n) (h : ℕ) :
    satViaCover_time (n:=n) f h ≤ 2 ^ n :=
  satViaCover_time_le_pow (f := f) (h := h)

end Pnp2.Algorithms
