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
noncomputable def satViaCover (f : BoolFun n) (h : ℕ) : Option (Point n) :=
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
      simp [satViaCover, hx, hxval]
  · constructor
    · intro hres
      rcases hres with ⟨x, hxres, _⟩
      simp [satViaCover, hx] at hxres
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
    have hxval := Classical.choose_spec hx
    simp [satViaCover, hx, hxval, hxfalse]
  · have hxforall : ∀ x, f x = false := by
      intro x
      by_contra hxtrue
      exact hx ⟨x, by simpa using hxtrue⟩
    simp [satViaCover, hx, hxforall]

noncomputable def satViaCover_time (f : BoolFun n) (h : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Point n => f x = true).card

lemma satViaCover_time_bound (f : BoolFun n) (h : ℕ) :
    satViaCover_time (n:=n) f h ≤ 2 ^ n := by
  classical
  have hle := Finset.card_filter_le (s := Finset.univ)
    (p := fun x : Point n => f x = true)
  have huniv : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
    classical
    simpa [Point] using (Finset.card_univ : (Finset.univ : Finset (Point n)).card = Fintype.card (Point n))
  simpa [satViaCover_time, huniv] using hle

end Pnp2.Algorithms
