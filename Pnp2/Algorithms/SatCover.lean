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

/-!  A simple cardinality bound for `satViaCover_time`.  Since the filtered
set of satisfying assignments is contained in the full cube of size `2^n`,
the running time is trivially bounded by this exponential. -/
lemma satViaCover_time_bound (f : BoolFun n) (h : ℕ) :
    satViaCover_time (n:=n) f h ≤ 2 ^ n := by
  classical
  -- The filtered set is contained in the full cube `Finset.univ`.
  have hsubset :
      (Finset.univ.filter fun x : Point n => f x = true) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  -- Cardinalities respect subset relations.
  have hcard := Finset.card_le_of_subset hsubset
  -- The cube `Fin n → Bool` has size `2 ^ n`.
  have hcube : (Finset.univ : Finset (Point n)).card = 2 ^ n := by
    simpa using (Fintype.card_fun (Fin := Fin n) (β := Bool))
  -- Combine the inequalities.
  simpa [satViaCover_time, hcube] using hcard

end Pnp2.Algorithms
