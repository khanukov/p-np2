import Pnp.BoolFunc.Support

open Pnp.BoolFunc

namespace SupportTests

/-- Updating a coordinate outside the support leaves a constant function unchanged. -/
example (n : ℕ) (x : Point n) (i : Fin n) (b : Bool) :
    let f : BFunc n := fun _ => true
    f x = f (x.update i b) := by
  classical
  intro f
  have hi : i ∉ support f := by
    ext j
    simp [support, f]
  simpa [f] using eval_update_not_support (f := f) hi x b

/-- If two points agree on the support, the function values coincide. -/
example (x y : Point 2) (hx : x 0 = y 0) (hy : x 1 = y 1) :
    let f : BFunc 2 := fun z => z 0 && z 1
    f x = f y := by
  classical
  intro f
  have hsupp : support f = {0, 1} := by
    ext i
    fin_cases i <;> simp [support, f]
  have hx' : ∀ i, i ∈ support f → x i = y i := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by
      simpa [hsupp] using hi
    cases hi' with
    | inl h0 => cases h0; simpa [hx]
    | inr h1 => cases h1; simpa [hy]
  simpa [f] using eval_eq_of_agree_on_support (f := f) hx'

/-- A nontrivial function evaluates to `true` somewhere on its support. -/
example :
    let f : BFunc 1 := fun z => z 0
    ∃ x, f x = true := by
  classical
  intro f
  have hsupp : support f ≠ (∅ : Finset (Fin 1)) := by
    classical
    simp [support, f]
  simpa [f] using exists_true_on_support (f := f) hsupp

end SupportTests
