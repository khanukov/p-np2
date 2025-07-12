import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Finset

namespace BoolFunc
variable {n : ℕ}

/-- If a coordinate is not in the `support` of `f`, updating that coordinate does
not change the value of `f`.  We record this as an axiom. -/
axiom eval_update_not_support {f : BFunc n} {i : Fin n}
    (hi : i ∉ support f) (x : Point n) (b : Bool) :
    f x = f (Point.update x i b)

/-- If `x` and `y` agree on `support f`, then `f x = f y`.
    This lemma is currently assumed as an axiom. -/
axiom eval_eq_of_agree_on_support
    {f : BFunc n} {x y : Point n}
    (h : ∀ i, i ∈ support f → x i = y i) :
    f x = f y

/-- Every non-trivial function evaluates to `true` at some point.
    This statement is provided as an axiom for now. -/
axiom exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true

end BoolFunc
