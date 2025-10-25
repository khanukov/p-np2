import Mathlib.Data.Nat.Basic

/-!
Utilities for natural numbers extending the lemmas available in `Mathlib`.
These statements are kept minimal and are intended to support the gate-count
bookkeeping developed for straight-line circuits with sharing.
-/

namespace Nat

/--
If `b ≤ a` and `a < b + c`, then the excess `a - b` is strictly smaller than
`c`.  Intuitively this just extracts the "headroom" of the inequality by
subtracting the common prefix `b` from both sides.
-/
lemma sub_lt_of_le_of_lt {a b c : ℕ} (hb : b ≤ a) (h : a < b + c) : a - b < c := by
  have hrewrite : b + (a - b) = a := Nat.add_sub_of_le hb
  have hbound : b + (a - b) < b + c := by simpa [hrewrite] using h
  exact Nat.lt_of_add_lt_add_left hbound

end Nat

