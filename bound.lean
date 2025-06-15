/-
bound.lean
===========

Pure *arithmetic* lemmas that translate the explicit counting bound  
`|𝓡| ≤ n·(h+2)·2^(10 h)` (proved in `cover.lean`) into the convenient
*sub‑exponential* tail bound that appears in every prose version of the
Family Collision‑Entropy Lemma:

> for sufficiently large `n` we have  
> `n·(h+2)·2^(10 h) < 2^{n / 100}`.

The file is intentionally **isolated** from the combinatorial logic:
its only imports are earlier modules for the *definitions* of `mBound`
and `coverFamily`.  All non‑trivial proofs are left as `sorry` (milestone
**F**), but the *statements* are final and can be used by subsequent
documentation or tests.
-/

import Cover
import Mathlib.Data.Real.Log
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic

open Classical
open Cover

namespace Bound

/-! ## Elementary growth estimates -/

/-- A *convenience constant* `n₀(h)` such that  
    for all `n ≥ n₀(h)` we have  
    `n·(h+2)·2^(10 h) < 2^{n/100}`.  

    The closed‑form we pick (far from optimal) is  
    `n₀(h) = 10 000 · (h + 2) · 2^(10 h)`.  -/
def n₀ (h : ℕ) : ℕ :=
  10000 * (h + 2) * Nat.pow 2 (10 * h)

/-- Main numeric inequality: the explicit bound *is* sub‑exponential. -/
lemma mBound_lt_subexp
    (h : ℕ) (n : ℕ) (hn : n ≥ n₀ h) :
    mBound n h < Nat.pow 2 (n / 100) := by
  /-  **Intended proof idea**

      •  Expand `mBound n h = n·(h+2)·2^(10 h)`.  
      •  Compare with `2^{n/100}` via logs:  
           `log₂(n·…) ≤ log₂ n + …`.  
      •  For `n ≥ 10000·…` the RHS < `n/100`. -/
  -- Formal (arith) proof still to be written.
  sorry

/-! ## Final packaging: the full FCE‑lemma statement -/

open BoolFunc

variable {n h : ℕ} (F : Family n)

/--
**Family Collision‑Entropy Lemma (β‑version).**

Under the entropy assumption `H₂(F) ≤ h`,
the `coverFamily` constructed in `cover.lean`:

1.  is jointly **monochromatic** on each rectangle;
2.  **covers** every `1`‑input of every `f ∈ F`;
3.  satisfies the **sub‑exponential** bound  
    `|coverFamily| < 2^{n/100}` once `n ≥ n₀(h)`.
-/
theorem FCE_lemma
    (hH : H₂ F ≤ (h : ℝ))
    (hn : n ≥ n₀ h) :
    (coverFamily (n := n) (h := h) F hH).card <
      Nat.pow 2 (n / 100) := by
  -- Combines `coverFamily_card_bound` from `cover.lean`
  -- with the arithmetic lemma above.
  have h1 :=
    Cover.coverFamily_card_bound (n := n) (h := h) F hH
  have h2 :=
    mBound_lt_subexp (h := h) (n := n) hn
  exact lt_of_le_of_lt h1 h2

end Bound
