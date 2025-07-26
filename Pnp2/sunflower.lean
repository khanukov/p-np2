import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Pnp2.Sunflower.Sunflower

/-! `sunflower.lean`
===================

This small module re-exports the definitions and main lemma from
`Pnp2.Sunflower.Sunflower`.  Downstream files can simply `import
Pnp2.sunflower` to make use of the classical sunflower lemma without
needing to remember the longer path.  No additional functionality is
introduced here; we only provide a convenient alias.
-/

namespace Sunflower

export Pnp2.Sunflower.Sunflower (IsSunflower HasSunflower)

/-- Re-export of `Sunflower.sunflower_exists` with a shorter path. -/
theorem sunflower_exists
    {α : Type} [DecidableEq α]
    (𝓢 : Finset (Finset α)) (w p : ℕ)
    (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (p - 1).factorial * w ^ p < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w p :=
  Pnp2.Sunflower.Sunflower.sunflower_exists
    (𝓢 := 𝓢) (w := w) (p := p) hw hp h_size h_w

end Sunflower

