import Pnp2.cover
import Pnp2.BoolFunc

open BoolFunc
open Classical

namespace SunflowerTest

abbrev trip {n : ℕ} (i j k : Fin n) : BFunc n := fun x => x i && x j && x k

noncomputable def fSet : Family 6 :=
  { trip 0 1 2, trip 0 1 3, trip 0 1 4, trip 0 1 5,
    trip 0 2 3, trip 0 2 4, trip 0 2 5, trip 0 3 4,
    trip 0 3 5, trip 0 4 5, trip 1 2 3, trip 1 2 4,
    trip 1 2 5, trip 1 3 4, trip 1 3 5 }

lemma supports_card_fset : (Family.supports fSet).card = 15 := by
  admit

lemma support_card_three :
  ∀ f ∈ fSet, (support f).card = 3 := by
  admit

lemma sunflower_step_example :
    ∃ (R : Subcube 6),
      (fSet.filter fun f ↦ ∀ x, x ∈ₛ R → f x = true).card ≥ 2 ∧ 1 ≤ R.dimension :=
by
  have hp : 0 < 3 := by decide
  have ht : 2 ≤ 2 := by decide
  have h_big : (2 - 1).factorial * 3 ^ 2 < (Family.supports fSet).card := by
    have hc := supports_card_fset
    have : (Family.supports fSet).card = 15 := hc
    have : 9 < 15 := by decide
    simpa [this]
  have h_support := support_card_three
  simpa using
    sunflower_step (F := fSet) (p := 3) (t := 2) hp ht h_big h_support

end SunflowerTest
end SunflowerStep
