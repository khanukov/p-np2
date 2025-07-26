import Pnp2.Sunflower.Sunflower

open Sunflower

namespace SunflowerTest

open Finset

/-- A simple family of two singletons forms a sunflower.
    We verify that `exists_of_large_family` can produce the structure
    for this tiny example. -/
example :
    let F : Finset (Petal 2) := { {0}, {1} }
    ∃ S : SunflowerFam 2 2, S.petals ⊆ F := by
  classical
  intro F
  have hw : 0 < (1 : ℕ) := by decide
  have ht : 2 ≤ (2 : ℕ) := by decide
  have hcard : ∀ S ∈ F, S.card = 1 := by
    intro S hS
    have hS' := by
      simpa [F] using hS
    rcases hS' with h0 | h1
    · simpa [h0]
    · simpa [h1]
  have hbig : F.card > Nat.factorial (2 - 1) * 1 ^ 2 := by
    simp [F]
  simpa [F] using
    SunflowerFam.exists_of_large_family
      (n := 2) (w := 1) (t := 2) (F := F)
      hw ht hcard hbig

end SunflowerTest
