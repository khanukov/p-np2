import Pnp2.Sunflower.Sunflower

open Sunflower

namespace SunflowerTest

open Finset

/-- A simple family of two singletons forms a sunflower.
    We verify that `exists_of_large_family_classic` can produce the structure
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
    · simp [h0]
    · simp [h1]
  have hbig : F.card > (2 - 1) ^ 1 * Nat.factorial 1 := by
    simp [F]
  simpa [F] using
    SunflowerFam.exists_of_large_family_classic
      (n := 2) (w := 1) (t := 2) (F := F)
      hw ht hcard hbig

/-- The specialised `sunflower_exists_two` also witnesses a sunflower
    in this basic family. -/
example :
    let F : Finset (Petal 2) := { {0}, {1} }
    HasSunflower F 1 2 := by
  classical
  intro F
  have hw : 0 < (1 : ℕ) := by decide
  have hlarge : 1 < F.card := by simp [F]
  have hcard : ∀ S ∈ F, S.card = 1 := by
    intro S hS
    have hS' := by simpa [F] using hS
    rcases hS' with h0 | h1
    · simp [h0]
    · simp [h1]
  simpa [F] using
    sunflower_exists_two (𝓢 := F) (w := 1) hw hlarge hcard

end SunflowerTest
