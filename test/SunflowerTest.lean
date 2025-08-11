import Pnp2.Sunflower.Sunflower
import Pnp2.Sunflower.Aux

open Sunflower
open scoped BigOperators

namespace SunflowerTest

open Finset

/-- Simple check of the double-counting lemma on a tiny family of two
    singletons. -/
example :
    let 𝓢 : Finset (Finset ℕ) := { {0}, {1} }
    ∑ x ∈ 𝓢.unions, (slice 𝓢 x).card = 1 * 𝓢.card := by
  classical
  intro 𝓢
  have h_w : ∀ A ∈ 𝓢, A.card = 1 := by
    intro A hA
    have hA' := by simpa [𝓢] using hA
    rcases hA' with h0 | h1
    · simp [h0]
    · simp [h1]
  simpa using
    (Sunflower.sum_card_slices_eq_w_mul_card (𝓢 := 𝓢) (w := 1) h_w)

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
  have hbig : F.card > Sunflower.threshold 1 2 := by
    simp [F, Sunflower.threshold]
  simpa [F] using
    SunflowerFam.exists_of_large_family_classic
      (n := 2) (w := 1) (t := 2) (F := F)
      hw ht hcard hbig

/-- `sum_slice_inter` specialises to the expected value on a simple
family and ambient set. -/
example :
    let 𝓢 : Finset (Finset ℕ) := { {0}, {1} }
    let U : Finset ℕ := {0, 1}
    ∑ x ∈ U, (slice 𝓢 x).card = ∑ A ∈ 𝓢, (A ∩ U).card := by
  classical
  intro 𝓢 U
  -- The general lemma handles this computation directly.
  simpa [𝓢, U] using
    (Sunflower.sum_slice_inter (𝓢 := 𝓢) (U := U))

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
