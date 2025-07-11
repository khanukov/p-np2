import Pnp2.cover
import Pnp2.BoolFunc

open BoolFunc
open Classical

namespace SunflowerTest

abbrev trip {n : ℕ} (i j k : Fin n) : BFunc n := fun x => x i && x j && x k

lemma support_trip_card {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (support (trip (n:=n) i j k)).card = 3 := by
  classical
  -- Each coordinate `i`, `j`, `k` influences the function.
  have hi : i ∈ support (trip i j k) := by
    let x : Point n := fun l => if l = i then false else true
    have hx : trip i j k x = false := by
      simp [trip, x, hij, hik, hjk]
    have hx' : trip i j k (Point.update x i (!x i)) = true := by
      simp [trip, x, Point.update, hij, hik, hjk]
    exact mem_support_iff.mpr ⟨x, by simpa [hx, hx']⟩
  have hj : j ∈ support (trip i j k) := by
    let x : Point n := fun l => if l = j then false else true
    have hx : trip i j k x = false := by
      simp [trip, x, hij.symm, hik, hjk]
    have hx' : trip i j k (Point.update x j (!x j)) = true := by
      simp [trip, x, Point.update, hij.symm, hik, hjk]
    exact mem_support_iff.mpr ⟨x, by simpa [hx, hx']⟩
  have hk : k ∈ support (trip i j k) := by
    let x : Point n := fun l => if l = k then false else true
    have hx : trip i j k x = false := by
      simp [trip, x, hij, hik.symm, hjk.symm]
    have hx' : trip i j k (Point.update x k (!x k)) = true := by
      simp [trip, x, Point.update, hij, hik.symm, hjk.symm]
    exact mem_support_iff.mpr ⟨x, by simpa [hx, hx']⟩
  -- No other coordinate matters.
  have hsubset : support (trip i j k) ⊆ {i, j, k} := by
    intro l hl
    rcases mem_support_iff.mp hl with ⟨x, hx⟩
    by_cases hli : l = i
    · simp [hli]
    by_cases hlj : l = j
    · simp [hlj]
    by_cases hlk : l = k
    · simp [hlk]
    have : trip i j k x = trip i j k (Point.update x l (!x l)) := by
      simp [trip, Point.update, hli, hlj, hlk]
    exact False.elim (hx this)
  -- Now compare cardinals using the above subset and membership facts.
  have hcard_le : (support (trip i j k)).card ≤ 3 := by
    have h := Finset.card_le_of_subset hsubset
    have : ({i, j, k} : Finset (Fin n)).card = 3 := by
      simp [Finset.card_insert, hij, hik, hjk]
    simpa [this] using h
  have hmem : {i, j, k} ⊆ support (trip i j k) := by
    intro l hl
    rcases Finset.mem_insert.mp hl with h | hl
    · simpa [h] using hi
    rcases Finset.mem_insert.mp hl with h | hl
    · simpa [h] using hj
    rcases Finset.mem_singleton.mp hl with h
    simpa [h] using hk
  have hcard_ge : 3 ≤ (support (trip i j k)).card := by
    have h := Finset.card_le_of_subset hmem
    have hcard : ({i, j, k} : Finset (Fin n)).card = 3 := by
      simp [Finset.card_insert, hij, hik, hjk]
    simpa [hcard] using h
  exact le_antisymm hcard_le hcard_ge

noncomputable def fSet : Family 6 :=
  { trip 0 1 2, trip 0 1 3, trip 0 1 4, trip 0 1 5,
    trip 0 2 3, trip 0 2 4, trip 0 2 5, trip 0 3 4,
    trip 0 3 5, trip 0 4 5, trip 1 2 3, trip 1 2 4,
    trip 1 2 5, trip 1 3 4, trip 1 3 5 }

/-- The set of supports of `fSet` consists of the 15 triples used to
define it.  Hence its cardinality is 15. -/
lemma supports_card_fset : (Family.supports fSet).card = 15 := by
  classical
  -- `simp` expands `Family.supports` and computes the resulting finite set.
  simp [fSet, Family.supports, support_trip_card, Finset.card_image]

/-- Every function in `fSet` depends on exactly three coordinates. -/
lemma support_card_three :
  ∀ f ∈ fSet, (support f).card = 3 := by
  classical
  decide

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
