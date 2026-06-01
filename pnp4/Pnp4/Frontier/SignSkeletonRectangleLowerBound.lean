import Mathlib

namespace Pnp4
namespace Frontier

abbrev plantedProduct
    {Assignment Coord Sign : Type}
    (badSign : Assignment → Coord → Sign)
    (σ : Coord → Sign)
    (a : Assignment) : Prop :=
  ∀ i : Coord, σ i ≠ badSign a i

def patternSubcube
    {Assignment Coord Sign : Type}
    (badSign : Assignment → Coord → Sign)
    (i : Coord)
    (τ : Sign) : Set Assignment :=
  {a | badSign a i = τ}

structure Rectangle (Coord Sign : Type) where
  singletonCoords : Finset Coord
  fixedSign : Coord → Sign
  carrier : Set (Coord → Sign)
  mem_iff : ∀ σ : Coord → Sign,
    σ ∈ carrier ↔ ∀ i ∈ singletonCoords, σ i = fixedSign i

abbrev InRectangle {Coord Sign : Type} (R : Rectangle Coord Sign) (σ : Coord → Sign) : Prop :=
  σ ∈ R.carrier

abbrev ProductZeroRectangle
    {Assignment Coord Sign : Type}
    (badSign : Assignment → Coord → Sign)
    (R : Rectangle Coord Sign) : Prop :=
  ∀ a σ, InRectangle R σ → plantedProduct badSign σ a → False

abbrev CoverLowerBound
    {Assignment Coord Sign : Type}
    (badSign : Assignment → Coord → Sign)
    (T : Nat) : Prop :=
  ∀ S : Finset Coord,
    (∀ a : Assignment, ∃ i ∈ S, ∃ τ : Sign, a ∈ patternSubcube badSign i τ) →
      T ≤ S.card

theorem productZeroRectangle_singletons_cover
    {Assignment Coord Sign : Type}
    [DecidableEq Coord]
    (badSign : Assignment → Coord → Sign)
    (avoidBad : Assignment → Coord → Sign)
    (hAvoid : ∀ a i, avoidBad a i ≠ badSign a i)
    (R : Rectangle Coord Sign)
    (hNonempty : ∃ σ0, InRectangle R σ0)
    (hZero : ProductZeroRectangle badSign R) :
    ∀ a : Assignment, ∃ i ∈ R.singletonCoords, R.fixedSign i = badSign a i := by
  intro a
  by_contra hNoHit
  rcases hNonempty with ⟨σ0, hσ0⟩
  let σa : Coord → Sign := fun i => if hi : i ∈ R.singletonCoords then R.fixedSign i else avoidBad a i
  have hσa_mem : InRectangle R σa := by
    change σa ∈ R.carrier
    rw [R.mem_iff]
    intro i hi
    simp [σa, hi]
  have hPlant : plantedProduct badSign σa a := by
    intro i
    by_cases hi : i ∈ R.singletonCoords
    · have hneq : R.fixedSign i ≠ badSign a i := by
        exact fun hEq => hNoHit ⟨i, hi, hEq⟩
      simpa [σa, hi] using hneq
    · simpa [σa, hi] using hAvoid a i
  exact hZero a σa hσa_mem hPlant

theorem singleton_cover_card_ge_coverNumber
    {Assignment Coord Sign : Type}
    [DecidableEq Coord]
    (badSign : Assignment → Coord → Sign)
    (T : Nat)
    (hCoverLB : CoverLowerBound badSign T)
    (R : Rectangle Coord Sign)
    (hCovers : ∀ a : Assignment, ∃ i ∈ R.singletonCoords, R.fixedSign i = badSign a i) :
    T ≤ R.singletonCoords.card := by
  apply hCoverLB
  intro a
  rcases hCovers a with ⟨i, hi, hEq⟩
  refine ⟨i, hi, R.fixedSign i, ?_⟩
  simpa [patternSubcube] using hEq.symm

abbrev rectangleMeasure {Coord Sign : Type} (signCard : Nat) (R : Rectangle Coord Sign) : ℚ :=
  1 / (signCard : ℚ) ^ R.singletonCoords.card

theorem rectangleMeasure_le_pow_two
    {Coord Sign : Type}
    [DecidableEq Coord]
    (k T signCard : Nat)
    (hSignCard : signCard = 2 ^ k)
    (R : Rectangle Coord Sign)
    (hCard : T ≤ R.singletonCoords.card) :
    rectangleMeasure signCard R ≤ 1 / (2 : ℚ) ^ (k * T) := by
  have hpow_nat : (2 ^ k) ^ T ≤ (2 ^ k) ^ R.singletonCoords.card := by
    exact Nat.pow_le_pow_right (by positivity) hCard
  have hpow_q : ((2 : ℚ) ^ k) ^ T ≤ ((2 : ℚ) ^ k) ^ R.singletonCoords.card := by
    exact_mod_cast hpow_nat
  have hdenom : (2 : ℚ) ^ (k * T) ≤ (2 : ℚ) ^ (k * R.singletonCoords.card) := by
    simpa [pow_mul] using hpow_q
  have hpos : 0 < (2 : ℚ) ^ (k * T) := by positivity
  have hpos' : 0 < (2 : ℚ) ^ (k * R.singletonCoords.card) := by positivity
  have hrecip : (1 / (2 : ℚ) ^ (k * R.singletonCoords.card)) ≤ (1 / (2 : ℚ) ^ (k * T)) := by
    exact one_div_le_one_div_of_le hpos hdenom
  simpa [rectangleMeasure, hSignCard, pow_mul, one_div] using hrecip

end Frontier
end Pnp4
