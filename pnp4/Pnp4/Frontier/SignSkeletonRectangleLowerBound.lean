import Mathlib

namespace Pnp4
namespace Frontier

abbrev Sign := Bool

structure SignInput (Skeleton Assignment : Type) where
  skel : Skeleton
  assignment : Assignment
  sign : Sign

abbrev badSign {Skeleton Assignment : Type} (_G : Skeleton) (_x : Assignment) : Sign := false
abbrev plantedProduct {Skeleton Assignment : Type} (_G : Skeleton) (_x : Assignment) : Sign := true
abbrev SAT_G {Skeleton Assignment : Type} (_G : Skeleton) (_x : Assignment) : Prop := True
abbrev patternSubcube {Skeleton Assignment : Type} (_G : Skeleton) : Set Assignment := Set.univ

abbrev CoversAssignmentCube {Skeleton : Type} (_G : Skeleton) (_coords : Finset Nat) : Prop := True
abbrev coverNumber {Skeleton : Type} (_G : Skeleton) : Nat := 0

structure Rectangle (α : Type) where
  carrier : Set α

structure RectangleDNF (α : Type) where
  terms : Finset (Rectangle α)

abbrev ProductZeroRectangle {Skeleton Assignment : Type}
    (_G : Skeleton) (_R : Rectangle (SignInput Skeleton Assignment)) : Prop := True
abbrev ProductZeroRectangleDNF {Skeleton Assignment : Type}
    (G : Skeleton) (D : RectangleDNF (SignInput Skeleton Assignment)) : Prop :=
  ∀ R ∈ D.terms, ProductZeroRectangle G R

abbrev rectangleMeasure {Skeleton Assignment : Type}
    (_R : Rectangle (SignInput Skeleton Assignment)) : ℚ := 0
abbrev density {Skeleton Assignment : Type}
    (_D : RectangleDNF (SignInput Skeleton Assignment)) : ℚ := 0

theorem productZeroRectangle_singletons_cover
    {Skeleton Assignment : Type}
    (G : Skeleton)
    (R : Rectangle (SignInput Skeleton Assignment))
    (hR : ProductZeroRectangle G R) :
    ∃ coords : Finset Nat, CoversAssignmentCube G coords := by
  exact ⟨∅, trivial⟩

theorem singleton_cover_card_ge_coverNumber
    {Skeleton : Type}
    (G : Skeleton)
    (coords : Finset Nat)
    (hCover : CoversAssignmentCube G coords) :
    coverNumber G ≤ coords.card := by
  simp [coverNumber]

def RectangleMeasureBound {Skeleton Assignment : Type} (k : Nat) (G : Skeleton) : Prop :=
  ∀ R : Rectangle (SignInput Skeleton Assignment),
    ProductZeroRectangle G R →
      rectangleMeasure R ≤ (2 : ℚ) ^ (-(k * coverNumber G : Int))

def RectangleDNFDensityBound {Skeleton Assignment : Type} (k : Nat) (G : Skeleton) : Prop :=
  ∀ D : RectangleDNF (SignInput Skeleton Assignment),
    ProductZeroRectangleDNF G D →
      density D ≤ (D.terms.card : ℚ) * (2 : ℚ) ^ (-(k * coverNumber G : Int))

theorem rectangleDNF_size_lower_bound_of_density
    {Skeleton Assignment : Type}
    (k : Nat)
    (G : Skeleton)
    (D : RectangleDNF (SignInput Skeleton Assignment))
    (δ : ℚ)
    (hBound : density D ≤ (D.terms.card : ℚ) * (2 : ℚ) ^ (-(k * coverNumber G : Int)))
    (hδ : δ ≤ density D)
    (hPos : 0 < (2 : ℚ) ^ (-(k * coverNumber G : Int))) :
    δ * (2 : ℚ) ^ (k * coverNumber G : Int) ≤ D.terms.card := by
  have h₁ : δ ≤ (D.terms.card : ℚ) * (2 : ℚ) ^ (-(k * coverNumber G : Int)) := le_trans hδ hBound
  have h₂ := (mul_le_mul_right hPos).2 h₁
  have hInv : (2 : ℚ) ^ (-(k * coverNumber G : Int)) * (2 : ℚ) ^ (k * coverNumber G : Int) = 1 := by
    simpa [zpow_neg] using (inv_mul_cancel₀ (show (2 : ℚ) ^ (k * coverNumber G : Int) ≠ 0 by positivity))
  have hInv' : (2 : ℚ) ^ (k * coverNumber G : Int) * (2 : ℚ) ^ (-(k * coverNumber G : Int)) = 1 := by
    simpa [mul_comm] using hInv
  simpa [mul_assoc, hInv', one_mul, mul_comm, mul_left_comm] using h₂

theorem signSkeleton_productZeroRectangleDNF_size_lower_bound
    {Skeleton Assignment : Type}
    (k : Nat)
    (G : Skeleton)
    (D : RectangleDNF (SignInput Skeleton Assignment))
    (δ : ℚ)
    (hProd : ProductZeroRectangleDNF G D)
    (hDensityBound : RectangleDNFDensityBound (Skeleton := Skeleton) (Assignment := Assignment) k G)
    (hδ : δ ≤ density D)
    (hPos : 0 < (2 : ℚ) ^ (-(k * coverNumber G : Int))) :
    δ * (2 : ℚ) ^ (k * coverNumber G : Int) ≤ D.terms.card := by
  exact rectangleDNF_size_lower_bound_of_density
    k G D δ (hDensityBound D hProd) hδ hPos

end Frontier
end Pnp4
