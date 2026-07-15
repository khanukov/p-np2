import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDSuffixLaplacian
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Per-vertex masked restriction bound for a finite uFBDD

This module combines the compatible-prefix homogeneous slice with the bounded
suffix coordinate Laplacian at one fixed uFBDD vertex.  Exact factorization
under a fixed Boolean base and mask reduces the product contribution to the
prefix contribution.  The existing finite Claim-18 endpoint then gives a
squared `p^k` bound after averaging over the explicit `D` and `T` seed types.

This is a per-vertex theorem only.  It does not regroup the full high-degree
Fourier tail as a vertex sum, control cross-vertex terms, sum over vertices,
or prove a program-level one-round fooling theorem.
-/

namespace FiniteBooleanPerVertexRestrictionBound

open scoped BigOperators
open FiniteBooleanRestrictionMoment

/-! ## Elementary exact finite-average inequalities -/

/-- The exact finite average of a constant over a nonempty finite type is the
constant. -/
theorem finiteAverage_const {Seed : Type*}
    [Fintype Seed] [Nonempty Seed] (value : ℚ) :
    finiteAverage (fun _seed : Seed => value) = value := by
  simp [finiteAverage]

/-- Exact finite averages preserve pointwise order on a nonempty finite
type. -/
theorem finiteAverage_mono {Seed : Type*}
    [Fintype Seed] [Nonempty Seed] {f g : Seed → ℚ}
    (h : ∀ seed, f seed ≤ g seed) :
    finiteAverage f ≤ finiteAverage g := by
  have hcard : (0 : ℚ) < (Fintype.card Seed : ℚ) := by
    exact_mod_cast Fintype.card_pos
  unfold finiteAverage
  rw [div_le_div_iff_of_pos_right hcard]
  exact Finset.sum_le_sum fun seed _ => h seed

/-- A pointwise nonnegative rational function has nonnegative exact finite
average. -/
theorem finiteAverage_nonneg {Seed : Type*}
    [Fintype Seed] [Nonempty Seed] {f : Seed → ℚ}
    (h : ∀ seed, 0 ≤ f seed) :
    0 ≤ finiteAverage f := by
  calc
    0 = finiteAverage (fun _seed : Seed => (0 : ℚ)) := by
      rw [finiteAverage_const]
    _ ≤ finiteAverage f := finiteAverage_mono h

/-- Triangle inequality for the exact finite average. -/
theorem abs_finiteAverage_le_finiteAverage_abs
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (f : Seed → ℚ) :
    |finiteAverage f| ≤ finiteAverage (fun seed => |f seed|) := by
  have hcard : (0 : ℚ) < (Fintype.card Seed : ℚ) := by
    exact_mod_cast Fintype.card_pos
  unfold finiteAverage
  rw [abs_div, abs_of_pos hcard]
  rw [div_le_div_iff_of_pos_right hcard]
  exact Finset.abs_sum_le_sum_abs f Finset.univ

/-- A pointwise absolute-value bound passes to the exact finite average. -/
theorem abs_finiteAverage_le_of_pointwise_abs_le
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (f : Seed → ℚ) (bound : ℚ)
    (hbound : ∀ seed, |f seed| ≤ bound) :
    |finiteAverage f| ≤ bound := by
  calc
    |finiteAverage f| ≤ finiteAverage (fun seed => |f seed|) :=
      abs_finiteAverage_le_finiteAverage_abs f
    _ ≤ finiteAverage (fun _seed : Seed => bound) :=
      finiteAverage_mono hbound
    _ = bound := finiteAverage_const bound

end FiniteBooleanPerVertexRestrictionBound

namespace FiniteUnambiguousFBDD

open FiniteBooleanRestrictionMoment
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanMaskedProductFactorization
open FiniteBooleanFourierEnergy

/-! ## A fixed suffix factor under a fixed mask -/

/-- The masked uniform average of the suffix Laplacian retains the sharper
absolute-value bound `1/2`. -/
theorem abs_finiteAverage_suffixLaplacian_maskedInput_le_half
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (base mask : Fin n → Bool) :
    |finiteAverage (fun uniform : Fin n → Bool =>
      B.suffixLaplacian vertex (maskedInput base mask uniform))| ≤
        (1 : ℚ) / 2 := by
  exact abs_finiteAverage_le_of_pointwise_abs_le _ ((1 : ℚ) / 2)
    (fun uniform =>
      B.abs_suffixLaplacian_le_half vertex (maskedInput base mask uniform))

/-- Paper-strength corollary of the sharper masked suffix-average bound. -/
theorem abs_finiteAverage_suffixLaplacian_maskedInput_le_one
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (base mask : Fin n → Bool) :
    |finiteAverage (fun uniform : Fin n → Bool =>
      B.suffixLaplacian vertex (maskedInput base mask uniform))| ≤
        (1 : ℚ) := by
  exact (B.abs_finiteAverage_suffixLaplacian_maskedInput_le_half
    vertex base mask).trans (by norm_num)

/-! ## Per-vertex product bounds -/

/-- At one fixed syntactically read-once vertex and one fixed base/mask pair,
the bounded suffix Laplacian cannot enlarge the absolute masked average of the
compatible-prefix homogeneous slice. -/
theorem abs_finiteAverage_prefixSlice_mul_suffixLaplacian_maskedInput_le
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce) (vertex : B.Vertex)
    (base mask : Fin n → Bool) :
    |finiteAverage (fun uniform : Fin n → Bool =>
      B.ratCompatiblePrefixHomogeneousSlice vertex k
          (maskedInput base mask uniform) *
        B.suffixLaplacian vertex (maskedInput base mask uniform))| ≤
      |finiteAverage (fun uniform : Fin n → Bool =>
        B.ratCompatiblePrefixHomogeneousSlice vertex k
          (maskedInput base mask uniform))| := by
  exact abs_finiteAverage_mul_maskedInput_le
    (B.ratCompatiblePrefixHomogeneousSlice_dependsOnlyOn_preVars vertex)
    (B.suffixLaplacian_dependsOnlyOn_postVars vertex)
    (B.preVars_disjoint_postVars hreadOnce vertex)
    base mask
    (B.abs_finiteAverage_suffixLaplacian_maskedInput_le_one
      vertex base mask)

/-- Squared per-vertex product-moment bound.  Under the same explicit source
moment hypotheses as the finite Claim-18 prefix endpoint, multiplying by the
bounded disjoint suffix Laplacian preserves the `p^k` upper bound. -/
theorem prefixSlice_mul_suffixLaplacian_restriction_absMoment_sq_le_pow
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce) (vertex : B.Vertex)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed =>
            FiniteBooleanFourier.character alpha (D d) *
              FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ k) :
    (finiteAverage (fun seed : DSeed × TSeed =>
      |finiteAverage (fun uniform : Fin n → Bool =>
        B.ratCompatiblePrefixHomogeneousSlice vertex k
            (maskedInput (D seed.1) (T seed.2) uniform) *
          B.suffixLaplacian vertex
            (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      p ^ k := by
  let productMoment : ℚ :=
    finiteAverage (fun seed : DSeed × TSeed =>
      |finiteAverage (fun uniform : Fin n → Bool =>
        B.ratCompatiblePrefixHomogeneousSlice vertex k
            (maskedInput (D seed.1) (T seed.2) uniform) *
          B.suffixLaplacian vertex
            (maskedInput (D seed.1) (T seed.2) uniform))|)
  let prefixMoment : ℚ :=
    finiteAverage (fun seed : DSeed × TSeed =>
      |finiteAverage (fun uniform : Fin n → Bool =>
        B.ratCompatiblePrefixHomogeneousSlice vertex k
          (maskedInput (D seed.1) (T seed.2) uniform))|)
  have hmoment : productMoment ≤ prefixMoment := by
    apply finiteAverage_mono
    intro seed
    exact B.abs_finiteAverage_prefixSlice_mul_suffixLaplacian_maskedInput_le
      hreadOnce vertex (D seed.1) (T seed.2)
  have hproductNonneg : 0 ≤ productMoment := by
    apply finiteAverage_nonneg
    intro seed
    exact abs_nonneg _
  have hprefixNonneg : 0 ≤ prefixMoment := by
    apply finiteAverage_nonneg
    intro seed
    exact abs_nonneg _
  have hsquare : productMoment ^ 2 ≤ prefixMoment ^ 2 := by
    nlinarith
  have hprefix : prefixMoment ^ 2 ≤ p ^ k := by
    dsimp [prefixMoment]
    simpa only [ratCompatiblePrefixHomogeneousSlice] using
      (FiniteBooleanFourierEnergy.ratCompatiblePrefixIndicator_restriction_absMoment_sq_le_pow
        B vertex D T p hp hDOrthogonal hTMask)
  change productMoment ^ 2 ≤ p ^ k
  exact hsquare.trans hprefix

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
