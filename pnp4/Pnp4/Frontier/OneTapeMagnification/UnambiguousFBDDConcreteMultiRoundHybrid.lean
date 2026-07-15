import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDAffineRestrictionIteration
import Pnp4.Frontier.OneTapeMagnification.DPTWIndependentSurvival

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Concrete finite multi-round hybrids for affine uFBDD restrictions

This file turns the fixed-prefix one-round theorem into an actual finite
multi-round hybrid.  A seed of depth `r` is an explicitly finite nested
product.  Its associated list is ordered from the outermost restriction to
the innermost restriction.  The hybrid value averages over all such prefixes
and then over a final uniform Boolean input.

The successor identity conditions on the first `r` (outer) rounds and adds
one independent innermost round.  Consequently the fixed-prefix theorem
applies pointwise before the prefix average is taken.  The resulting adjacent
bound and its telescoping corollaries have no unformalized probabilistic
conditioning step.

The last theorem records the precise interface to the existing DPTW
zero-tail survivor estimate.  The only extra premise there is an equality
identifying the nested-product hybrid with the flattened DPTW packed-tail
average.  Proving that equality for concrete DPTW seed primitives is a seed
layout/reindexing obligation, not part of the uFBDD Fourier estimate.
-/

open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanPerVertexRestrictionBound

namespace FiniteAffineRestrictionHybrid

/-! ## Explicit finite prefixes -/

universe u

/-- A depth-`r` independent seed prefix, associated to the left.  Thus a
successor prefix is an old outer prefix paired with one new innermost seed. -/
def Seeds (Seed : Type u) : Nat -> Type u
  | 0 => PUnit
  | r + 1 => Prod (Seeds Seed r) Seed

/-- Every explicit prefix is finite when the one-round seed type is finite. -/
instance seedsFintype (Seed : Type*) [Fintype Seed] :
    (r : Nat) -> Fintype (Seeds Seed r)
  | 0 => inferInstanceAs (Fintype PUnit)
  | r + 1 =>
      letI : Fintype (Seeds Seed r) := seedsFintype Seed r
      inferInstanceAs (Fintype (Prod (Seeds Seed r) Seed))

/-- Every explicit prefix is inhabited when the one-round seed type is. -/
instance seedsNonempty (Seed : Type*) [Nonempty Seed] :
    (r : Nat) -> Nonempty (Seeds Seed r)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | r + 1 =>
      letI : Nonempty (Seeds Seed r) := seedsNonempty Seed r
      inferInstanceAs (Nonempty (Prod (Seeds Seed r) Seed))

/-- Turn one independent base/mask seed pair into an affine round. -/
def roundOfSeed {n : Nat} {DSeed TSeed : Type*}
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (seed : Prod DSeed TSeed) : AffineRestrictionRound n where
  base := D seed.1
  mask := T seed.2

/-- Turn a nested seed prefix into its outer-to-inner affine round list. -/
def roundsOfSeeds {n : Nat} {DSeed TSeed : Type*}
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    (r : Nat) -> Seeds (Prod DSeed TSeed) r ->
      List (AffineRestrictionRound n)
  | 0, _ => []
  | r + 1, seeds =>
      roundsOfSeeds D T r seeds.1 ++ [roundOfSeed D T seeds.2]

@[simp]
theorem roundsOfSeeds_zero {n : Nat} {DSeed TSeed : Type*}
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (seed : Seeds (Prod DSeed TSeed) 0) :
    roundsOfSeeds D T 0 seed = [] := rfl

@[simp]
theorem roundsOfSeeds_succ {n r : Nat} {DSeed TSeed : Type*}
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (oldSeeds : Seeds (Prod DSeed TSeed) r) (seed : Prod DSeed TSeed) :
    roundsOfSeeds D T (r + 1) (oldSeeds, seed) =
      roundsOfSeeds D T r oldSeeds ++ [roundOfSeed D T seed] := rfl

/-! ## Exact list and program semantics -/

/-- Recursive masked composition respects list append. -/
theorem applyAffineRestrictionRounds_append {n : Nat}
    (outer inner : List (AffineRestrictionRound n))
    (input : Fin n -> Bool) :
    applyAffineRestrictionRounds (outer ++ inner) input =
      applyAffineRestrictionRounds outer
        (applyAffineRestrictionRounds inner input) := by
  induction outer with
  | nil => rfl
  | cons round outer ih =>
      simp only [List.cons_append, applyAffineRestrictionRounds]
      rw [ih]

/-- Appending rounds to a transformed program is semantically the same as
feeding their recursively masked input to the fixed-prefix program. -/
theorem affinePaddedRestrictByRounds_append_ratAcceptanceIndicator_eq
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (outer inner : List (AffineRestrictionRound n))
    (input : Fin n -> Bool) :
    (B.affinePaddedRestrictByRounds (outer ++ inner)).ratAcceptanceIndicator
        input =
      (B.affinePaddedRestrictByRounds outer).ratAcceptanceIndicator
        (applyAffineRestrictionRounds inner input) := by
  rw [B.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
  rw [B.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
  rw [applyAffineRestrictionRounds_append]

/-- The singleton append identity in the exact `maskedInput` form used by
the one-round theorem. -/
theorem affinePaddedRestrictByRounds_append_one_ratAcceptanceIndicator_eq
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (outer : List (AffineRestrictionRound n))
    (round : AffineRestrictionRound n) (input : Fin n -> Bool) :
    (B.affinePaddedRestrictByRounds (outer ++ [round])).ratAcceptanceIndicator
        input =
      (B.affinePaddedRestrictByRounds outer).ratAcceptanceIndicator
        (maskedInput round.base round.mask input) := by
  rw [affinePaddedRestrictByRounds_append_ratAcceptanceIndicator_eq]
  rfl

/-! ## The concrete nested-average hybrid -/

/-- The depth-`r` hybrid: average over `r` independent affine round seeds,
then over a final uniform input. -/
noncomputable def value {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    (B : FiniteUnambiguousFBDD n)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (r : Nat) : Rat :=
  finiteAverage (fun seeds : Seeds (Prod DSeed TSeed) r =>
    finiteAverage
      (B.affinePaddedRestrictByRounds
        (roundsOfSeeds D T r seeds)).ratAcceptanceIndicator)

/-- The program-transform definition is exactly the advertised nested
masked-input average. -/
theorem value_eq_nested_maskedInput_average
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    (B : FiniteUnambiguousFBDD n)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (r : Nat) :
    value B D T r =
      finiteAverage (fun seeds : Seeds (Prod DSeed TSeed) r =>
        finiteAverage (fun input : Fin n -> Bool =>
          B.ratAcceptanceIndicator
            (applyAffineRestrictionRounds
              (roundsOfSeeds D T r seeds) input))) := by
  unfold value
  apply finiteAverage_congr
  intro seeds
  apply finiteAverage_congr
  intro input
  exact B.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq
    (roundsOfSeeds D T r seeds) input

/-- At depth zero the concrete hybrid is the true uniform acceptance
average. -/
theorem value_zero
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    value B D T 0 = finiteAverage B.ratAcceptanceIndicator := by
  unfold value
  change finiteAverage (fun _seed : PUnit =>
    finiteAverage B.ratAcceptanceIndicator) = _
  exact finiteAverage_const _

/-- Conditioning on the old outer prefix exposes precisely the one-round
average for the fixed-prefix transformed program. -/
theorem value_succ_eq_prefixAverage_oneRound
    {n r : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    (B : FiniteUnambiguousFBDD n)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    value B D T (r + 1) =
      finiteAverage (fun oldSeeds : Seeds (Prod DSeed TSeed) r =>
        finiteAverage (fun seed : Prod DSeed TSeed =>
          finiteAverage (fun input : Fin n -> Bool =>
            (B.affinePaddedRestrictByRounds
              (roundsOfSeeds D T r oldSeeds)).ratAcceptanceIndicator
                (maskedInput (D seed.1) (T seed.2) input)))) := by
  calc
    value B D T (r + 1) =
        finiteAverage (fun oldSeeds : Seeds (Prod DSeed TSeed) r =>
          finiteAverage (fun seed : Prod DSeed TSeed =>
            finiteAverage
              (B.affinePaddedRestrictByRounds
                (roundsOfSeeds D T (r + 1)
                  (oldSeeds, seed))).ratAcceptanceIndicator)) := by
      unfold value
      exact finiteAverage_prod_eq_iterated
        (Left := Seeds (Prod DSeed TSeed) r)
        (Right := Prod DSeed TSeed)
        (fun oldSeeds seed =>
          finiteAverage
            (B.affinePaddedRestrictByRounds
              (roundsOfSeeds D T (r + 1)
                (oldSeeds, seed))).ratAcceptanceIndicator)
    _ = _ := by
      apply finiteAverage_congr
      intro oldSeeds
      apply finiteAverage_congr
      intro seed
      apply finiteAverage_congr
      intro input
      exact affinePaddedRestrictByRounds_append_one_ratAcceptanceIndicator_eq
        B (roundsOfSeeds D T r oldSeeds) (roundOfSeed D T seed) input

/-! ## Adjacent conditioning and telescoping -/

/-- Every adjacent pair of concrete hybrids differs by at most the original
vertex factor times `p^m`.  The absolute value is outside all seed averages;
this is the valid signed-cancellation form of the one-round theorem. -/
theorem abs_value_succ_sub_value_le_card_mul_pow
    {n m r : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
      (4 * m) D)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p T) :
    |value B D T (r + 1) - value B D T r| <=
      (Fintype.card B.Vertex : Rat) * p ^ m := by
  rw [value_succ_eq_prefixAverage_oneRound]
  unfold value
  rw [<- finiteAverage_sub]
  apply abs_finiteAverage_le_of_pointwise_abs_le
  intro oldSeeds
  exact B.affinePaddedRestrictByRounds_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
    (roundsOfSeeds D T r oldSeeds) hreadOnce hunambiguous hreadsAll
      D T p hp hD hT

/-- The concrete depth-`L` hybrid has accumulated error at most `L` times
the one-round bound. -/
theorem abs_value_sub_value_zero_le_rounds_mul_card_mul_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
      (4 * m) D)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p T) (L : Nat) :
    |value B D T L - value B D T 0| <=
      (L : Rat) * ((Fintype.card B.Vertex : Rat) * p ^ m) := by
  apply FiniteRoundTelescoping.abs_value_sub_initial_le_rounds_mul
  intro round _hround
  exact abs_value_succ_sub_value_le_card_mul_pow
    B hreadOnce hunambiguous hreadsAll D T p hp hD hT

/-- Telescoping from the true uniform average to an arbitrary terminal
quantity.  Only the displayed terminal comparison remains to be supplied by
the zero-tail layer. -/
theorem abs_uniformAverage_sub_terminal_le_rounds_mul_card_mul_pow_add
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
      (4 * m) D)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p T)
    (L : Nat) (terminal tailCost : Rat)
    (htail : |value B D T L - terminal| <= tailCost) :
    |finiteAverage B.ratAcceptanceIndicator - terminal| <=
      (L : Rat) * ((Fintype.card B.Vertex : Rat) * p ^ m) + tailCost := by
  rw [<- value_zero B D T]
  exact FiniteRoundTelescoping.abs_initial_sub_terminal_le_rounds_mul_add
    (value B D T) terminal L
      ((Fintype.card B.Vertex : Rat) * p ^ m) tailCost
      (fun round _hround => abs_value_succ_sub_value_le_card_mul_pow
        B hreadOnce hunambiguous hreadsAll D T p hp hD hT)
      htail

/-- DPTW-shaped specialization of the concrete finite hybrid. -/
theorem abs_uniformAverage_sub_zeroTail_le_dptw_shape
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
      (4 * m) D)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p T)
    (L : Nat) (zeroTail N : Rat)
    (htail : |value B D T L - zeroTail| <= N * (1 - p) ^ L) :
    |finiteAverage B.ratAcceptanceIndicator - zeroTail| <=
      (L : Rat) * (Fintype.card B.Vertex : Rat) * p ^ m +
        N * (1 - p) ^ L := by
  have h := abs_uniformAverage_sub_terminal_le_rounds_mul_card_mul_pow_add
    B hreadOnce hunambiguous hreadsAll D T p hp hD hT
      L zeroTail (N * (1 - p) ^ L) htail
  simpa [mul_assoc] using h

/-! ## Honest bridge to the existing DPTW survivor theorem -/

/-- Once a concrete seed-layout equality identifies the nested hybrid with
the flattened packed-tail DPTW average, the existing independent-survival
theorem supplies the terminal comparison.  The equality `hPacked` is the
remaining representation/reindexing obligation between the two APIs. -/
theorem abs_value_sub_dptwZeroTailAverage_le_marginal_pow_of_packed_eq
    {inputBits primitiveSeedBits : Nat}
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    (B : FiniteUnambiguousFBDD (2 ^ inputBits))
    (D : DSeed -> Fin (2 ^ inputBits) -> Bool)
    (T : TSeed -> Fin (2 ^ inputBits) -> Bool)
    (a b : DPTWCoordinatePrimitive inputBits primitiveSeedBits)
    (levelsAfterFirst : Nat)
    (test : StreamingMagnification.TotalSearch.TruthTable inputBits -> Bool)
    (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape primitiveSeedBits =>
        b.generate seed index) = rho)
    (hPacked :
      value B D T (levelsAfterFirst + 1) =
        uniformPredicateAverage
          (fun pair : Prod
              (StreamingMagnification.TotalSearch.TruthTable inputBits)
              (FiniteBitTape
                ((levelsAfterFirst + 1) *
                  (primitiveSeedBits + primitiveSeedBits))) =>
            test (dptwGenerateWithTail a b levelsAfterFirst
              pair.2 pair.1))) :
    |value B D T (levelsAfterFirst + 1) -
        uniformPredicateAverage
          (fun pair : Prod
              (StreamingMagnification.TotalSearch.TruthTable inputBits)
              (FiniteBitTape
                ((levelsAfterFirst + 1) *
                  (primitiveSeedBits + primitiveSeedBits))) =>
            test (dptwZeroTailGenerate a b levelsAfterFirst pair.2))| <=
      (2 ^ inputBits : Rat) * rho ^ (levelsAfterFirst + 1) := by
  rw [hPacked]
  exact dptwZeroTail_product_test_average_sub_le_marginal_pow
    a b levelsAfterFirst test rho hMarginal

/-- Full concrete hybrid plus survivor-cost composition.  This theorem
closes the probabilistic telescoping once `hPacked` identifies the explicit
nested affine seeds with the DPTW flattened seed tape.  No relation between
the one-round mask parameter `p` and the primitive marginal `rho` is hidden:
both appear explicitly in the conclusion. -/
theorem abs_uniformAverage_sub_dptwZeroTailAverage_le_of_packed_eq
    {inputBits primitiveSeedBits m : Nat}
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD (2 ^ inputBits))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed -> Fin (2 ^ inputBits) -> Bool)
    (T : TSeed -> Fin (2 ^ inputBits) -> Bool)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
      (4 * m) D)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p T)
    (a b : DPTWCoordinatePrimitive inputBits primitiveSeedBits)
    (levelsAfterFirst : Nat)
    (test : StreamingMagnification.TotalSearch.TruthTable inputBits -> Bool)
    (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape primitiveSeedBits =>
        b.generate seed index) = rho)
    (hPacked :
      value B D T (levelsAfterFirst + 1) =
        uniformPredicateAverage
          (fun pair : Prod
              (StreamingMagnification.TotalSearch.TruthTable inputBits)
              (FiniteBitTape
                ((levelsAfterFirst + 1) *
                  (primitiveSeedBits + primitiveSeedBits))) =>
            test (dptwGenerateWithTail a b levelsAfterFirst
              pair.2 pair.1))) :
    |finiteAverage B.ratAcceptanceIndicator -
        uniformPredicateAverage
          (fun pair : Prod
              (StreamingMagnification.TotalSearch.TruthTable inputBits)
              (FiniteBitTape
                ((levelsAfterFirst + 1) *
                  (primitiveSeedBits + primitiveSeedBits))) =>
            test (dptwZeroTailGenerate a b levelsAfterFirst pair.2))| <=
      ((levelsAfterFirst + 1 : Nat) : Rat) *
          ((Fintype.card B.Vertex : Rat) * p ^ m) +
        (2 ^ inputBits : Rat) * rho ^ (levelsAfterFirst + 1) := by
  apply abs_uniformAverage_sub_terminal_le_rounds_mul_card_mul_pow_add
    B hreadOnce hunambiguous hreadsAll D T p hp hD hT
      (levelsAfterFirst + 1)
      (uniformPredicateAverage
        (fun pair : Prod
            (StreamingMagnification.TotalSearch.TruthTable inputBits)
            (FiniteBitTape
              ((levelsAfterFirst + 1) *
                (primitiveSeedBits + primitiveSeedBits))) =>
          test (dptwZeroTailGenerate a b levelsAfterFirst pair.2)))
      ((2 ^ inputBits : Rat) * rho ^ (levelsAfterFirst + 1))
  exact abs_value_sub_dptwZeroTailAverage_le_marginal_pow_of_packed_eq
    B D T a b levelsAfterFirst test rho hMarginal hPacked

end FiniteAffineRestrictionHybrid

end OneTapeMagnification
end Frontier
end Pnp4
