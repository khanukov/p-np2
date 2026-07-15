import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDConcreteMultiRoundHybrid

/-!
# Exact DPTW packing bridge for the affine uFBDD hybrid

`FiniteAffineRestrictionHybrid.Seeds` stores affine rounds in a left-associated
nested product, while the retained DPTW generator stores the same independent
`A/B` seed pairs contiguously in one Boolean tape.  This file gives an explicit
finite equivalence between those layouts, proves that their recursive Boolean
semantics agree pointwise, and transports the uniform finite average across the
equivalence.

The final survivor estimate therefore no longer needs an external equality
between the nested hybrid and the packed DPTW average.  Its only semantic
premise says that the uFBDD rational acceptance indicator represents the
chosen Boolean test; this is the honest model-to-test interface.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open Pnp3.ComplexityInterfaces
open StreamingMagnification
open StreamingMagnification.TotalSearch
open FiniteBooleanRestrictionMoment

namespace FiniteAffineRestrictionHybrid

/-! ## Reassociating explicit round seeds -/

/-- Expose the outermost seed of a nonempty left-associated seed prefix. -/
def seedsHeadTailEquiv (Seed : Type*) :
    (r : Nat) -> Seeds Seed (r + 1) ≃ Seed × Seeds Seed r
  | 0 => Equiv.prodComm PUnit Seed
  | r + 1 =>
      (Equiv.prodCongr (seedsHeadTailEquiv Seed r) (Equiv.refl Seed)).trans
        (Equiv.prodAssoc Seed (Seeds Seed r) Seed)

/-- A single seed is the unique depth-one prefix with trivial empty prefix. -/
def seedToSeedsOneEquiv (Seed : Type*) : Seed ≃ Seeds Seed 1 where
  toFun seed := (PUnit.unit, seed)
  invFun seeds := seeds.2
  left_inv _ := rfl
  right_inv seeds := by
    rcases seeds with ⟨empty, seed⟩
    rcases empty with ⟨⟩
    rfl

/-- Reading the outer seed and then the tail preserves the round-list order. -/
theorem roundsOfSeeds_eq_head_cons_tail
    {n r : Nat} {DSeed TSeed : Type*}
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (seeds : Seeds (DSeed × TSeed) (r + 1)) :
    roundsOfSeeds D T (r + 1) seeds =
      roundOfSeed D T (seedsHeadTailEquiv (DSeed × TSeed) r seeds).1 ::
        roundsOfSeeds D T r
          (seedsHeadTailEquiv (DSeed × TSeed) r seeds).2 := by
  induction r with
  | zero =>
      rcases seeds with ⟨empty, seed⟩
      rcases empty with ⟨⟩
      rfl
  | succ r ih =>
      rcases seeds with ⟨oldSeeds, seed⟩
      change roundsOfSeeds D T (r + 1) oldSeeds ++
          [roundOfSeed D T seed] = _
      rw [ih oldSeeds]
      rfl

/-! ## Packed DPTW tapes versus nested products -/

/-- A retained DPTW tape of `levelsAfterFirst + 1` `A/B` pairs is exactly a
depth-`levelsAfterFirst + 1` affine-round seed prefix. -/
def dptwPackedSeedsEquiv (s : Nat) :
    (levelsAfterFirst : Nat) ->
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) ≃
        Seeds (FiniteBitTape s × FiniteBitTape s) (levelsAfterFirst + 1)
  | 0 => (dptwFinalASeedBSeedEquiv s).trans
      (seedToSeedsOneEquiv (FiniteBitTape s × FiniteBitTape s))
  | levelsAfterFirst + 1 =>
      (dptwASeedBSeedTailEquiv levelsAfterFirst s).trans
        ((Equiv.prodCongr (Equiv.refl (FiniteBitTape s × FiniteBitTape s))
          (dptwPackedSeedsEquiv s levelsAfterFirst)).trans
        (seedsHeadTailEquiv (FiniteBitTape s × FiniteBitTape s)
          (levelsAfterFirst + 1)).symm)

/-- At the final retained level, packing exposes precisely its `A/B` pair. -/
theorem dptwPackedSeedsEquiv_zero_apply
    {s : Nat} (seed : FiniteBitTape (1 * (s + s))) :
    dptwPackedSeedsEquiv s 0 seed =
      (PUnit.unit, dptwFinalASeedBSeedEquiv s seed) := by
  rfl

/-- At a nonfinal level, the nested head is the first packed `A/B` pair and
the nested tail is the recursively packed suffix. -/
theorem seedsHeadTailEquiv_dptwPackedSeedsEquiv_succ
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s))) :
    seedsHeadTailEquiv (FiniteBitTape s × FiniteBitTape s)
        (levelsAfterFirst + 1)
        (dptwPackedSeedsEquiv s (levelsAfterFirst + 1) seed) =
      ((dptwASeedBSeedTailEquiv levelsAfterFirst s seed).1,
        dptwPackedSeedsEquiv s levelsAfterFirst
          (dptwASeedBSeedTailEquiv levelsAfterFirst s seed).2) := by
  simp [dptwPackedSeedsEquiv, Prod.map]

/-- The `A` component exposed by the DPTW split is the first primitive block. -/
theorem dptwASeedBSeedTailEquiv_a
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s))) :
    (dptwASeedBSeedTailEquiv levelsAfterFirst s seed).1.1 =
      dptwFirstASeed seed := by
  rfl

/-- The `B` component exposed by the DPTW split is the second primitive block. -/
theorem dptwASeedBSeedTailEquiv_b
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s))) :
    (dptwASeedBSeedTailEquiv levelsAfterFirst s seed).1.2 =
      dptwFirstBSeed seed := by
  funext index
  exact dptwASeedBSeedTailEquiv_b_apply seed index

/-- The remaining packed suffix is exactly `dptwTailSeed`. -/
theorem dptwASeedBSeedTailEquiv_tail
    {levelsAfterFirst s : Nat}
    (seed : FiniteBitTape ((levelsAfterFirst + 2) * (s + s))) :
    (dptwASeedBSeedTailEquiv levelsAfterFirst s seed).2 =
      dptwTailSeed seed := by
  funext index
  exact dptwASeedBSeedTailEquiv_tail_apply seed index

/-! ## Exact recursive semantics -/

/-- Nested affine masking under the packing equivalence is pointwise the
retained DPTW recursion with the supplied terminal truth table. -/
theorem applyAffineRestrictionRounds_dptwPackedSeedsEquiv_eq
    {n s : Nat} (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (seed : FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
    (tail : TruthTable n) :
    applyAffineRestrictionRounds
        (roundsOfSeeds a.generate b.generate (levelsAfterFirst + 1)
          (dptwPackedSeedsEquiv s levelsAfterFirst seed)) tail =
      dptwGenerateWithTail a b levelsAfterFirst seed tail := by
  induction levelsAfterFirst with
  | zero =>
      rfl
  | succ levelsAfterFirst ih =>
      rw [roundsOfSeeds_eq_head_cons_tail]
      rw [seedsHeadTailEquiv_dptwPackedSeedsEquiv_succ]
      funext index
      simp only [applyAffineRestrictionRounds, roundOfSeed, maskedInput,
        dptwGenerateWithTail_step]
      rw [dptwASeedBSeedTailEquiv_a, dptwASeedBSeedTailEquiv_b,
        dptwASeedBSeedTailEquiv_tail]
      rw [ih (dptwTailSeed seed)]

/-! ## Exact average transport -/

/-- Rational finite averages are invariant under a finite equivalence. -/
theorem finiteAverage_comp_equiv
    {Input Output : Type*} [Fintype Input] [Fintype Output]
    (equiv : Input ≃ Output) (f : Output -> Rat) :
    finiteAverage (fun input => f (equiv input)) = finiteAverage f := by
  unfold finiteAverage
  have hSum :
      (∑ input : Input, f (equiv input)) = ∑ output : Output, f output :=
    Fintype.sum_equiv equiv _ _ (fun _ => rfl)
  rw [hSum, Fintype.card_congr equiv]

/-- Under the explicit packing equivalence, the nested masked-input average
is exactly the packed DPTW-with-tail average, still with a rational-valued
test. -/
theorem value_dptw_generateWithTail_rational_average
    {n s : Nat} (B : FiniteUnambiguousFBDD (2 ^ n))
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat) :
    value B a.generate b.generate (levelsAfterFirst + 1) =
      finiteAverage
        (fun pair : TruthTable n ×
            FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
          B.ratAcceptanceIndicator
            (dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1)) := by
  rw [value_eq_nested_maskedInput_average]
  calc
    finiteAverage (fun seeds :
        Seeds (FiniteBitTape s × FiniteBitTape s) (levelsAfterFirst + 1) =>
      finiteAverage (fun tail : TruthTable n =>
        B.ratAcceptanceIndicator
          (applyAffineRestrictionRounds
            (roundsOfSeeds a.generate b.generate (levelsAfterFirst + 1)
              seeds) tail))) =
        finiteAverage (fun packedSeed :
            FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
          finiteAverage (fun tail : TruthTable n =>
            B.ratAcceptanceIndicator
              (applyAffineRestrictionRounds
                (roundsOfSeeds a.generate b.generate
                  (levelsAfterFirst + 1)
                  (dptwPackedSeedsEquiv s levelsAfterFirst packedSeed))
                tail))) := by
      exact (finiteAverage_comp_equiv
        (dptwPackedSeedsEquiv s levelsAfterFirst) _).symm
    _ = finiteAverage (fun packedSeed :
          FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
        finiteAverage (fun tail : TruthTable n =>
          B.ratAcceptanceIndicator
            (dptwGenerateWithTail a b levelsAfterFirst packedSeed tail))) := by
      apply finiteAverage_congr
      intro packedSeed
      apply finiteAverage_congr
      intro tail
      rw [applyAffineRestrictionRounds_dptwPackedSeedsEquiv_eq]
    _ = finiteAverage (fun pair :
          FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) × TruthTable n =>
        B.ratAcceptanceIndicator
          (dptwGenerateWithTail a b levelsAfterFirst pair.1 pair.2)) := by
      symm
      exact finiteAverage_prod_eq_iterated
        (Left := FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))
        (Right := TruthTable n)
        (fun packedSeed tail => B.ratAcceptanceIndicator
          (dptwGenerateWithTail a b levelsAfterFirst packedSeed tail))
    _ = finiteAverage (fun pair : TruthTable n ×
          FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
        B.ratAcceptanceIndicator
          (dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1)) := by
      exact (finiteAverage_comp_equiv
        (Equiv.prodComm (TruthTable n)
          (FiniteBitTape ((levelsAfterFirst + 1) * (s + s)))) _).symm

/-- If the uFBDD represents a Boolean test pointwise, the concrete terminal
hybrid is exactly the packed Boolean DPTW average. -/
theorem value_dptw_generateWithTail_eq_uniformPredicateAverage
    {n s : Nat} (B : FiniteUnambiguousFBDD (2 ^ n))
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (test : TruthTable n -> Bool)
    (hTest : forall input,
      B.ratAcceptanceIndicator input = boolIndicator (test input)) :
    value B a.generate b.generate (levelsAfterFirst + 1) =
      uniformPredicateAverage
        (fun pair : TruthTable n ×
            FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
          test (dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1)) := by
  rw [value_dptw_generateWithTail_rational_average]
  change finiteAverage (fun pair : TruthTable n ×
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
        B.ratAcceptanceIndicator
          (dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1)) =
    finiteAverage (fun pair : TruthTable n ×
      FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
        boolIndicator
          (test (dptwGenerateWithTail a b levelsAfterFirst pair.2 pair.1)))
  apply finiteAverage_congr
  intro pair
  exact hTest _

/-! ## Survivor bound with no external packing equality -/

/-- The existing independent-survival theorem now supplies the terminal
comparison directly.  No `hPacked` representation premise remains. -/
theorem abs_value_dptw_sub_zeroTailAverage_le_marginal_pow
    {n s : Nat} (B : FiniteUnambiguousFBDD (2 ^ n))
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (test : TruthTable n -> Bool)
    (hTest : forall input,
      B.ratAcceptanceIndicator input = boolIndicator (test input))
    (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) = rho) :
    |value B a.generate b.generate (levelsAfterFirst + 1) -
        uniformPredicateAverage
          (fun pair : TruthTable n ×
              FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
            test (dptwZeroTailGenerate a b levelsAfterFirst pair.2))| <=
      (2 ^ n : Rat) * rho ^ (levelsAfterFirst + 1) := by
  rw [value_dptw_generateWithTail_eq_uniformPredicateAverage
    B a b levelsAfterFirst test hTest]
  exact dptwZeroTail_product_test_average_sub_le_marginal_pow
    a b levelsAfterFirst test rho hMarginal

/-- Full concrete DPTW hybrid estimate.  The first summand is the accumulated
one-round Fourier error; the second is the exact independent-survivor cost of
deleting the terminal truth table.  All seed packing, conditioning, and
telescoping are internal to the statement, so no external `hPacked` premise
remains. -/
theorem abs_uniformAverage_sub_dptwZeroTailAverage_le
    {n s m : Nat} (B : FiniteUnambiguousFBDD (2 ^ n))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (a b : DPTWCoordinatePrimitive n s)
    (levelsAfterFirst : Nat)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased
      (4 * m) a.generate)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p b.generate)
    (test : TruthTable n -> Bool)
    (hTest : forall input,
      B.ratAcceptanceIndicator input = boolIndicator (test input))
    (rho : Rat)
    (hMarginal : forall index,
      uniformPredicateAverage (fun seed : FiniteBitTape s =>
        b.generate seed index) = rho) :
    |finiteAverage B.ratAcceptanceIndicator -
        uniformPredicateAverage
          (fun pair : TruthTable n ×
              FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
            test (dptwZeroTailGenerate a b levelsAfterFirst pair.2))| <=
      ((levelsAfterFirst + 1 : Nat) : Rat) *
          (Fintype.card B.Vertex : Rat) * p ^ m +
        (2 ^ n : Rat) * rho ^ (levelsAfterFirst + 1) := by
  have htail := abs_value_dptw_sub_zeroTailAverage_le_marginal_pow
    B a b levelsAfterFirst test hTest rho hMarginal
  have h := abs_uniformAverage_sub_terminal_le_rounds_mul_card_mul_pow_add
    B hreadOnce hunambiguous hreadsAll a.generate b.generate
      p hp hD hT (levelsAfterFirst + 1)
      (uniformPredicateAverage
        (fun pair : TruthTable n ×
            FiniteBitTape ((levelsAfterFirst + 1) * (s + s)) =>
          test (dptwZeroTailGenerate a b levelsAfterFirst pair.2)))
      ((2 ^ n : Rat) * rho ^ (levelsAfterFirst + 1)) htail
  simpa only [mul_assoc] using h

end FiniteAffineRestrictionHybrid

end OneTapeMagnification
end Frontier
end Pnp4
