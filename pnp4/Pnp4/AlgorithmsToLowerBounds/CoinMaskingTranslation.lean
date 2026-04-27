import Pnp4.AlgorithmsToLowerBounds.CoinProblem

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Expectation of a rational-valued observable under the Bernoulli product
distribution with bit bias `bias`.
-/
noncomputable def expectationProductBias
    {n : Nat}
    (bias : Rat)
    (F : BitVec n → Rat) : Rat :=
  ∑ x : BitVec n, productBiasWeight bias x * F x

/--
Average acceptance after randomly masking inputs.

The outer distribution samples the mask `keep`; the inner distribution samples
the target input `x`, and the source algorithm sees `maskVec keep x`.
-/
noncomputable def maskedAcceptanceAverage
    {n : Nat}
    (keepBias inputBias : Rat)
    (A : BitVec n → Bool) : Rat :=
  expectationProductBias keepBias
    (fun keep => acceptanceProbability inputBias (fun x => A (maskVec keep x)))

/-- Bias parameters for the masking translation in the coin-problem route. -/
structure MaskingBiasParams where
  p : Rat
  q : Rat
  eps : Rat
  hp_nonneg : 0 ≤ p
  hp_pos : 0 < p
  hq_pos : 0 < q
  hq_le_one : q ≤ 1
  hp_le_q : p ≤ q
  heps_nonneg : 0 ≤ eps
  heps_lt_one : eps < 1

/-- Source low-bias side: `p * (1 - eps)`. -/
def MaskingBiasParams.lowSourceBias (params : MaskingBiasParams) : Rat :=
  params.p * (1 - params.eps)

/-- Source high-bias side: `p`. -/
def MaskingBiasParams.highSourceBias (params : MaskingBiasParams) : Rat :=
  params.p

/-- Target low-bias side: `q * (1 - eps)`. -/
def MaskingBiasParams.lowTargetBias (params : MaskingBiasParams) : Rat :=
  params.q * (1 - params.eps)

/-- Target high-bias side: `q`. -/
def MaskingBiasParams.highTargetBias (params : MaskingBiasParams) : Rat :=
  params.q

/-- Mask keep probability: `p / q`. -/
def MaskingBiasParams.keepBias (params : MaskingBiasParams) : Rat :=
  params.p / params.q

/--
Distribution-pushforward facts for input masking.

These are the probability identities behind Claim 2.4: masking a `q`-biased
input by an independent `p/q` mask yields a `p`-biased input, and similarly for
the `(1 - eps)`-scaled low side.
-/
structure MaskingPushforwardFacts
    (n : Nat)
    (params : MaskingBiasParams) where
  high_pushforward :
    ∀ A : BitVec n → Bool,
      acceptanceProbability params.highSourceBias A =
        maskedAcceptanceAverage params.keepBias params.highTargetBias A
  low_pushforward :
    ∀ A : BitVec n → Bool,
      acceptanceProbability params.lowSourceBias A =
        maskedAcceptanceAverage params.keepBias params.lowTargetBias A

/-- Advantage of the masked target algorithms, averaged over masks. -/
noncomputable def maskedAcceptanceAdvantage
    {n : Nat}
    (keepBias targetLowBias targetHighBias : Rat)
    (A : BitVec n → Bool) : Rat :=
  maskedAcceptanceAverage keepBias targetHighBias A -
    maskedAcceptanceAverage keepBias targetLowBias A

/-- Advantage after fixing one concrete mask. -/
noncomputable def fixedMaskAcceptanceAdvantage
    {n : Nat}
    (keep : BitVec n)
    (targetLowBias targetHighBias : Rat)
    (A : BitVec n → Bool) : Rat :=
  acceptanceProbability targetHighBias (fun x => A (maskVec keep x)) -
    acceptanceProbability targetLowBias (fun x => A (maskVec keep x))

/--
The pushforward facts identify the averaged target advantage with the source
advantage.
-/
theorem MaskingPushforwardFacts.masked_advantage_eq_source
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : MaskingPushforwardFacts n params)
    (A : BitVec n → Bool) :
    maskedAcceptanceAdvantage
        params.keepBias
        params.lowTargetBias
        params.highTargetBias
        A =
      acceptanceProbability params.highSourceBias A -
        acceptanceProbability params.lowSourceBias A := by
  unfold maskedAcceptanceAdvantage
  rw [← facts.high_pushforward A, ← facts.low_pushforward A]

/--
Finite averaging contract for masks.

If the average advantage over all masks is at least `adv`, some fixed mask has
advantage at least `adv`.
-/
structure MaskAveragingContract
    (n : Nat)
    (keepBias : Rat) where
  exists_good_mask :
    ∀ (A : BitVec n → Bool) (targetLowBias targetHighBias adv : Rat),
      adv ≤ maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A →
        ∃ keep : BitVec n,
          adv ≤ fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A

/-- Combined probability side of the masking translation. -/
structure CoinMaskingTranslationFacts
    (params : MaskingBiasParams)
    (n : Nat) where
  pushforward : MaskingPushforwardFacts n params
  averaging : MaskAveragingContract n params.keepBias

/-- Combined class/probability source facts for a fixed slice. -/
structure CoinMaskingClassTranslationFacts
    (C : CircuitFamilyClass)
    (params : MaskingBiasParams)
    (n : Nat) where
  closedUnderMasking : ClosedUnderInputMasking C
  translationFacts : CoinMaskingTranslationFacts params n

/--
Readout theorem: pushforward plus finite averaging produces a fixed mask whose
target advantage is at least the source advantage lower bound.
-/
theorem CoinMaskingTranslationFacts.exists_mask_with_source_advantage
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : CoinMaskingTranslationFacts params n)
    (A : BitVec n → Bool)
    {adv : Rat}
    (hAdv :
      adv ≤
        acceptanceProbability params.highSourceBias A -
          acceptanceProbability params.lowSourceBias A) :
    ∃ keep : BitVec n,
      adv ≤
        fixedMaskAcceptanceAdvantage
          keep
          params.lowTargetBias
          params.highTargetBias
          A := by
  apply facts.averaging.exists_good_mask
  rwa [facts.pushforward.masked_advantage_eq_source A]

end AlgorithmsToLowerBounds
end Pnp4
