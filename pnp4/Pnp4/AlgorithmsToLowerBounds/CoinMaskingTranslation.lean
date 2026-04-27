import Pnp4.AlgorithmsToLowerBounds.CoinProblem
import Mathlib.Data.Fintype.Lattice

namespace Pnp4
namespace AlgorithmsToLowerBounds

/-- Local splitter for one head bit and an `n`-bit tail. -/
private def bitVecSuccEquivMask (n : Nat) :
    BitVec (n + 1) ≃ Bool × BitVec n where
  toFun x := (x 0, fun i => x i.succ)
  invFun y := Fin.cases y.1 y.2
  left_inv x := by
    funext i
    cases i using Fin.cases <;> simp
  right_inv y := by
    cases y with
    | mk b x =>
        rfl

/-- Sum over `(n+1)`-bit vectors by head bit and tail. -/
private theorem sum_bitVec_succ
    {n : Nat}
    {α : Type}
    [AddCommMonoid α]
    (F : BitVec (n + 1) → α) :
    (∑ x : BitVec (n + 1), F x) =
      ∑ b : Bool, ∑ x : BitVec n, F ((bitVecSuccEquivMask n).symm (b, x)) := by
  calc
    (∑ x : BitVec (n + 1), F x)
        = ∑ y : Bool × BitVec n, F ((bitVecSuccEquivMask n).symm y) := by
          exact Fintype.sum_equiv (bitVecSuccEquivMask n)
            F
            (fun y : Bool × BitVec n => F ((bitVecSuccEquivMask n).symm y))
            (fun _ => by simp)
    _ = ∑ b : Bool, ∑ x : BitVec n,
          F ((bitVecSuccEquivMask n).symm (b, x)) := by
          rw [Fintype.sum_prod_type]

/-- Product weight split by head bit and tail. -/
private theorem productBiasWeight_succ
    (bias : Rat)
    {n : Nat}
    (b : Bool)
    (x : BitVec n) :
    productBiasWeight bias ((bitVecSuccEquivMask n).symm (b, x)) =
      bernoulliBitWeight bias b * productBiasWeight bias x := by
  unfold productBiasWeight
  rw [Fin.prod_univ_succ]
  simp [bitVecSuccEquivMask]

/-- Coordinatewise masking respects the head/tail split. -/
private theorem maskVec_succ
    {n : Nat}
    (keepBit xBit : Bool)
    (keepTail xTail : BitVec n) :
    maskVec
        ((bitVecSuccEquivMask n).symm (keepBit, keepTail))
        ((bitVecSuccEquivMask n).symm (xBit, xTail)) =
      (bitVecSuccEquivMask n).symm
        (maskBit keepBit xBit, maskVec keepTail xTail) := by
  funext i
  cases i using Fin.cases <;> simp [bitVecSuccEquivMask, maskVec]

/-- Acceptance probability split by head bit and tail. -/
private theorem acceptanceProbability_succ
    (bias : Rat)
    {n : Nat}
    (A : BitVec (n + 1) → Bool) :
    acceptanceProbability bias A =
      ∑ b : Bool,
        bernoulliBitWeight bias b *
          acceptanceProbability bias
            (fun x : BitVec n =>
              A ((bitVecSuccEquivMask n).symm (b, x))) := by
  unfold acceptanceProbability
  rw [sum_bitVec_succ]
  apply Finset.sum_congr rfl
  intro b _hb
  calc
    (∑ x : BitVec n,
        if A ((bitVecSuccEquivMask n).symm (b, x)) then
          productBiasWeight bias ((bitVecSuccEquivMask n).symm (b, x))
        else
          0)
        =
          ∑ x : BitVec n,
            bernoulliBitWeight bias b *
              (if A ((bitVecSuccEquivMask n).symm (b, x)) then
                productBiasWeight bias x
              else
                0) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [productBiasWeight_succ]
          by_cases hA : A ((bitVecSuccEquivMask n).symm (b, x)) <;>
            simp [hA]
    _ =
          bernoulliBitWeight bias b *
            (∑ x : BitVec n,
              if A ((bitVecSuccEquivMask n).symm (b, x)) then
                productBiasWeight bias x
              else
                0) := by
          rw [Finset.mul_sum]

/--
Expectation of a rational-valued observable under the Bernoulli product
distribution with bit bias `bias`.
-/
noncomputable def expectationProductBias
    {n : Nat}
    (bias : Rat)
    (F : BitVec n → Rat) : Rat :=
  ∑ x : BitVec n, productBiasWeight bias x * F x

/-- Expectation is linear over subtraction for rational-valued observables. -/
theorem expectationProductBias_sub
    {n : Nat}
    (bias : Rat)
    (F G : BitVec n → Rat) :
    expectationProductBias bias (fun x => F x - G x) =
      expectationProductBias bias F - expectationProductBias bias G := by
  unfold expectationProductBias
  simp [mul_sub, Finset.sum_sub_distrib]

/--
If a rational-valued observable is pointwise bounded above by `bound`, then so
is its expectation under any valid Bernoulli product distribution.
-/
theorem expectationProductBias_le_of_pointwise_le
    {n : Nat}
    {bias bound : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (F : BitVec n → Rat)
    (hF : ∀ x : BitVec n, F x ≤ bound) :
    expectationProductBias bias F ≤ bound := by
  classical
  unfold expectationProductBias
  calc
    (∑ x : BitVec n, productBiasWeight bias x * F x)
        ≤ ∑ x : BitVec n, productBiasWeight bias x * bound := by
          refine Finset.sum_le_sum ?_
          intro x _hx
          exact mul_le_mul_of_nonneg_left
            (hF x)
            (productBiasWeight_nonneg hBias_nonneg hBias_le_one x)
    _ = (∑ x : BitVec n, productBiasWeight bias x) * bound := by
          rw [Finset.sum_mul]
    _ = bound := by
          rw [productBiasWeight_total]
          ring

/-- A rational-valued function on bit-vectors has a maximum. -/
theorem exists_max_bitVec_rat
    {n : Nat}
    (F : BitVec n → Rat) :
    ∃ x0 : BitVec n, ∀ x : BitVec n, F x ≤ F x0 := by
  classical
  simpa using (Finite.exists_max F)

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

/-- Masked acceptance split by head bit, target head bit, and tail. -/
private theorem maskedAcceptanceAverage_succ
    (keepBias inputBias : Rat)
    {n : Nat}
    (A : BitVec (n + 1) → Bool) :
    maskedAcceptanceAverage keepBias inputBias A =
      ∑ keepBit : Bool,
        ∑ xBit : Bool,
          bernoulliBitWeight keepBias keepBit *
            bernoulliBitWeight inputBias xBit *
              maskedAcceptanceAverage keepBias inputBias
                (fun tail : BitVec n =>
                  A ((bitVecSuccEquivMask n).symm
                    (maskBit keepBit xBit, tail))) := by
  unfold maskedAcceptanceAverage expectationProductBias
  rw [sum_bitVec_succ]
  simp_rw [productBiasWeight_succ]
  simp_rw [acceptanceProbability_succ]
  simp_rw [maskVec_succ]
  simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc,
    mul_left_comm]

/--
Masking a product-biased input by an independent product-biased keep mask
pushes the input bias from `inputBias` to `keepBias * inputBias`.
-/
theorem maskedAcceptanceAverage_eq_acceptanceProbability_mul
    {n : Nat}
    (keepBias inputBias : Rat)
    (A : BitVec n → Bool) :
    maskedAcceptanceAverage keepBias inputBias A =
      acceptanceProbability (keepBias * inputBias) A := by
  induction n with
  | zero =>
      have hMask : ∀ keep x : BitVec 0, maskVec keep x = x := by
        intro keep x
        funext i
        exact Fin.elim0 i
      unfold maskedAcceptanceAverage expectationProductBias acceptanceProbability productBiasWeight
      simp [hMask]
  | succ n ih =>
      rw [maskedAcceptanceAverage_succ]
      simp_rw [ih]
      rw [acceptanceProbability_succ]
      simp [maskBit, bernoulliBitWeight, sub_eq_add_neg, mul_add, add_mul,
        mul_assoc, mul_comm]
      ring

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

/-- The masking keep bias is nonnegative. -/
theorem MaskingBiasParams.keepBias_nonneg
    (params : MaskingBiasParams) :
    0 ≤ params.keepBias := by
  unfold MaskingBiasParams.keepBias
  exact div_nonneg params.hp_nonneg (le_of_lt params.hq_pos)

/-- The masking keep bias is at most one. -/
theorem MaskingBiasParams.keepBias_le_one
    (params : MaskingBiasParams) :
    params.keepBias ≤ 1 := by
  unfold MaskingBiasParams.keepBias
  have hDiv :
      params.p / params.q ≤ params.q / params.q :=
    div_le_div_of_nonneg_right params.hp_le_q (le_of_lt params.hq_pos)
  simpa [div_self (ne_of_gt params.hq_pos)] using hDiv

/-- The keep mask turns the target high bias `q` into the source high bias `p`. -/
theorem MaskingBiasParams.keepBias_mul_highTargetBias
    (params : MaskingBiasParams) :
    params.keepBias * params.highTargetBias = params.highSourceBias := by
  unfold MaskingBiasParams.keepBias
    MaskingBiasParams.highTargetBias
    MaskingBiasParams.highSourceBias
  field_simp [ne_of_gt params.hq_pos]

/--
The keep mask turns the target low bias `q * (1 - eps)` into the source low
bias `p * (1 - eps)`.
-/
theorem MaskingBiasParams.keepBias_mul_lowTargetBias
    (params : MaskingBiasParams) :
    params.keepBias * params.lowTargetBias = params.lowSourceBias := by
  unfold MaskingBiasParams.keepBias
    MaskingBiasParams.lowTargetBias
    MaskingBiasParams.lowSourceBias
  field_simp [ne_of_gt params.hq_pos]
  ring

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

/-- The masking pushforward identities induced by valid masking parameters. -/
theorem MaskingPushforwardFacts.of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    MaskingPushforwardFacts n params := by
  refine ⟨?_, ?_⟩
  · intro A
    rw [maskedAcceptanceAverage_eq_acceptanceProbability_mul]
    rw [params.keepBias_mul_highTargetBias]
  · intro A
    rw [maskedAcceptanceAverage_eq_acceptanceProbability_mul]
    rw [params.keepBias_mul_lowTargetBias]

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
The averaged masked advantage is the expectation of the fixed-mask advantage.
-/
theorem maskedAcceptanceAdvantage_eq_expectation_fixed
    {n : Nat}
    (keepBias targetLowBias targetHighBias : Rat)
    (A : BitVec n → Bool) :
    maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A =
      expectationProductBias keepBias
        (fun keep =>
          fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A) := by
  unfold maskedAcceptanceAdvantage maskedAcceptanceAverage fixedMaskAcceptanceAdvantage
  rw [expectationProductBias_sub]

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

/--
Finite averaging for masks.

The average of the fixed-mask advantages is at most their maximum, so any lower
bound on the average is attained by some fixed mask.
-/
theorem MaskAveragingContract.of_valid_keepBias
    {n : Nat}
    {keepBias : Rat}
    (hKeep_nonneg : 0 ≤ keepBias)
    (hKeep_le_one : keepBias ≤ 1) :
    MaskAveragingContract n keepBias := by
  refine ⟨?_⟩
  intro A targetLowBias targetHighBias adv hAvg
  let F : BitVec n → Rat :=
    fun keep => fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A
  rcases exists_max_bitVec_rat F with ⟨keep0, hMax⟩
  have hEq :
      maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A =
        expectationProductBias keepBias F := by
    simpa [F] using
      (maskedAcceptanceAdvantage_eq_expectation_fixed
        keepBias targetLowBias targetHighBias A)
  have hExpectationLe :
      expectationProductBias keepBias F ≤ F keep0 :=
    expectationProductBias_le_of_pointwise_le
      hKeep_nonneg
      hKeep_le_one
      F
      hMax
  exact ⟨keep0, by
    calc
      adv ≤ maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A := hAvg
      _ = expectationProductBias keepBias F := hEq
      _ ≤ F keep0 := hExpectationLe⟩

/-- Finite mask averaging specialized to the masking parameters. -/
theorem MaskAveragingContract.of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    MaskAveragingContract n params.keepBias :=
  MaskAveragingContract.of_valid_keepBias
    params.keepBias_nonneg
    params.keepBias_le_one

/-- Combined probability side of the masking translation. -/
structure CoinMaskingTranslationFacts
    (params : MaskingBiasParams)
    (n : Nat) where
  pushforward : MaskingPushforwardFacts n params
  averaging : MaskAveragingContract n params.keepBias

/-- Probability side of the masking translation from explicit masking params. -/
theorem CoinMaskingTranslationFacts.of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    CoinMaskingTranslationFacts params n :=
  { pushforward := MaskingPushforwardFacts.of_maskingBiasParams params n
    averaging := MaskAveragingContract.of_maskingBiasParams params n }

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

/--
Choose, for a fixed circuit and target biases, a mask maximizing the translated
fixed-mask advantage.
-/
noncomputable def bestMaskForCircuit
    {C : CircuitFamilyClass}
    {n : Nat}
    (targetLowBias targetHighBias : Rat)
    (c : C.Family n) : BitVec n :=
  Classical.choose
    (exists_max_bitVec_rat
      (fun keep =>
        fixedMaskAcceptanceAdvantage
          keep
          targetLowBias
          targetHighBias
          (fun x => C.eval c x)))

/-- The selected best mask maximizes fixed-mask advantage. -/
theorem bestMaskForCircuit_max
    {C : CircuitFamilyClass}
    {n : Nat}
    (targetLowBias targetHighBias : Rat)
    (c : C.Family n) :
    ∀ keep : BitVec n,
      fixedMaskAcceptanceAdvantage
        keep
        targetLowBias
        targetHighBias
        (fun x => C.eval c x) ≤
      fixedMaskAcceptanceAdvantage
        (bestMaskForCircuit targetLowBias targetHighBias c)
        targetLowBias
        targetHighBias
        (fun x => C.eval c x) :=
  Classical.choose_spec
    (exists_max_bitVec_rat
      (fun keep =>
        fixedMaskAcceptanceAdvantage
          keep
          targetLowBias
          targetHighBias
          (fun x => C.eval c x)))

/--
If a circuit has source advantage, its pre-selected best mask has at least that
advantage on the translated target biases.
-/
theorem source_advantage_le_bestMask_fixed_advantage
    {C : CircuitFamilyClass}
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : CoinMaskingTranslationFacts params n)
    (c : C.Family n)
    {adv : Rat}
    (hSourceAdv :
      adv ≤
        acceptanceProbability params.highSourceBias (fun x => C.eval c x) -
          acceptanceProbability params.lowSourceBias (fun x => C.eval c x)) :
    adv ≤
      fixedMaskAcceptanceAdvantage
        (bestMaskForCircuit params.lowTargetBias params.highTargetBias c)
        params.lowTargetBias
        params.highTargetBias
        (fun x => C.eval c x) := by
  rcases facts.exists_mask_with_source_advantage
      (fun x => C.eval c x)
      hSourceAdv with
    ⟨keep, hKeep⟩
  exact le_trans hKeep
    (bestMaskForCircuit_max
      params.lowTargetBias
      params.highTargetBias
      c
      keep)

end AlgorithmsToLowerBounds
end Pnp4
