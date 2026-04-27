import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound
import Pnp4.AlgorithmsToLowerBounds.CoinMaskingTranslation
import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
MCSP-to-coin reduction witness specialized to the paper-facing half-vs-fair
regime on truth-table inputs.
-/
abbrev HalfVsFairMCSPCoinReductionWitness
    (hardness : HalfVsFairTruthTableCoinHardness)
    (n : Nat) : Type :=
  MCSPCoinReductionWitness
    n
    (((1 : Rat) - hardness.biasGap n) / 2)
    ((1 : Rat) / 2)
    (halfVsFair_lowBias_nonneg (hardness.biasGap_le_one n))
    (by norm_num)
    (halfVsFair_lowBias_lt_fair (hardness.biasGap_pos n))
    (hardness.advantage n)

/--
Acceptance-profile contract for the MCSP-to-coin reduction on truth-table
inputs.

This splits the statistical obligation into falsifiable pieces: an upper bound
on low-bias acceptance, a lower bound on fair-coin acceptance, and a certificate
that those two bounds leave at least the requested advantage gap.
-/
structure HalfVsFairMCSPCoinAcceptanceProfile
    (hardness : HalfVsFairTruthTableCoinHardness) where
  threshold : Nat → Nat
  lowAcceptanceUpper : Nat → Rat
  fairAcceptanceLower : Nat → Rat
  low_acceptance_le :
    ∀ n : Nat,
      acceptanceProbability (hardness.instance n).lowBias
          (exactTreeMCSPThresholdDecision n (threshold n)) ≤
        lowAcceptanceUpper n
  fair_acceptance_ge :
    ∀ n : Nat,
      fairAcceptanceLower n ≤
        acceptanceProbability (hardness.instance n).highBias
          (exactTreeMCSPThresholdDecision n (threshold n))
  advantage_gap :
    ∀ n : Nat,
      hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n

/--
The decomposed acceptance-profile contract implies the original monolithic
coin-solving statement.
-/
theorem HalfVsFairMCSPCoinAcceptanceProfile.exact_solvesCoin
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinAcceptanceProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (profile.threshold n))
      (hardness.advantage n) := by
  exact solvesCoinProblem_of_acceptanceProbability_bounds
    (inst := hardness.instance n)
    (A := exactTreeMCSPThresholdDecision n (profile.threshold n))
    (adv := hardness.advantage n)
    (lowAcceptanceUpper := profile.lowAcceptanceUpper n)
    (highAcceptanceLower := profile.fairAcceptanceLower n)
    (profile.low_acceptance_le n)
    (profile.fair_acceptance_ge n)
    (profile.advantage_gap n)

/--
Acceptance-profile contract with the corrected half-vs-fair polarity.

Here acceptance means "the table is above the low-complexity MCSP threshold".
Since `highBias` is the fair side in `halfVsFairCoinInstance`, this is the
profile whose fair-side acceptance should be large by Shannon counting.
-/
structure HalfVsFairMCSPCoinRejectionProfile
    (hardness : HalfVsFairTruthTableCoinHardness) where
  threshold : Nat → Nat
  lowAcceptanceUpper : Nat → Rat
  fairAcceptanceLower : Nat → Rat
  low_rejection_acceptance_le :
    ∀ n : Nat,
      acceptanceProbability (hardness.instance n).lowBias
          (exactTreeMCSPThresholdHardDecision n (threshold n)) ≤
        lowAcceptanceUpper n
  fair_rejection_acceptance_ge :
    ∀ n : Nat,
      fairAcceptanceLower n ≤
        acceptanceProbability (hardness.instance n).highBias
          (exactTreeMCSPThresholdHardDecision n (threshold n))
  advantage_gap :
    ∀ n : Nat,
      hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n

/--
The corrected-polarity rejection profile solves the half-vs-fair coin problem.
-/
theorem HalfVsFairMCSPCoinRejectionProfile.hard_solvesCoin
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinRejectionProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdHardDecision n (profile.threshold n))
      (hardness.advantage n) := by
  exact solvesCoinProblem_of_acceptanceProbability_bounds
    (inst := hardness.instance n)
    (A := exactTreeMCSPThresholdHardDecision n (profile.threshold n))
    (adv := hardness.advantage n)
    (lowAcceptanceUpper := profile.lowAcceptanceUpper n)
    (highAcceptanceLower := profile.fairAcceptanceLower n)
    (profile.low_rejection_acceptance_le n)
    (profile.fair_rejection_acceptance_ge n)
    (profile.advantage_gap n)

/--
Smaller theorem-facing contract for the MCSP-to-coin reduction on truth-table
inputs.

Instead of carrying an arbitrary threshold oracle for each slice, this packages
exactly the threshold schedule together with the decomposed acceptance profile
that proves the corresponding exact thresholded tree-MCSP decision function
solves the half-vs-fair coin problem.
-/
structure HalfVsFairMCSPCoinReductionContract
    (hardness : HalfVsFairTruthTableCoinHardness)
    extends HalfVsFairMCSPCoinAcceptanceProfile hardness

/--
Theorem-facing contract for the corrected-polarity MCSP-to-coin reduction.

This does not extend `MCSPThresholdOracle`, whose `decide = true` convention is
reserved for low-complexity tables.  It instead packages the hard-table
complement decision that actually has large fair-side acceptance.
-/
structure HalfVsFairMCSPCoinRejectionContract
    (hardness : HalfVsFairTruthTableCoinHardness)
    extends HalfVsFairMCSPCoinRejectionProfile hardness

/--
Source-side biased/easy mass target for the corrected-polarity MCSP/coin route.

This is the remaining MCSP-side probabilistic theorem: under the low-bias
distribution, low-complexity truth tables have high mass.
-/
structure HalfVsFairBiasedLowComplexityMassFacts
    (hardness : HalfVsFairTruthTableCoinHardness) where
  threshold : Nat → Nat
  lowAcceptanceUpper : Nat → Rat
  low_lowComplexity_mass_ge :
    ∀ n : Nat,
      1 - lowAcceptanceUpper n ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n (threshold n))

/--
Published-proof-facing adjacent-bias MCSP separation source.

This captures the paper-style middle layer before translating back to the
half-vs-fair coin formulation: for each truth-table slice, a hard-table MCSP
threshold separates two neighboring product biases `qLow n < qHigh n`.
-/
structure AdjacentBiasMCSPThresholdSeparationFacts where
  qLow : Nat → Rat
  qHigh : Nat → Rat
  qLow_nonneg : ∀ n : Nat, 0 ≤ qLow n
  qHigh_le_one : ∀ n : Nat, qHigh n ≤ 1
  qLow_lt_qHigh : ∀ n : Nat, qLow n < qHigh n
  advantage : Nat → Rat
  threshold : Nat → Nat
  lowHardAcceptanceUpper : Nat → Rat
  highHardAcceptanceLower : Nat → Rat
  low_hard_acceptance_le :
    ∀ n : Nat,
      acceptanceProbability (qLow n)
          (exactTreeMCSPThresholdHardDecision n (threshold n)) ≤
        lowHardAcceptanceUpper n
  high_hard_acceptance_ge :
    ∀ n : Nat,
      highHardAcceptanceLower n ≤
        acceptanceProbability (qHigh n)
          (exactTreeMCSPThresholdHardDecision n (threshold n))
  advantage_gap :
    ∀ n : Nat,
      advantage n + lowHardAcceptanceUpper n ≤ highHardAcceptanceLower n

/-- Coin instance associated with one adjacent-bias MCSP separation slice. -/
def AdjacentBiasMCSPThresholdSeparationFacts.instance
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    CoinProblemInstance :=
  truthTableCoinInstance
    n
    (facts.qLow n)
    (facts.qHigh n)
    (facts.qLow_nonneg n)
    (facts.qHigh_le_one n)
    (facts.qLow_lt_qHigh n)

/--
The adjacent-bias separation facts mechanically solve their own adjacent-bias
coin instance.
-/
theorem AdjacentBiasMCSPThresholdSeparationFacts.toSolvesCoin
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    SolvesCoinProblem
      (facts.instance n)
      (exactTreeMCSPThresholdHardDecision n (facts.threshold n))
      (facts.advantage n) := by
  exact solvesCoinProblem_of_acceptanceProbability_bounds
    (inst := facts.instance n)
    (A := exactTreeMCSPThresholdHardDecision n (facts.threshold n))
    (adv := facts.advantage n)
    (lowAcceptanceUpper := facts.lowHardAcceptanceUpper n)
    (highAcceptanceLower := facts.highHardAcceptanceLower n)
    (facts.low_hard_acceptance_le n)
    (facts.high_hard_acceptance_ge n)
    (facts.advantage_gap n)

/--
Read adjacent-bias MCSP threshold separation as a generic coin-distinguisher
family.  This is the faithful interface for later translation steps: the
translator may construct a new distinguisher instead of preserving this exact
MCSP threshold predicate.
-/
noncomputable def CoinDistinguisherFamily.of_adjacentBiasMCSP
    (facts : AdjacentBiasMCSPThresholdSeparationFacts) :
    CoinDistinguisherFamily where
  sampleBits := fun n => Pnp3.Models.Partial.tableLen n
  lowBias := facts.qLow
  highBias := facts.qHigh
  low_nonneg := facts.qLow_nonneg
  high_le_one := facts.qHigh_le_one
  bias_gap := facts.qLow_lt_qHigh
  advantage := facts.advantage
  algorithm := fun n => exactTreeMCSPThresholdHardDecision n (facts.threshold n)
  solves := fun n => facts.toSolvesCoin n

/--
If circuits in `C` compute the adjacent-bias MCSP hard-threshold decisions,
then they realize the corresponding generic adjacent-bias coin-distinguisher
family.
-/
noncomputable def CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
    (C : CircuitFamilyClass)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (circuit :
      ∀ n : Nat, C.Family (Pnp3.Models.Partial.tableLen n))
    (computes :
      ∀ n : Nat, ∀ x : BitVec (Pnp3.Models.Partial.tableLen n),
        C.eval (circuit n) x =
          exactTreeMCSPThresholdHardDecision n (facts.threshold n) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ n : Nat,
        C.size (circuit n) ≤ sizeBound n) :
    CircuitCoinDistinguisherFamily
      C
      (CoinDistinguisherFamily.of_adjacentBiasMCSP facts) where
  circuit := circuit
  computes := computes
  sizeBound := sizeBound
  size_le := size_le

/--
Paper-style translation contract from an arbitrary source coin distinguisher to
the half-vs-fair coin formulation.

The translated algorithm is intentionally a new Boolean function: the
published masking/averaging argument constructs a new deterministic
distinguisher from the old one, rather than proving that the same predicate
works on the target biases.
-/
structure CoinDistinguisherToHalfVsFairTranslationContract
    (source : CoinDistinguisherFamily)
    (hardness : HalfVsFairTruthTableCoinHardness) where
  translatedAlgorithm :
    ∀ n : Nat, BitVec (hardness.instance n).sampleBits → Bool
  solvesTarget :
    ∀ n : Nat,
      SolvesCoinProblem
        (hardness.instance n)
        (translatedAlgorithm n)
        (hardness.advantage n)

/-- Read the solved half-vs-fair coin certificate from a translation contract. -/
theorem CoinDistinguisherToHalfVsFairTranslationContract.solvesCoin
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (translation :
      CoinDistinguisherToHalfVsFairTranslationContract source hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (translation.translatedAlgorithm n)
      (hardness.advantage n) :=
  translation.solvesTarget n

/--
Class/size-preserving version of the paper-style translation.

This is the lower-bound-facing form of Claim 2.4: a circuit solving the source
coin problem can be translated into a circuit in the same class solving the
half-vs-fair target problem, without increasing size.
-/
structure CoinTranslationPreservesClass
    (C : CircuitFamilyClass)
    (source : CoinDistinguisherFamily)
    (target : HalfVsFairTruthTableCoinHardness) where
  translateCircuit :
    ∀ n : Nat,
      C.Family (source.sampleBits n) →
        C.Family (target.instance n).sampleBits
  size_le :
    ∀ n : Nat, ∀ c : C.Family (source.sampleBits n),
      C.size (translateCircuit n c) ≤ C.size c
  solvesTarget_of_solvesSource :
    ∀ n : Nat,
      ∀ c : C.Family (source.sampleBits n),
        SolvesCoinProblem
          (source.instance n)
          (fun x => C.eval c x)
          (source.advantage n) →
        SolvesCoinProblem
          (target.instance n)
          (fun x => C.eval (translateCircuit n c) x)
          (target.advantage n)

/--
Bias/sample matching data needed to instantiate the masking translation between
a source coin-distinguisher family and a half-vs-fair target.
-/
structure CoinMaskingTranslationSetup
    (source : CoinDistinguisherFamily)
    (target : HalfVsFairTruthTableCoinHardness) where
  params : Nat → MaskingBiasParams
  sampleBits_eq :
    ∀ n : Nat, source.sampleBits n = (target.instance n).sampleBits
  source_low_eq :
    ∀ n : Nat, source.lowBias n = (params n).lowSourceBias
  source_high_eq :
    ∀ n : Nat, source.highBias n = (params n).highSourceBias
  target_low_eq :
    ∀ n : Nat, (target.instance n).lowBias = (params n).lowTargetBias
  target_high_eq :
    ∀ n : Nat, (target.instance n).highBias = (params n).highTargetBias
  advantage_le :
    ∀ n : Nat, target.advantage n ≤ source.advantage n

private def castFamily
    {C : CircuitFamilyClass}
    {m n : Nat}
    (h : m = n)
    (c : C.Family m) : C.Family n :=
  cast (congrArg C.Family h) c

private def castBitVec
    {m n : Nat}
    (h : m = n)
    (x : BitVec m) : BitVec n :=
  cast (congrArg BitVec h) x

private theorem size_castFamily
    {C : CircuitFamilyClass}
    {m n : Nat}
    (h : m = n)
    (c : C.Family m) :
    C.size (castFamily h c) = C.size c := by
  cases h
  rfl

private theorem eval_castFamily
    {C : CircuitFamilyClass}
    {m n : Nat}
    (h : m = n)
    (c : C.Family m)
    (x : BitVec n) :
    C.eval (castFamily h c) x =
      C.eval c (castBitVec h.symm x) := by
  cases h
  rfl

private theorem acceptanceProbability_castDomain
    {m n : Nat}
    (h : m = n)
    (bias : Rat)
    (A : BitVec m → Bool) :
    acceptanceProbability bias (fun x : BitVec n => A (castBitVec h.symm x)) =
      acceptanceProbability bias A := by
  cases h
  rfl

/--
Derive the class/size-preserving coin translation from input-masking closure
and the masking probability facts.

The translated circuit uses a mask chosen solely from the circuit and target
biases, before any source-solving proof is supplied. The correctness proof then
uses maximality of that mask plus the probability-side masking facts.
-/
noncomputable def coinTranslationPreservesClass_of_maskingSetup
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {target : HalfVsFairTruthTableCoinHardness}
    (closed : ClosedUnderInputMasking C)
    (setup : CoinMaskingTranslationSetup source target)
    (facts :
      ∀ n : Nat,
        CoinMaskingTranslationFacts (setup.params n) (source.sampleBits n)) :
    CoinTranslationPreservesClass C source target where
  translateCircuit := fun n c =>
    castFamily (setup.sampleBits_eq n)
      (closed.maskCircuit
        (bestMaskForCircuit
          (setup.params n).lowTargetBias
          (setup.params n).highTargetBias
          c)
        c)
  size_le := by
    intro n c
    rw [size_castFamily]
    exact
      closed.size_maskCircuit
        (bestMaskForCircuit
          (setup.params n).lowTargetBias
          (setup.params n).highTargetBias
          c)
        c
  solvesTarget_of_solvesSource := by
    intro n c hSource
    let keep : BitVec (source.sampleBits n) :=
      bestMaskForCircuit
        (setup.params n).lowTargetBias
        (setup.params n).highTargetBias
        c
    have hEval :
        ∀ x : BitVec (target.instance n).sampleBits,
          C.eval
              (castFamily (setup.sampleBits_eq n)
                (closed.maskCircuit keep c))
              x =
            C.eval c (maskVec keep (castBitVec (setup.sampleBits_eq n).symm x)) := by
      intro x
      rw [eval_castFamily]
      exact closed.eval_maskCircuit keep c (castBitVec (setup.sampleBits_eq n).symm x)
    have hHighEval :
        acceptanceProbability (target.instance n).highBias
            (fun x : BitVec (target.instance n).sampleBits =>
              C.eval
                (castFamily (setup.sampleBits_eq n)
                  (closed.maskCircuit keep c))
                x) =
          acceptanceProbability (target.instance n).highBias
            (fun y : BitVec (source.sampleBits n) =>
              C.eval c (maskVec keep y)) := by
      rw [← acceptanceProbability_castDomain
        (setup.sampleBits_eq n)
        (target.instance n).highBias
        (fun y : BitVec (source.sampleBits n) => C.eval c (maskVec keep y))]
      congr
      funext x
      exact hEval x
    have hLowEval :
        acceptanceProbability (target.instance n).lowBias
            (fun x : BitVec (target.instance n).sampleBits =>
              C.eval
                (castFamily (setup.sampleBits_eq n)
                  (closed.maskCircuit keep c))
                x) =
          acceptanceProbability (target.instance n).lowBias
            (fun y : BitVec (source.sampleBits n) =>
              C.eval c (maskVec keep y)) := by
      rw [← acceptanceProbability_castDomain
        (setup.sampleBits_eq n)
        (target.instance n).lowBias
        (fun y : BitVec (source.sampleBits n) => C.eval c (maskVec keep y))]
      congr
      funext x
      exact hEval x
    have hSourceAdv :
        source.advantage n ≤
          acceptanceProbability (setup.params n).highSourceBias
              (fun x => C.eval c x) -
            acceptanceProbability (setup.params n).lowSourceBias
              (fun x => C.eval c x) := by
      simpa [SolvesCoinProblem, acceptanceGap, CoinDistinguisherFamily.instance,
        setup.source_low_eq n, setup.source_high_eq n] using hSource
    have hBest :
        source.advantage n ≤
          fixedMaskAcceptanceAdvantage
            (bestMaskForCircuit
              (setup.params n).lowTargetBias
              (setup.params n).highTargetBias
              c)
            (setup.params n).lowTargetBias
            (setup.params n).highTargetBias
            (fun x => C.eval c x) :=
      source_advantage_le_bestMask_fixed_advantage
        (facts n)
        c
        hSourceAdv
    have hTargetAdv :
        target.advantage n ≤
          fixedMaskAcceptanceAdvantage
            keep
            (setup.params n).lowTargetBias
            (setup.params n).highTargetBias
            (fun x => C.eval c x) :=
      le_trans (setup.advantage_le n) hBest
    unfold SolvesCoinProblem acceptanceGap
    rw [hHighEval, hLowEval, setup.target_high_eq n, setup.target_low_eq n]
    simpa [fixedMaskAcceptanceAdvantage, keep] using hTargetAdv

/--
Coin-distinguisher family for a half-vs-fair target, parameterized by the
actual Boolean algorithms used on each slice.
-/
noncomputable def halfVsFairCoinDistinguisherFamily
    (hardness : HalfVsFairTruthTableCoinHardness)
    (A : ∀ n : Nat, BitVec (hardness.instance n).sampleBits → Bool)
    (hSolves :
      ∀ n : Nat,
        SolvesCoinProblem
          (hardness.instance n)
          (A n)
          (hardness.advantage n)) :
    CoinDistinguisherFamily where
  sampleBits := fun n => (hardness.instance n).sampleBits
  lowBias := fun n => (hardness.instance n).lowBias
  highBias := fun n => (hardness.instance n).highBias
  low_nonneg := fun n => (hardness.instance n).low_nonneg
  high_le_one := fun n => (hardness.instance n).high_le_one
  bias_gap := fun n => (hardness.instance n).bias_gap
  advantage := hardness.advantage
  algorithm := A
  solves := fun n => hSolves n

/--
Translate a circuit-realized source coin distinguisher through a class/size
preserving translation contract.
-/
noncomputable def CircuitCoinDistinguisherFamily.translate_to_halfVsFair
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (realized : CircuitCoinDistinguisherFamily C source)
    (translation : CoinTranslationPreservesClass C source hardness) :
    CircuitCoinDistinguisherFamily
      C
      (halfVsFairCoinDistinguisherFamily
        hardness
        (fun n x =>
          C.eval (translation.translateCircuit n (realized.circuit n)) x)
        (fun n =>
          translation.solvesTarget_of_solvesSource
            n
            (realized.circuit n)
            (realized.solves n))) where
  circuit := fun n => translation.translateCircuit n (realized.circuit n)
  computes := by
    intro n x
    rfl
  sizeBound := realized.sizeBound
  size_le := fun n =>
    le_trans
      (translation.size_le n (realized.circuit n))
      (realized.size_le n)

/--
The lower-bound-facing readout of a class-preserving coin translation: a
circuit-realized source solver yields a bounded circuit solver for the target
half-vs-fair coin instance.
-/
theorem BoundedClassSolvesCoinProblem_of_translated_realization
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (realized : CircuitCoinDistinguisherFamily C source)
    (translation : CoinTranslationPreservesClass C source hardness)
    (n : Nat) :
    BoundedClassSolvesCoinProblem
      C
      (hardness.instance n)
      (hardness.advantage n)
      (realized.sizeBound n) :=
  (realized.translate_to_halfVsFair translation).boundedSolves n

/--
Generic contradiction bridge: once a source coin solver is circuit-realized and
the translation preserves the circuit class and size, the published half-vs-fair
coin lower-bound contract rules out any slice whose translated size fits under
the contract's bound.
-/
theorem false_of_translated_realization_and_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    {source : CoinDistinguisherFamily}
    {p depth n : Nat}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hp : Nat.Prime p)
    (realized :
      CircuitCoinDistinguisherFamily
        (model.classOf p depth)
        source)
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        source
        hardness)
    (hSize :
      realized.sizeBound n ≤ contract.sizeBound depth n) :
    False := by
  have hTargetSmall :
      BoundedClassSolvesCoinProblem
        (model.classOf p depth)
        (hardness.instance n)
        (hardness.advantage n)
        (realized.sizeBound n) :=
    BoundedClassSolvesCoinProblem_of_translated_realization
      realized
      translation
      n
  have hTarget :
      BoundedClassSolvesCoinProblem
        (model.classOf p depth)
        (hardness.instance n)
        (hardness.advantage n)
        (contract.sizeBound depth n) :=
    BoundedClassSolvesCoinProblem.mono_size hTargetSmall hSize
  exact contract.excludes_small_solver hp hTarget

/--
Adjacent-bias specialization of the generic contradiction bridge.
-/
theorem false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {p depth n : Nat}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hp : Nat.Prime p)
    (realized :
      CircuitCoinDistinguisherFamily
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts))
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (hSize :
      realized.sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_translated_realization_and_AC0pCoinLowerBound
    contract
    hp
    realized
    translation
    hSize

/--
Contradiction form starting from an explicit `AC0[p]` circuit family computing
the adjacent-bias MCSP hard-threshold decisions.
-/
theorem false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (circuit :
      ∀ m : Nat, (model.classOf p depth).Family (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : BitVec (Pnp3.Models.Partial.tableLen m),
        (model.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.classOf p depth).size (circuit m) ≤ sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False := by
  let realized :=
    CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
      (model.classOf p depth)
      facts
      circuit
      computes
      sizeBound
      size_le
  exact
    false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
      contract
      hp
      realized
      translation
      hSize

/-- Adjacent-bias specialization of the generic half-vs-fair translation contract. -/
abbrev AdjacentBiasToHalfVsFairCoinSolverTranslationContract
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) : Type :=
  CoinDistinguisherToHalfVsFairTranslationContract
    (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
    hardness

/--
Strong direct translation target.

This asks the same MCSP hard-threshold predicate to satisfy the half-vs-fair
acceptance bounds.  That is stronger than the published translation argument,
which generally constructs a translated distinguisher/circuit by randomized
masking and averaging.
-/
structure AdjacentBiasToHalfVsFairRejectionTranslationContract
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) where
  lowAcceptanceUpper : Nat → Rat
  fairAcceptanceLower : Nat → Rat
  low_rejection_acceptance_le :
    ∀ n : Nat,
      acceptanceProbability (hardness.instance n).lowBias
          (exactTreeMCSPThresholdHardDecision n (facts.threshold n)) ≤
        lowAcceptanceUpper n
  fair_rejection_acceptance_ge :
    ∀ n : Nat,
      fairAcceptanceLower n ≤
        acceptanceProbability (hardness.instance n).highBias
          (exactTreeMCSPThresholdHardDecision n (facts.threshold n))
  advantage_gap :
    ∀ n : Nat,
      hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n

/--
Named constructor for the MCSP-side half-vs-fair reduction contract from the
three distribution facts that remain after the exact threshold predicate is
fixed.
-/
def HalfVsFairMCSPCoinReductionContract.of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness where
  threshold := threshold
  lowAcceptanceUpper := lowAcceptanceUpper
  fairAcceptanceLower := fairAcceptanceLower
  low_acceptance_le := low_acceptance_le
  fair_acceptance_ge := fair_acceptance_ge
  advantage_gap := advantage_gap

/-- Constructor for the corrected-polarity rejection contract. -/
def HalfVsFairMCSPCoinRejectionContract.of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_rejection_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdHardDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_rejection_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdHardDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness where
  threshold := threshold
  lowAcceptanceUpper := lowAcceptanceUpper
  fairAcceptanceLower := fairAcceptanceLower
  low_rejection_acceptance_le := low_rejection_acceptance_le
  fair_rejection_acceptance_ge := fair_rejection_acceptance_ge
  advantage_gap := advantage_gap

/--
Build the half-vs-fair reduction contract from probability-mass bounds for the
proof-level tree-MCSP predicate itself.

This is the next decomposition layer below `of_distributionFacts`: downstream
counting or concentration arguments should now target the mass of
`treeMCSPPredicateDecision`, not the exact decision wrapper.
-/
def HalfVsFairMCSPCoinReductionContract.of_treeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (treeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness :=
  HalfVsFairMCSPCoinReductionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    (fun n =>
      acceptanceProbability_exactTreeMCSPThresholdDecision_le_of_treeMCSPPredicateDecision_bound
        (n := n)
        (threshold := threshold n)
        (bias := (hardness.instance n).lowBias)
        (q := lowAcceptanceUpper n)
        (hardness.instance n).low_nonneg
        (hardness.instance n).low_le_one
        (low_mass_le n))
    (fun n =>
      treeMCSPPredicateDecision_bound_le_acceptanceProbability_exactTreeMCSPThresholdDecision
        (n := n)
        (threshold := threshold n)
        (bias := (hardness.instance n).highBias)
        (q := fairAcceptanceLower n)
        (hardness.instance n).high_nonneg
        (hardness.instance n).high_le_one
        (fair_mass_ge n))
    advantage_gap

/--
Build the corrected-polarity rejection contract from probability-mass bounds
for the complement of the proof-level tree-MCSP predicate.
-/
def HalfVsFairMCSPCoinRejectionContract.of_notTreeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_not_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (notTreeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_not_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (notTreeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    (fun n => by
      simpa [exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision]
        using low_not_mass_le n)
    (fun n => by
      simpa [exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision]
        using fair_not_mass_ge n)
    advantage_gap

/--
In the half-vs-fair regime, `highBias` is the fair side `1 / 2`.  Therefore the
Shannon-counting upper bound applies directly to the `highBias` mass of
low-tree-complexity truth tables.
-/
theorem halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    acceptanceProbability (hardness.instance n).highBias
        (treeMCSPPredicateDecision n threshold) ≤
      treeMCSPCountRatio n threshold := by
  simpa [HalfVsFairTruthTableCoinHardness.instance, halfVsFairCoinInstance] using
    fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio n threshold

/--
Convenience form: if the Shannon-counting ratio is bounded by `q`, then the
fair-side mass of low-tree-complexity truth tables is at most `q`.
-/
theorem halfVsFair_highBias_treeMCSPPredicateDecision_le_of_countRatio_le
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hRatio :
      treeMCSPCountRatio n threshold ≤ q) :
    acceptanceProbability (hardness.instance n).highBias
        (treeMCSPPredicateDecision n threshold) ≤ q :=
  le_trans
    (halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
      (hardness := hardness) n threshold)
    hRatio

/--
Correct-polarity fair-side lower bound: under `highBias = 1 / 2`, the
hard-table complement of the low-complexity predicate has mass at least one
minus the Shannon-counting ratio.
-/
theorem one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    1 - treeMCSPCountRatio n threshold ≤
      acceptanceProbability (hardness.instance n).highBias
        (notTreeMCSPPredicateDecision n threshold) := by
  simpa [
      HalfVsFairTruthTableCoinHardness.instance,
      halfVsFairCoinInstance,
      treeMCSPCountRatio
    ] using
    one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
      n threshold

/--
Exact hard-decision form of
`one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision`.
-/
theorem one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    1 - treeMCSPCountRatio n threshold ≤
      acceptanceProbability (hardness.instance n).highBias
        (exactTreeMCSPThresholdHardDecision n threshold) := by
  simpa [exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision] using
    one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision
      (hardness := hardness) n threshold

/--
Convenience form: any upper bound `q` on the Shannon-counting ratio yields a
fair-side lower bound `1 - q` for the corrected-polarity hard-table decision.
-/
theorem one_sub_countRatioUpper_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hRatio :
      treeMCSPCountRatio n threshold ≤ q) :
    1 - q ≤
      acceptanceProbability (hardness.instance n).highBias
        (exactTreeMCSPThresholdHardDecision n threshold) := by
  have hBase :=
    one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
      (hardness := hardness) n threshold
  linarith

/--
Low-bias upper bound for the corrected-polarity predicate from a lower bound on
the low-bias mass of low-complexity truth tables.
-/
theorem halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hMass :
      1 - q ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n threshold)) :
    acceptanceProbability (hardness.instance n).lowBias
        (notTreeMCSPPredicateDecision n threshold) ≤ q := by
  simpa [notTreeMCSPPredicateDecision] using
    acceptanceProbability_not_le_of_one_sub_le
      (bias := (hardness.instance n).lowBias)
      (A := treeMCSPPredicateDecision n threshold)
      (q := q)
      hMass

/--
Exact hard-decision version of
`halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower`.
-/
theorem halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hMass :
      1 - q ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n threshold)) :
    acceptanceProbability (hardness.instance n).lowBias
        (exactTreeMCSPThresholdHardDecision n threshold) ≤ q := by
  simpa [exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision] using
    halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower
      (hardness := hardness)
      (n := n)
      (threshold := threshold)
      (q := q)
      hMass

/--
Source-facing constructor for the corrected-polarity MCSP/coin reduction.

The remaining probabilistic input is now stated in the mathematically natural
direction: the low-bias side has large low-complexity mass, while the fair side
is controlled by the already-proved Shannon-counting ratio.
-/
def HalfVsFairMCSPCoinRejectionContract.of_treeMCSPPredicateBiasedLower_and_fairCounting
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_lowComplexity_mass_ge :
      ∀ n : Nat,
        1 - lowAcceptanceUpper n ≤
          acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)))
    (fair_count_ratio_le :
      ∀ n : Nat,
        treeMCSPCountRatio n (threshold n) ≤
          1 - fairAcceptanceLower n)
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    (fun n =>
      halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
        (hardness := hardness)
        (n := n)
        (threshold := threshold n)
        (q := lowAcceptanceUpper n)
        (low_lowComplexity_mass_ge n))
    (fun n => by
      have hFairBase :
          1 - (1 - fairAcceptanceLower n) ≤
            acceptanceProbability (hardness.instance n).highBias
              (exactTreeMCSPThresholdHardDecision n (threshold n)) :=
        one_sub_countRatioUpper_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
          (hardness := hardness)
          (n := n)
          (threshold := threshold n)
          (q := 1 - fairAcceptanceLower n)
          (fair_count_ratio_le n)
      linarith)
    advantage_gap

/--
The self-normalized fair lower bound used by
`of_biasedLowComplexityMassFacts`.
-/
theorem treeMCSPCountRatio_le_one_sub_self_fairLower
    (n threshold : Nat) :
    treeMCSPCountRatio n threshold ≤
      1 - (1 - treeMCSPCountRatio n threshold) := by
  linarith

/--
Source-facing constructor for the corrected-polarity route from the explicit
biased/easy mass target.

The fair-side lower bound is fixed to the Shannon-counting value
`1 - treeMCSPCountRatio`; the only remaining non-arithmetic source input is the
large low-bias mass of low-complexity truth tables.
-/
noncomputable def HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (facts : HalfVsFairBiasedLowComplexityMassFacts hardness)
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + facts.lowAcceptanceUpper n ≤
          1 - treeMCSPCountRatio n (facts.threshold n)) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_treeMCSPPredicateBiasedLower_and_fairCounting
    facts.threshold
    facts.lowAcceptanceUpper
    (fun n => 1 - treeMCSPCountRatio n (facts.threshold n))
    facts.low_lowComplexity_mass_ge
    (fun n => treeMCSPCountRatio_le_one_sub_self_fairLower n (facts.threshold n))
    advantage_gap

/--
Build the corrected-polarity half-vs-fair rejection contract via the
paper-faithful adjacent-bias source plus an explicit translation contract.
-/
def HalfVsFairMCSPCoinRejectionContract.of_adjacentBiasSeparation_and_translation
    {hardness : HalfVsFairTruthTableCoinHardness}
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (translation :
      AdjacentBiasToHalfVsFairRejectionTranslationContract facts hardness) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_distributionFacts
    facts.threshold
    translation.lowAcceptanceUpper
    translation.fairAcceptanceLower
    translation.low_rejection_acceptance_le
    translation.fair_rejection_acceptance_ge
    translation.advantage_gap

/--
Recover the original monolithic coin-solving statement from the decomposed
reduction contract.
-/
theorem HalfVsFairMCSPCoinReductionContract.exact_solvesCoin
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.toHalfVsFairMCSPCoinAcceptanceProfile.exact_solvesCoin n

/-- The corrected-polarity rejection contract solves the half-vs-fair coin problem. -/
theorem HalfVsFairMCSPCoinRejectionContract.hard_solvesCoin
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinRejectionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdHardDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.toHalfVsFairMCSPCoinRejectionProfile.hard_solvesCoin n

/--
Exact thresholded MCSP language attached to one half-vs-fair reduction
contract.
-/
noncomputable def halfVsFairMCSPCoinLanguage
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) : BitVecLanguage :=
  exactTreeMCSPThresholdLanguage n (contract.threshold n)

/--
Pointwise lower-bound schedule attached to one half-vs-fair reduction contract.

The reduction contract fixes only the thresholded language; the forbidden size
bound still comes from the target-class lower-bound contract.
-/
def halfVsFairMCSPCoinLowerBound
    {hardness : HalfVsFairTruthTableCoinHardness}
    (_contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n maxSize : Nat) : Nat → Nat :=
  exactTreeMCSPThresholdLowerBound n maxSize

/--
Read the smaller theorem-facing reduction contract back as the older witness
package expected by the first-layer `AC0[p]` route.
-/
noncomputable def HalfVsFairMCSPCoinReductionContract.toWitness
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    HalfVsFairMCSPCoinReductionWitness hardness n where
  oracle := {
    threshold := contract.threshold n
    decide := exactTreeMCSPThresholdDecision n (contract.threshold n)
    correct := exactTreeMCSPThresholdDecision_spec
  }
  solvesCoin := contract.exact_solvesCoin n

/-- The witness reconstructed from the smaller contract has the expected threshold. -/
@[simp] theorem HalfVsFairMCSPCoinReductionContract.toWitness_threshold
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    (contract.toWitness n).oracle.threshold = contract.threshold n :=
  rfl

/-- The witness reconstructed from the smaller contract uses the exact slice decision. -/
@[simp] theorem HalfVsFairMCSPCoinReductionContract.toWitness_decide
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    (contract.toWitness n).oracle.decide =
      exactTreeMCSPThresholdDecision n (contract.threshold n) :=
  rfl

end AlgorithmsToLowerBounds
end Pnp4
