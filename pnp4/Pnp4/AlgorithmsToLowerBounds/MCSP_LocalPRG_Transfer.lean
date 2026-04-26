import Pnp4.AlgorithmsToLowerBounds.LocalPRG
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction
import Counting.ShannonCounting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Pnp4
namespace AlgorithmsToLowerBounds

/-- At fair bias, every bit has weight `1 / 2`. -/
theorem bernoulliBitWeight_fair
    (b : Bool) :
    bernoulliBitWeight ((1 : Rat) / 2) b = (1 : Rat) / 2 := by
  cases b <;> norm_num [bernoulliBitWeight]

/-- Under fair bias, every bit-vector has uniform product weight `2^-m`. -/
theorem productBiasWeight_fair
    {m : Nat}
    (x : BitVec m) :
    productBiasWeight ((1 : Rat) / 2) x =
      (1 : Rat) / (2 ^ m : Rat) := by
  classical
  calc
    productBiasWeight ((1 : Rat) / 2) x
        = ∏ _i : Fin m, ((1 : Rat) / 2) := by
            unfold productBiasWeight
            apply Finset.prod_congr rfl
            intro i _hi
            exact bernoulliBitWeight_fair (x i)
    _ = ((1 : Rat) / 2) ^ m := by
            simp
    _ = (1 : Rat) / (2 ^ m : Rat) := by
            rw [div_pow]
            norm_num

/--
The product distribution with bias `1 / 2` is the uniform distribution over
bit-vectors.
-/
theorem acceptanceProbability_fair_eq_bitVecAcceptanceProbability
    {m : Nat}
    (A : BitVec m → Bool) :
    acceptanceProbability ((1 : Rat) / 2) A =
      bitVecAcceptanceProbability A := by
  classical
  let accepted : Finset (BitVec m) :=
    (Finset.univ : Finset (BitVec m)).filter (fun x => A x = true)
  have hSum :
      acceptanceProbability ((1 : Rat) / 2) A =
        ∑ x ∈ accepted, productBiasWeight ((1 : Rat) / 2) x := by
    unfold acceptanceProbability
    rw [← Finset.sum_filter]
  calc
    acceptanceProbability ((1 : Rat) / 2) A
        = ∑ x ∈ accepted, productBiasWeight ((1 : Rat) / 2) x := hSum
    _ = ∑ _x ∈ accepted, (1 : Rat) / (2 ^ m : Rat) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact productBiasWeight_fair x
    _ = ((accepted.card : Rat) / (2 ^ m : Rat)) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = bitVecAcceptanceProbability A := by
          simp [bitVecAcceptanceProbability, accepted]

/-- Uniform acceptance of a Boolean complement is one minus acceptance. -/
theorem bitVecAcceptanceProbability_not
    {m : Nat}
    (A : BitVec m → Bool) :
    bitVecAcceptanceProbability (fun x => ! A x) =
      1 - bitVecAcceptanceProbability A := by
  classical
  let accepted : Finset (BitVec m) :=
    (Finset.univ : Finset (BitVec m)).filter (fun x => A x = true)
  let rejected : Finset (BitVec m) :=
    (Finset.univ : Finset (BitVec m)).filter (fun x => (! A x) = true)
  have hDisjoint : Disjoint accepted rejected := by
    rw [Finset.disjoint_left]
    intro x hxAccepted hxRejected
    have hA : A x = true := (Finset.mem_filter.mp hxAccepted).2
    have hNotA : (! A x) = true := (Finset.mem_filter.mp hxRejected).2
    cases hAx : A x <;> simp [hAx] at hA hNotA
  have hUnion :
      accepted ∪ rejected = (Finset.univ : Finset (BitVec m)) := by
    ext x
    by_cases hA : A x = true
    · simp [accepted, rejected, hA]
    · have hFalse : A x = false := by
        cases hAx : A x
        · rfl
        · exact (hA hAx).elim
      simp [accepted, rejected, hFalse]
  have hCard : accepted.card + rejected.card = 2 ^ m := by
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion]
    simp
  have hCardRat :
      (accepted.card : Rat) + (rejected.card : Rat) = (2 ^ m : Rat) := by
    exact_mod_cast hCard
  have hDenNeZero : (2 ^ m : Rat) ≠ 0 := by positivity
  have hRejected :
      (rejected.card : Rat) / (2 ^ m : Rat) =
        1 - (accepted.card : Rat) / (2 ^ m : Rat) := by
    field_simp [hDenNeZero]
    linarith
  calc
    bitVecAcceptanceProbability (fun x => ! A x)
        = (rejected.card : Rat) / (2 ^ m : Rat) := by
            simp [bitVecAcceptanceProbability, rejected]
    _ = 1 - (accepted.card : Rat) / (2 ^ m : Rat) := hRejected
    _ = 1 - bitVecAcceptanceProbability A := by
            simp [bitVecAcceptanceProbability, accepted]

/--
If a predicate has uniform acceptance at most `q`, then its Boolean complement
has uniform acceptance at least `1 - q`.
-/
theorem one_sub_upper_le_bitVecAcceptanceProbability_not
    {m : Nat}
    {A : BitVec m → Bool}
    {q : Rat}
    (hA : bitVecAcceptanceProbability A ≤ q) :
    1 - q ≤ bitVecAcceptanceProbability (fun x => ! A x) := by
  rw [bitVecAcceptanceProbability_not]
  linarith

/--
Fair product-distribution specialization of the complement lower-bound lemma.
-/
theorem one_sub_upper_le_acceptanceProbability_fair_not
    {m : Nat}
    {A : BitVec m → Bool}
    {q : Rat}
    (hA : acceptanceProbability ((1 : Rat) / 2) A ≤ q) :
    1 - q ≤ acceptanceProbability ((1 : Rat) / 2) (fun x => ! A x) := by
  rw [acceptanceProbability_fair_eq_bitVecAcceptanceProbability] at hA
  rw [acceptanceProbability_fair_eq_bitVecAcceptanceProbability]
  exact one_sub_upper_le_bitVecAcceptanceProbability_not hA

/--
Any truth table accepted by the proof-level tree-MCSP predicate at threshold
`s` is one of the Shannon-counting "easy functions" of size at most `s`.
-/
lemma mem_easyFunctions_of_treeMCSPPredicate
    {n s : Nat}
    {tt : TruthTable n}
    (h : treeMCSPPredicate n s tt) :
    tt ∈ Pnp3.Counting.easyFunctions n s := by
  classical
  rcases h with ⟨c, hcSize, hComp⟩
  have hmemC : c ∈ Pnp3.Counting.circuitsOfSizeAtMost n s :=
    Pnp3.Counting.mem_circuitsOfSizeAtMost c s hcSize
  have hEq : tt = Pnp3.Counting.circuitToTable c := by
    exact Pnp3.Counting.circuitComputes_eq_circuitToTable c tt hComp
  have hImage :
      Pnp3.Counting.circuitToTable c ∈ Pnp3.Counting.easyFunctions n s :=
    Finset.mem_image.mpr ⟨c, hmemC, rfl⟩
  simpa [hEq] using hImage

/--
Counting ratio for truth tables on `n` variables accepted by an exact
tree-MCSP threshold oracle at threshold `threshold`.

This is the Shannon-counting upper-bound target reused by both the local-PRG
route and the half-vs-fair MCSP/coin route.
-/
noncomputable def treeMCSPCountRatio
    (n threshold : Nat) : Rat :=
  (Pnp3.Models.circuitCountBound n threshold : Rat) /
    (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)

/--
If a thresholded tree-MCSP oracle has threshold at least the PRG image-size
bound, then every PRG output is accepted by that oracle.
-/
theorem TruthTableLocalPRG.oracle_accepts_all_outputs
    {n : Nat}
    (prg : TruthTableLocalPRG n)
    (oracle : MCSPThresholdOracle n)
    (hThreshold : prg.imageSizeBound ≤ oracle.threshold) :
    ∀ seed : BitVec prg.seedBits, oracle.decide (prg.gen seed) = true := by
  intro seed
  have hEasyAtImage :
      treeMCSPPredicate n prg.imageSizeBound (prg.gen seed) :=
    prg.image_easy seed
  have hEasyAtThreshold :
      treeMCSPPredicate n oracle.threshold (prg.gen seed) :=
    treeMCSPPredicate_mono hThreshold hEasyAtImage
  exact (oracle.correct (prg.gen seed)).2 hEasyAtThreshold

/--
Counting upper bound on the uniform acceptance probability of any exact
thresholded tree-MCSP oracle.
-/
theorem uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle
    {n : Nat}
    (oracle : MCSPThresholdOracle n) :
    uniformTruthTableAcceptanceProbability oracle.decide ≤
      (Pnp3.Models.circuitCountBound n oracle.threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) := by
  classical
  let accepted : Finset (TruthTable n) :=
    (Finset.univ : Finset (TruthTable n)).filter (fun tt => oracle.decide tt = true)
  have hSubset :
      accepted ⊆ Pnp3.Counting.easyFunctions n oracle.threshold := by
    intro tt htt
    have hDecide : oracle.decide tt = true :=
      (Finset.mem_filter.mp htt).2
    have hPred : treeMCSPPredicate n oracle.threshold tt :=
      (oracle.correct tt).1 hDecide
    exact mem_easyFunctions_of_treeMCSPPredicate hPred
  have hCardLeEasy :
      accepted.card ≤ (Pnp3.Counting.easyFunctions n oracle.threshold).card :=
    Finset.card_le_card hSubset
  have hCardLeBound :
      accepted.card ≤ Pnp3.Models.circuitCountBound n oracle.threshold :=
    Nat.le_trans hCardLeEasy (Pnp3.Counting.card_easyFunctions_le n oracle.threshold)
  have hCardLeBoundRat :
      (accepted.card : Rat) ≤
        (Pnp3.Models.circuitCountBound n oracle.threshold : Rat) := by
    exact_mod_cast hCardLeBound
  have hDenNonneg :
      (0 : Rat) ≤ (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) := by
    positivity
  have hDiv :
      ((accepted.card : Rat) / (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) ≤
        ((Pnp3.Models.circuitCountBound n oracle.threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) :=
    div_le_div_of_nonneg_right hCardLeBoundRat hDenNonneg
  simpa [uniformTruthTableAcceptanceProbability, bitVecAcceptanceProbability, accepted] using hDiv

/--
Boolean single-slice MCSP language: at input length `2^n`, return the exact
thresholded tree-MCSP predicate for `threshold`; off that slice, return `false`.
-/
noncomputable def exactTreeMCSPThresholdDecision
    (n threshold : Nat) : TruthTable n → Bool := by
  classical
  intro tt
  exact decide (treeMCSPPredicate n threshold tt)

/-- Specification lemma for the exact Boolean thresholded tree-MCSP predicate. -/
theorem exactTreeMCSPThresholdDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    exactTreeMCSPThresholdDecision n threshold tt = true ↔
      treeMCSPPredicate n threshold tt := by
  classical
  simp [exactTreeMCSPThresholdDecision]

/--
Complement of the exact thresholded tree-MCSP predicate.  This is the correct
polarity for the half-vs-fair coin route when the high-bias side is the fair
coin: random fair truth tables should be rejected by the low-complexity
predicate and accepted by this hard-table predicate.
-/
noncomputable def exactTreeMCSPThresholdHardDecision
    (n threshold : Nat) : TruthTable n → Bool :=
  fun tt => ! exactTreeMCSPThresholdDecision n threshold tt

/-- Specification lemma for the hard-table thresholded tree-MCSP predicate. -/
theorem exactTreeMCSPThresholdHardDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    exactTreeMCSPThresholdHardDecision n threshold tt = true ↔
      ¬ treeMCSPPredicate n threshold tt := by
  classical
  simp [exactTreeMCSPThresholdHardDecision, exactTreeMCSPThresholdDecision]

/--
Boolean indicator for the proof-level tree-MCSP predicate.  This gives
probability statements a name that refers to the predicate mass rather than to
the exact MCSP decision wrapper.
-/
noncomputable def treeMCSPPredicateDecision
    (n threshold : Nat) : TruthTable n → Bool := by
  classical
  intro tt
  exact decide (treeMCSPPredicate n threshold tt)

/-- Specification lemma for `treeMCSPPredicateDecision`. -/
theorem treeMCSPPredicateDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    treeMCSPPredicateDecision n threshold tt = true ↔
      treeMCSPPredicate n threshold tt := by
  classical
  simp [treeMCSPPredicateDecision]

/-- Boolean complement of the proof-level tree-MCSP predicate decision. -/
noncomputable def notTreeMCSPPredicateDecision
    (n threshold : Nat) : TruthTable n → Bool :=
  fun tt => ! treeMCSPPredicateDecision n threshold tt

/-- Specification lemma for `notTreeMCSPPredicateDecision`. -/
theorem notTreeMCSPPredicateDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    notTreeMCSPPredicateDecision n threshold tt = true ↔
      ¬ treeMCSPPredicate n threshold tt := by
  classical
  simp [notTreeMCSPPredicateDecision, treeMCSPPredicateDecision]

/--
The exact hard-table decision agrees extensionally with the complement of the
proof-level predicate decision.
-/
theorem exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision
    (n threshold : Nat) :
    exactTreeMCSPThresholdHardDecision n threshold =
      notTreeMCSPPredicateDecision n threshold := by
  funext tt
  simp [exactTreeMCSPThresholdHardDecision, exactTreeMCSPThresholdDecision,
    notTreeMCSPPredicateDecision, treeMCSPPredicateDecision]

/-- `treeMCSPPredicateDecision` packaged as a correct threshold oracle. -/
noncomputable def treeMCSPPredicateOracle
    (n threshold : Nat) : MCSPThresholdOracle n where
  threshold := threshold
  decide := treeMCSPPredicateDecision n threshold
  correct := treeMCSPPredicateDecision_spec

/--
Uniform Shannon-counting upper bound for the mass of low-complexity truth
tables.
-/
theorem uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    (n threshold : Nat) :
    uniformTruthTableAcceptanceProbability (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) := by
  simpa [treeMCSPPredicateOracle] using
    uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle
      (treeMCSPPredicateOracle n threshold)

/--
Fair product-distribution upper bound for the mass of low-complexity truth
tables.
-/
theorem fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    (n threshold : Nat) :
    acceptanceProbability ((1 : Rat) / 2) (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) := by
  rw [acceptanceProbability_fair_eq_bitVecAcceptanceProbability]
  exact
    uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
      n threshold

/--
Fair product-distribution lower bound for the hard-table predicate, obtained by
complementing the Shannon-counting upper bound for low-complexity tables.
-/
theorem one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
    (n threshold : Nat) :
    1 -
        (Pnp3.Models.circuitCountBound n threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) ≤
      acceptanceProbability ((1 : Rat) / 2)
        (notTreeMCSPPredicateDecision n threshold) := by
  have hLowMass :
      acceptanceProbability ((1 : Rat) / 2)
          (treeMCSPPredicateDecision n threshold) ≤
        (Pnp3.Models.circuitCountBound n threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
    fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio n threshold
  simpa [notTreeMCSPPredicateDecision] using
    one_sub_upper_le_acceptanceProbability_fair_not hLowMass

/-- The exact thresholded tree-MCSP decision accepts low-complexity tables. -/
theorem exactTreeMCSPThresholdDecision_accepts_of_treeMCSPPredicate
    {n threshold : Nat}
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdDecision n threshold tt = true :=
  (exactTreeMCSPThresholdDecision_spec tt).2 hEasy

/-- The exact thresholded tree-MCSP decision rejects tables above the threshold. -/
theorem exactTreeMCSPThresholdDecision_rejects_of_not_treeMCSPPredicate
    {n threshold : Nat}
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdDecision n threshold tt = false := by
  by_cases hTrue : exactTreeMCSPThresholdDecision n threshold tt = true
  · exact (hHard ((exactTreeMCSPThresholdDecision_spec tt).1 hTrue)).elim
  · cases hDecision : exactTreeMCSPThresholdDecision n threshold tt
    · rfl
    · exact (hTrue hDecision).elim

/-- The hard-table decision accepts tables above the threshold. -/
theorem exactTreeMCSPThresholdHardDecision_accepts_of_not_treeMCSPPredicate
    {n threshold : Nat}
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdHardDecision n threshold tt = true :=
  (exactTreeMCSPThresholdHardDecision_spec tt).2 hHard

/-- The hard-table decision rejects low-complexity tables. -/
theorem exactTreeMCSPThresholdHardDecision_rejects_of_treeMCSPPredicate
    {n threshold : Nat}
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdHardDecision n threshold tt = false := by
  by_cases hTrue : exactTreeMCSPThresholdHardDecision n threshold tt = true
  · exact ((exactTreeMCSPThresholdHardDecision_spec tt).1 hTrue hEasy).elim
  · cases hDecision : exactTreeMCSPThresholdHardDecision n threshold tt
    · rfl
    · exact (hTrue hDecision).elim

/--
Upper probability lift: acceptance by the exact threshold decision is bounded
by the probability mass of the proof-level tree-MCSP predicate.
-/
theorem acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
    {n threshold : Nat}
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1) :
    acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) ≤
      acceptanceProbability bias (treeMCSPPredicateDecision n threshold) := by
  exact acceptanceProbability_mono hBias_nonneg hBias_le_one (fun tt hAccept =>
    (treeMCSPPredicateDecision_spec tt).2
      ((exactTreeMCSPThresholdDecision_spec tt).1 hAccept))

/--
Lower probability lift: the proof-level tree-MCSP predicate mass is bounded by
acceptance of the exact threshold decision.
-/
theorem treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
    {n threshold : Nat}
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1) :
    acceptanceProbability bias (treeMCSPPredicateDecision n threshold) ≤
      acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) := by
  exact acceptanceProbability_mono hBias_nonneg hBias_le_one (fun tt hAccept =>
    (exactTreeMCSPThresholdDecision_spec tt).2
      ((treeMCSPPredicateDecision_spec tt).1 hAccept))

/--
One-sided upper-bound form for consuming externally supplied mass bounds on
low-complexity truth tables.
-/
theorem acceptanceProbability_exactTreeMCSPThresholdDecision_le_of_treeMCSPPredicateDecision_bound
    {n threshold : Nat}
    {bias q : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (hMass :
      acceptanceProbability bias (treeMCSPPredicateDecision n threshold) ≤ q) :
    acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) ≤ q :=
  le_trans
    (acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
      (n := n) (threshold := threshold)
      hBias_nonneg hBias_le_one)
    hMass

/--
One-sided lower-bound form for consuming externally supplied mass lower bounds
on low-complexity truth tables.
-/
theorem treeMCSPPredicateDecision_bound_le_acceptanceProbability_exactTreeMCSPThresholdDecision
    {n threshold : Nat}
    {bias q : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (hMass :
      q ≤ acceptanceProbability bias (treeMCSPPredicateDecision n threshold)) :
    q ≤ acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) :=
  le_trans hMass
    (treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
      (n := n) (threshold := threshold)
      hBias_nonneg hBias_le_one)

/--
Boolean single-slice MCSP language: at input length `2^n`, return the exact
thresholded tree-MCSP predicate for `threshold`; off that slice, return `false`.
-/
noncomputable def exactTreeMCSPThresholdLanguage
    (n threshold : Nat) : BitVecLanguage := by
  classical
  intro m x
  exact if hm : m = Pnp3.Models.Partial.tableLen n then
      exactTreeMCSPThresholdDecision n threshold
        (cast (by simpa [TruthTable] using congrArg BitVec hm) x)
    else
      false

/--
Pointwise lower-bound schedule for the exact thresholded tree-MCSP slice:
enforce the bound `maxSize + 1` only on the truth-table length `2^n`.
-/
def exactTreeMCSPThresholdLowerBound
    (n maxSize : Nat) : Nat → Nat :=
  fun m => if m = Pnp3.Models.Partial.tableLen n then maxSize + 1 else 0

/--
Package one exact circuit for the thresholded tree-MCSP language as an
`ImplementedThresholdOracle`.
-/
noncomputable def implementedThresholdOracleOfCircuit
    {C : CircuitFamilyClass}
    {n threshold : Nat}
    (c : C.Family (Pnp3.Models.Partial.tableLen n))
    (hComputes :
      ∀ tt : TruthTable n,
        C.eval c tt = exactTreeMCSPThresholdDecision n threshold tt) :
    ImplementedThresholdOracle C n where
  threshold := threshold
  decide := fun tt => C.eval c tt
  correct := by
    intro tt
    rw [hComputes tt]
    exact exactTreeMCSPThresholdDecision_spec tt
  circuit := c
  circuit_correct := by
    intro tt
    rfl

/--
Lower-transfer theorem for the local-PRG route: if a small circuit class
implements a thresholded MCSP oracle whose threshold accepts the whole PRG
image, and the PRG one-sided fools that class, then the oracle must accept a
large fraction of uniform truth tables.
-/
theorem uniformTruthTableAcceptanceProbability_ge_one_sub_epsilon_of_localPRG
    {C : CircuitFamilyClass}
    {n maxSize : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (impl : ImplementedThresholdOracle C n)
    (hSize : C.size impl.circuit ≤ maxSize)
    (hThreshold : prg.imageSizeBound ≤ impl.threshold)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon) :
    1 - epsilon ≤ uniformTruthTableAcceptanceProbability impl.decide := by
  have hAcceptSeeds :
      ∀ seed : BitVec prg.seedBits, impl.decide (prg.gen seed) = true :=
    prg.oracle_accepts_all_outputs impl.toMCSPThresholdOracle hThreshold
  have hSeedOne : seedAcceptanceProbability prg impl.decide = 1 :=
    seedAcceptanceProbability_eq_one_of_forall_accept prg hAcceptSeeds
  have hFoolImpl :
      seedAcceptanceProbability prg (fun tt => C.eval impl.circuit tt) ≤
        uniformTruthTableAcceptanceProbability (fun tt => C.eval impl.circuit tt) + epsilon :=
    hFool impl.circuit hSize
  have hSeedCongr :
      seedAcceptanceProbability prg (fun tt => C.eval impl.circuit tt) =
        seedAcceptanceProbability prg impl.decide := by
    exact seedAcceptanceProbability_congr prg
      (funext fun tt => impl.circuit_correct tt)
  have hUniformCongr :
      uniformTruthTableAcceptanceProbability (fun tt => C.eval impl.circuit tt) =
        uniformTruthTableAcceptanceProbability impl.decide := by
    exact uniformTruthTableAcceptanceProbability_congr
      (funext fun tt => impl.circuit_correct tt)
  have hCompare : 1 ≤ uniformTruthTableAcceptanceProbability impl.decide + epsilon := by
    calc
      1 = seedAcceptanceProbability prg impl.decide := by symm; exact hSeedOne
      _ = seedAcceptanceProbability prg (fun tt => C.eval impl.circuit tt) := by
            symm
            exact hSeedCongr
      _ ≤ uniformTruthTableAcceptanceProbability (fun tt => C.eval impl.circuit tt) + epsilon :=
            hFoolImpl
      _ = uniformTruthTableAcceptanceProbability impl.decide + epsilon := by
            rw [hUniformCongr]
  linarith

/--
Explicit contradiction form of the local-PRG transfer route, closed using the
proved Shannon-counting upper bound for tree-MCSP threshold oracles.
-/
theorem smallImplementedThresholdOracle_contradiction_of_localPRGTransfer
    {C : CircuitFamilyClass}
    {n maxSize : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (impl : ImplementedThresholdOracle C n)
    (hSize : C.size impl.circuit ≤ maxSize)
    (hThreshold : prg.imageSizeBound ≤ impl.threshold)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon)
    (hEpsSmall :
      epsilon <
        1 - ((Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
              (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat))) :
    False := by
  have hLower :
      1 - epsilon ≤ uniformTruthTableAcceptanceProbability impl.decide :=
    uniformTruthTableAcceptanceProbability_ge_one_sub_epsilon_of_localPRG
      prg impl hSize hThreshold hFool
  have hCountUpper :
      uniformTruthTableAcceptanceProbability impl.decide ≤
        (Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
    uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle
      impl.toMCSPThresholdOracle
  have hUpper :
      uniformTruthTableAcceptanceProbability impl.decide < 1 - epsilon := by
    have hRatioLt :
        ((Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) < 1 - epsilon := by
      linarith
    exact lt_of_le_of_lt hCountUpper hRatioLt
  exact (not_lt_of_ge hLower) hUpper

/--
Existential wrapper for the same transfer contradiction.
-/
theorem noSmallImplementedThresholdOracle_of_localPRGTransfer
    {C : CircuitFamilyClass}
    {n maxSize : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon) :
    ¬ ∃ impl : ImplementedThresholdOracle C n,
        C.size impl.circuit ≤ maxSize ∧
        prg.imageSizeBound ≤ impl.threshold ∧
        epsilon <
          1 - ((Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
                (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) := by
  intro hImpl
  rcases hImpl with ⟨impl, hSize, hThreshold, hEpsSmall⟩
  exact smallImplementedThresholdOracle_contradiction_of_localPRGTransfer
    prg impl hSize hThreshold hFool hEpsSmall

/--
Variant that accepts the stronger two-sided pseudorandomness contract directly.
-/
theorem noSmallImplementedThresholdOracle_of_foolsLocalPRGTransfer
    {C : CircuitFamilyClass}
    {n maxSize : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hFool :
      FoolsBoundedTruthTableClass prg C maxSize epsilon) :
    ¬ ∃ impl : ImplementedThresholdOracle C n,
        C.size impl.circuit ≤ maxSize ∧
        prg.imageSizeBound ≤ impl.threshold ∧
        epsilon <
          1 - ((Pnp3.Models.circuitCountBound n impl.threshold : Rat) /
                (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) := by
  exact noSmallImplementedThresholdOracle_of_localPRGTransfer
    prg
    (oneSidedFoolsBoundedTruthTableClass_of_foolsBounded hFool)

/--
Contradiction form of the local-PRG transfer theorem for one exact small
`C`-circuit computing the thresholded tree-MCSP language.
-/
theorem smallCircuit_contradiction_of_localPRGTransfer
    {C : CircuitFamilyClass}
    {n maxSize threshold : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hThreshold : prg.imageSizeBound ≤ threshold)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon)
    (hEpsSmall :
      epsilon <
        1 - ((Pnp3.Models.circuitCountBound n threshold : Rat) /
              (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)))
    (c : C.Family (Pnp3.Models.Partial.tableLen n))
    (hSize : C.size c ≤ maxSize)
    (hComputes :
      ∀ tt : TruthTable n,
        C.eval c tt = exactTreeMCSPThresholdDecision n threshold tt) :
    False := by
  let impl := implementedThresholdOracleOfCircuit
    (C := C) (n := n) (threshold := threshold) c hComputes
  exact smallImplementedThresholdOracle_contradiction_of_localPRGTransfer
    prg impl hSize hThreshold hFool hEpsSmall

/--
Size-lower-bound form of the local-PRG transfer theorem for the exact
thresholded tree-MCSP language on the truth-table slice `2^n`.
-/
theorem sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer
    {C : CircuitFamilyClass}
    {n maxSize threshold : Nat}
    {epsilon : Rat}
    (prg : TruthTableLocalPRG n)
    (hThreshold : prg.imageSizeBound ≤ threshold)
    (hFool :
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon)
    (hEpsSmall :
      epsilon <
        1 - ((Pnp3.Models.circuitCountBound n threshold : Rat) /
              (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat))) :
    SizeLowerBound
      C
      (exactTreeMCSPThresholdLanguage n threshold)
      (exactTreeMCSPThresholdLowerBound n maxSize) := by
  intro m c hComp
  by_cases hm : m = Pnp3.Models.Partial.tableLen n
  · subst hm
    have hExact :
        ∀ tt : TruthTable n,
          C.eval c tt = exactTreeMCSPThresholdDecision n threshold tt := by
      intro tt
      simpa [exactTreeMCSPThresholdLanguage] using hComp tt
    by_contra hLower
    have hLower' : ¬ maxSize + 1 ≤ C.size c := by
      simpa [exactTreeMCSPThresholdLowerBound] using hLower
    have hSizeLt : C.size c < maxSize + 1 := Nat.not_le.mp hLower'
    have hSize : C.size c ≤ maxSize := Nat.lt_succ_iff.mp hSizeLt
    exact smallCircuit_contradiction_of_localPRGTransfer
      (prg := prg)
      (hThreshold := hThreshold)
      (hFool := hFool)
      (hEpsSmall := hEpsSmall)
      c hSize hExact
  · simp [exactTreeMCSPThresholdLowerBound, hm]

end AlgorithmsToLowerBounds
end Pnp4
