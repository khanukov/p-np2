import Pnp4.AlgorithmsToLowerBounds.LocalPRG
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction
import Counting.ShannonCounting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Pnp4
namespace AlgorithmsToLowerBounds

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

end AlgorithmsToLowerBounds
end Pnp4
