import Pnp4.AlgorithmsToLowerBounds.CoinProblem
import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Coin-problem instance induced by sampling truth tables of `n`-bit Boolean
functions from a product distribution on their `2^n` entries.
-/
def truthTableCoinInstance
    (n : Nat)
    (lowBias highBias : Rat)
    (hlow_nonneg : 0 ≤ lowBias)
    (hhigh_le_one : highBias ≤ 1)
    (hbias_gap : lowBias < highBias) :
    CoinProblemInstance where
  sampleBits := Pnp3.Models.Partial.tableLen n
  lowBias := lowBias
  highBias := highBias
  low_nonneg := hlow_nonneg
  high_le_one := hhigh_le_one
  bias_gap := hbias_gap

/--
Boolean oracle for thresholded truth-table MCSP.

The field `correct` intentionally states exact agreement with the proof-level
predicate `treeMCSPPredicate`; this keeps the interface honest while remaining
agnostic about how the oracle is implemented.
-/
structure MCSPThresholdOracle (n : Nat) where
  threshold : Nat
  decide : TruthTable n → Bool
  correct : ∀ tt : TruthTable n,
    decide tt = true ↔ treeMCSPPredicate n threshold tt

/--
An `MCSPThresholdOracle` implemented by a circuit from a chosen non-uniform
class over truth-table inputs.
-/
structure ImplementedThresholdOracle
    (C : CircuitFamilyClass) (n : Nat) extends MCSPThresholdOracle n where
  circuit : C.Family (Pnp3.Models.Partial.tableLen n)
  circuit_correct : ∀ tt : TruthTable n, C.eval circuit tt = decide tt

/--
Abstract reduction witness for the paper's statistical middle layer:
some thresholded MCSP oracle distinguishes two truth-table product
distributions with advantage at least `adv`.
-/
structure MCSPCoinReductionWitness
    (n : Nat)
    (lowBias highBias : Rat)
    (hlow_nonneg : 0 ≤ lowBias)
    (hhigh_le_one : highBias ≤ 1)
    (hbias_gap : lowBias < highBias)
    (adv : Rat) where
  oracle : MCSPThresholdOracle n
  solvesCoin :
    SolvesCoinProblem
      (truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
      oracle.decide
      adv

/--
If a class `C` implements a thresholded MCSP oracle whose decision function
already has the desired distinguishing advantage, then `C` solves the same coin
problem on truth-table inputs.
-/
theorem ImplementedThresholdOracle.classSolvesCoinProblem_of_advantage
    {C : CircuitFamilyClass}
    {n : Nat}
    {lowBias highBias : Rat}
    {hlow_nonneg : 0 ≤ lowBias}
    {hhigh_le_one : highBias ≤ 1}
    {hbias_gap : lowBias < highBias}
    {adv : Rat}
    (impl : ImplementedThresholdOracle C n)
    (hSolve :
      SolvesCoinProblem
        (truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
        impl.decide
        adv) :
    ClassSolvesCoinProblem
      C
      (truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
      adv := by
  refine ⟨impl.circuit, ?_⟩
  exact solvesCoinProblem_congr
    (inst :=
      truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
    (A := impl.decide)
    (B := fun x => C.eval impl.circuit x)
    (adv := adv)
    (funext fun tt => (impl.circuit_correct tt).symm)
    hSolve

/--
Bundled version of the previous theorem: any implemented oracle realizing a
coin-reduction witness yields a class-level solver for that coin problem.
-/
theorem MCSPCoinReductionWitness.realizedByClass
    {C : CircuitFamilyClass}
    {n : Nat}
    {lowBias highBias : Rat}
    {hlow_nonneg : 0 ≤ lowBias}
    {hhigh_le_one : highBias ≤ 1}
    {hbias_gap : lowBias < highBias}
    {adv : Rat}
    (w :
      MCSPCoinReductionWitness
        n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap adv)
    (impl : ImplementedThresholdOracle C n)
    (_hThreshold : impl.threshold = w.oracle.threshold)
    (hDecide :
      ∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :
    ClassSolvesCoinProblem
      C
      (truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
      adv := by
  have hSolveImpl :
      SolvesCoinProblem
        (truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
        impl.decide
        adv := by
    exact solvesCoinProblem_congr
      (inst :=
        truthTableCoinInstance n lowBias highBias hlow_nonneg hhigh_le_one hbias_gap)
      (A := w.oracle.decide)
      (B := impl.decide)
      (adv := adv)
      (funext fun tt => (hDecide tt).symm)
      w.solvesCoin
  exact impl.classSolvesCoinProblem_of_advantage hSolveImpl

end AlgorithmsToLowerBounds
end Pnp4
