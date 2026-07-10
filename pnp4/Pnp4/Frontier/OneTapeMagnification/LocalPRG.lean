import Pnp4.Frontier.OneTapeMagnification.RandomizedSemantics
import Pnp4.Frontier.StreamingMagnification.TotalSearch
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Exact finite local-generator probabilities

This module isolates the probability step used by CHMY Lemma 15.  Both
experiments use a fresh, independent uniform finite random tape for the
randomized one-tape machine:

* the uniform experiment averages over all `2^(2^n)` truth tables and all
  `2^randomBits` random tapes;
* the generator experiment averages over all seeds and, independently, all
  random tapes.

"Local" has the circuit-complexity meaning used by CHMY: every fixed-seed
output truth table has a standard DAG of at most `threshold` internal gates.
It does not say that each output coordinate depends on few seed coordinates.

The theorem proved here is conditional on an explicit generator and an
explicit pointwise MCSP completeness statement.  It neither postulates nor
packages existence of the small-seed generator that remains open.
-/

open scoped BigOperators

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open StreamingMagnification
open StreamingMagnification.TotalSearch

/-- A local generator whose fixed-seed outputs have small standard DAGs. -/
structure DAGLocalGenerator (n threshold : Nat) where
  seedBits : Nat
  generate : FiniteBitTape seedBits -> TruthTable n
  image_easy : forall seed, HasCircuit n threshold (generate seed)

/-- Exact machine acceptance on one truth table and a fresh finite random tape. -/
def machineAcceptance
    (machine : RandomizedMachine) {n : Nat} (table : TruthTable n)
    (randomBits steps : Nat) : Rat :=
  acceptanceProbability machine (tableBits table) randomBits steps

/--
Joint uniform average over generator seeds and an independent machine random
tape.  The inner `machineAcceptance` is itself the exact uniform random-tape
average, so this quotient is exactly the finite product experiment.
-/
def generatedMachineAcceptance
    (machine : RandomizedMachine) {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat) : Rat :=
  (∑ seed : FiniteBitTape generator.seedBits,
      machineAcceptance machine (generator.generate seed) randomBits steps) /
    (2 ^ generator.seedBits : Rat)

/--
Joint uniform average over all truth tables and an independent machine random
tape.  There are exactly `2^(2^n)` tables of length `2^n`.
-/
def uniformMachineAcceptance
    (machine : RandomizedMachine) (n randomBits steps : Nat) : Rat :=
  (∑ table : TruthTable n,
      machineAcceptance machine table randomBits steps) /
    (2 ^ (2 ^ n) : Rat)

/-- Exact two-sided fooling statement for the two finite product experiments. -/
def FoolsOneTapeMachineWithin
    (machine : RandomizedMachine) {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat) (epsilon : Rat) : Prop :=
  |uniformMachineAcceptance machine n randomBits steps -
      generatedMachineAcceptance machine generator randomBits steps| <= epsilon

/-- The finite seed space has exactly `2^seedBits` elements. -/
theorem finiteSeedSpace_card (seedBits : Nat) :
    Fintype.card (FiniteBitTape seedBits) = 2 ^ seedBits :=
  finiteBitTape_card seedBits

/-- The finite truth-table cube has exactly `2^(2^n)` elements. -/
theorem truthTableSpace_card (n : Nat) :
    Fintype.card (TruthTable n) = 2 ^ (2 ^ n) := by
  simp [TruthTable]

/-- A pointwise lower bound survives the exact uniform seed average. -/
theorem le_generatedMachineAcceptance_of_forall
    (machine : RandomizedMachine) {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat) (lower : Rat)
    (hLower : forall seed : FiniteBitTape generator.seedBits,
      lower <= machineAcceptance machine (generator.generate seed)
        randomBits steps) :
    lower <= generatedMachineAcceptance machine generator randomBits steps := by
  have hDenPos : (0 : Rat) < (2 ^ generator.seedBits : Rat) := by positivity
  apply (le_div_iff₀ hDenPos).2
  have hSum :
      ∑ seed : FiniteBitTape generator.seedBits, lower <=
        ∑ seed : FiniteBitTape generator.seedBits,
          machineAcceptance machine (generator.generate seed)
            randomBits steps := by
    exact Finset.sum_le_sum fun seed _ => hLower seed
  calc
    lower * (2 ^ generator.seedBits : Rat) =
        ∑ _seed : FiniteBitTape generator.seedBits, lower := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [mul_comm]
    _ <= ∑ seed : FiniteBitTape generator.seedBits,
          machineAcceptance machine (generator.generate seed)
            randomBits steps := hSum

/--
If the machine accepts every easy table with probability at least `2/3`, then
it accepts every local-generator output, and hence the whole generator
experiment, with probability at least `2/3`.
-/
theorem generatedMachineAcceptance_ge_two_thirds
    (machine : RandomizedMachine) {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat)
    (hCompleteness : forall table : TruthTable n,
      HasCircuit n threshold table ->
        (2 : Rat) / 3 <= machineAcceptance machine table randomBits steps) :
    (2 : Rat) / 3 <=
      generatedMachineAcceptance machine generator randomBits steps := by
  apply le_generatedMachineAcceptance_of_forall
  intro seed
  exact hCompleteness (generator.generate seed) (generator.image_easy seed)

/--
Finite counting/soundness step.  Let `easy` be any explicitly enumerated set
of low-complexity tables.  If fewer than one quarter of all tables are easy
and every table outside that set is accepted with probability at most `1/3`,
then uniform acceptance is strictly below `1/2`.

The later DAG-counting layer supplies the concrete `easy` set; this lemma
contains the exact finite arithmetic and uses no asymptotic probability.
-/
theorem uniformMachineAcceptance_lt_half_of_easy_set_small
    (machine : RandomizedMachine) (n randomBits steps : Nat)
    (easy : Finset (TruthTable n))
    (hEasySmall : easy.card * 4 < 2 ^ (2 ^ n))
    (hSoundness : forall table : TruthTable n,
      table ∉ easy ->
        machineAcceptance machine table randomBits steps <= (1 : Rat) / 3) :
    uniformMachineAcceptance machine n randomBits steps < (1 : Rat) / 2 := by
  classical
  let total : Rat := (2 ^ (2 ^ n) : Rat)
  have hTotalPos : 0 < total := by
    dsimp [total]
    positivity
  have hPointwise : forall table : TruthTable n,
      machineAcceptance machine table randomBits steps <=
        (1 : Rat) / 3 + if table ∈ easy then (2 : Rat) / 3 else 0 := by
    intro table
    by_cases hEasy : table ∈ easy
    · have hAtMostOne :
          machineAcceptance machine table randomBits steps <= 1 :=
        acceptanceProbability_le_one machine (tableBits table) randomBits steps
      convert hAtMostOne using 1
      all_goals norm_num [hEasy]
    · simpa [hEasy] using hSoundness table hEasy
  have hSum :
      (∑ table : TruthTable n,
          machineAcceptance machine table randomBits steps) <=
        ∑ table : TruthTable n,
          ((1 : Rat) / 3 +
            if table ∈ easy then (2 : Rat) / 3 else 0) := by
    exact Finset.sum_le_sum fun table _ => hPointwise table
  have hRightSum :
      (∑ table : TruthTable n,
          ((1 : Rat) / 3 +
            if table ∈ easy then (2 : Rat) / 3 else 0)) =
        total / 3 + (easy.card : Rat) * 2 / 3 := by
    simp [total, Finset.sum_add_distrib]
    ring
  have hCountRat : (easy.card : Rat) * 4 < total := by
    dsimp [total]
    exact_mod_cast hEasySmall
  unfold uniformMachineAcceptance
  apply (div_lt_iff₀ hTotalPos).2
  calc
    (∑ table : TruthTable n,
        machineAcceptance machine table randomBits steps)
        <= total / 3 + (easy.card : Rat) * 2 / 3 := by
          rw [← hRightSum]
          exact hSum
    _ < ((1 : Rat) / 2) * total := by
      linarith

/--
Exact CHMY `1/6` gap.  The strict uniform bound `< 1/2` is the output of the
separate counting/soundness step; locality and completeness give the
generator-side bound `>= 2/3` here.
-/
theorem localGenerator_acceptance_gap_gt_one_sixth
    (machine : RandomizedMachine) {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat)
    (hCompleteness : forall table : TruthTable n,
      HasCircuit n threshold table ->
        (2 : Rat) / 3 <= machineAcceptance machine table randomBits steps)
    (hUniform :
      uniformMachineAcceptance machine n randomBits steps < (1 : Rat) / 2) :
    (1 : Rat) / 6 <
      |uniformMachineAcceptance machine n randomBits steps -
        generatedMachineAcceptance machine generator randomBits steps| := by
  have hGenerated :
      (2 : Rat) / 3 <=
        generatedMachineAcceptance machine generator randomBits steps :=
    generatedMachineAcceptance_ge_two_thirds
      machine generator randomBits steps hCompleteness
  have hDifference :
      (1 : Rat) / 6 <
        generatedMachineAcceptance machine generator randomBits steps -
          uniformMachineAcceptance machine n randomBits steps := by
    linarith
  have hPositive :
      0 < generatedMachineAcceptance machine generator randomBits steps -
        uniformMachineAcceptance machine n randomBits steps := by
    linarith
  rw [abs_sub_comm, abs_of_pos hPositive]
  exact hDifference

/--
Consequently no generator satisfying the preceding hypotheses can fool the
machine to error at most `1/6`.  This is a finite contradiction, not an
informal asymptotic probability claim.
-/
theorem not_foolsWithin_one_sixth_of_localGenerator_gap
    (machine : RandomizedMachine) {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (randomBits steps : Nat)
    (hCompleteness : forall table : TruthTable n,
      HasCircuit n threshold table ->
        (2 : Rat) / 3 <= machineAcceptance machine table randomBits steps)
    (hUniform :
      uniformMachineAcceptance machine n randomBits steps < (1 : Rat) / 2) :
    Not (FoolsOneTapeMachineWithin machine generator randomBits steps
      ((1 : Rat) / 6)) := by
  intro hFools
  have hGap := localGenerator_acceptance_gap_gt_one_sixth
    machine generator randomBits steps hCompleteness hUniform
  exact (not_lt_of_ge hFools) hGap

end OneTapeMagnification
end Frontier
end Pnp4
