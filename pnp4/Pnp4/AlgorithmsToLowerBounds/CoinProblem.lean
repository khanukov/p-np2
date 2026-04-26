import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

open scoped BigOperators

namespace Pnp4
namespace AlgorithmsToLowerBounds

/-- Weight contributed by a single Bernoulli sample with success bias `bias`. -/
def bernoulliBitWeight (bias : Rat) (b : Bool) : Rat :=
  if b then bias else 1 - bias

/--
Weight of a full bit-vector under the product distribution where each bit is 1
independently with probability `bias`.
-/
noncomputable def productBiasWeight
    (bias : Rat) {n : Nat} (x : BitVec n) : Rat :=
  ∏ i : Fin n, bernoulliBitWeight bias (x i)

/--
Acceptance probability of a Boolean algorithm under the product distribution of
 bias `bias`.
-/
noncomputable def acceptanceProbability
    (bias : Rat) {n : Nat} (A : BitVec n → Bool) : Rat :=
  ∑ x : BitVec n, if A x then productBiasWeight bias x else 0

/-- A Bernoulli bit weight is nonnegative when the bias is a probability. -/
theorem bernoulliBitWeight_nonneg
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (b : Bool) :
    0 ≤ bernoulliBitWeight bias b := by
  cases b <;> simp [bernoulliBitWeight] <;> linarith

/-- Product-distribution weights are nonnegative for valid Bernoulli biases. -/
theorem productBiasWeight_nonneg
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    {n : Nat}
    (x : BitVec n) :
    0 ≤ productBiasWeight bias x := by
  classical
  unfold productBiasWeight
  exact Finset.prod_nonneg fun i _ =>
    bernoulliBitWeight_nonneg hBias_nonneg hBias_le_one (x i)

/-- Split an `(n+1)`-bit vector into its head bit and remaining tail. -/
private def bitVecSuccEquiv (n : Nat) :
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

/-- The total mass of the Bernoulli product distribution is one. -/
theorem productBiasWeight_total
    (bias : Rat)
    (n : Nat) :
    (∑ x : BitVec n, productBiasWeight bias x) = 1 := by
  induction n with
  | zero =>
      simp [productBiasWeight]
  | succ n ih =>
      have hSplit :
          (∑ x : BitVec (n + 1), productBiasWeight bias x) =
            ∑ y : Bool × BitVec n,
              productBiasWeight bias ((bitVecSuccEquiv n).symm y) := by
        exact Fintype.sum_equiv (bitVecSuccEquiv n)
          (fun x : BitVec (n + 1) => productBiasWeight bias x)
          (fun y : Bool × BitVec n =>
            productBiasWeight bias ((bitVecSuccEquiv n).symm y))
          (fun _ => by simp)
      have hWeight :
          ∀ b : Bool, ∀ x : BitVec n,
            productBiasWeight bias ((bitVecSuccEquiv n).symm (b, x)) =
              bernoulliBitWeight bias b * productBiasWeight bias x := by
        intro b x
        unfold productBiasWeight
        rw [Fin.prod_univ_succ]
        simp [bitVecSuccEquiv]
      calc
        (∑ x : BitVec (n + 1), productBiasWeight bias x)
            = ∑ y : Bool × BitVec n,
                productBiasWeight bias ((bitVecSuccEquiv n).symm y) := hSplit
        _ = ∑ b : Bool, ∑ x : BitVec n,
              bernoulliBitWeight bias b * productBiasWeight bias x := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro b _hb
              apply Finset.sum_congr rfl
              intro x _hx
              exact hWeight b x
        _ = ∑ b : Bool, bernoulliBitWeight bias b *
              (∑ x : BitVec n, productBiasWeight bias x) := by
              apply Finset.sum_congr rfl
              intro b _hb
              rw [Finset.mul_sum]
        _ = ∑ b : Bool, bernoulliBitWeight bias b := by
              rw [ih]
              simp
        _ = 1 := by
              simp [bernoulliBitWeight]

/-- The always-accept algorithm has probability one under any Bernoulli bias. -/
theorem acceptanceProbability_true
    {n : Nat}
    (bias : Rat) :
    acceptanceProbability bias (fun _ : BitVec n => true) = 1 := by
  simp [acceptanceProbability, productBiasWeight_total]

/-- Acceptance probability of a Boolean complement under a product distribution. -/
theorem acceptanceProbability_not
    {n : Nat}
    (bias : Rat)
    (A : BitVec n → Bool) :
    acceptanceProbability bias (fun x => ! A x) =
      1 - acceptanceProbability bias A := by
  classical
  let accepted : Finset (BitVec n) :=
    (Finset.univ : Finset (BitVec n)).filter (fun x => A x = true)
  let rejected : Finset (BitVec n) :=
    (Finset.univ : Finset (BitVec n)).filter (fun x => (! A x) = true)
  have hDisjoint : Disjoint accepted rejected := by
    rw [Finset.disjoint_left]
    intro x hxAccepted hxRejected
    have hA : A x = true := (Finset.mem_filter.mp hxAccepted).2
    have hNotA : (! A x) = true := (Finset.mem_filter.mp hxRejected).2
    cases hAx : A x <;> simp [hAx] at hA hNotA
  have hUnion :
      accepted ∪ rejected = (Finset.univ : Finset (BitVec n)) := by
    ext x
    by_cases hA : A x = true
    · simp [accepted, rejected, hA]
    · have hFalse : A x = false := by
        cases hAx : A x
        · rfl
        · exact (hA hAx).elim
      simp [accepted, rejected, hFalse]
  have hTotal :
      (∑ x ∈ accepted, productBiasWeight bias x) +
          (∑ x ∈ rejected, productBiasWeight bias x) = 1 := by
    have hUnionSum :
        (∑ x ∈ accepted ∪ rejected, productBiasWeight bias x) =
          (∑ x ∈ accepted, productBiasWeight bias x) +
            (∑ x ∈ rejected, productBiasWeight bias x) := by
      rw [Finset.sum_union hDisjoint]
    have hAll :
        (∑ x ∈ accepted ∪ rejected, productBiasWeight bias x) = 1 := by
      rw [hUnion]
      simpa using productBiasWeight_total bias n
    linarith
  have hAccepted :
      acceptanceProbability bias A =
        ∑ x ∈ accepted, productBiasWeight bias x := by
    unfold acceptanceProbability
    rw [← Finset.sum_filter]
  have hRejected :
      acceptanceProbability bias (fun x => ! A x) =
        ∑ x ∈ rejected, productBiasWeight bias x := by
    unfold acceptanceProbability
    rw [← Finset.sum_filter]
  rw [hAccepted, hRejected]
  linarith

/--
If a predicate has mass at least `1 - q`, its Boolean complement has mass at
most `q`.
-/
theorem acceptanceProbability_not_le_of_one_sub_le
    {n : Nat}
    {bias : Rat}
    {A : BitVec n → Bool}
    {q : Rat}
    (hMass : 1 - q ≤ acceptanceProbability bias A) :
    acceptanceProbability bias (fun x => ! A x) ≤ q := by
  rw [acceptanceProbability_not]
  linarith

/--
One finite coin-problem instance: distinguish `lowBias` from `highBias` on
sample strings of length `sampleBits`.
-/
structure CoinProblemInstance where
  sampleBits : Nat
  lowBias : Rat
  highBias : Rat
  low_nonneg : 0 ≤ lowBias
  high_le_one : highBias ≤ 1
  bias_gap : lowBias < highBias

/-- The low-bias side of a valid coin instance is at most one. -/
theorem CoinProblemInstance.low_le_one
    (inst : CoinProblemInstance) :
    inst.lowBias ≤ 1 :=
  le_trans (le_of_lt inst.bias_gap) inst.high_le_one

/-- The high-bias side of a valid coin instance is nonnegative. -/
theorem CoinProblemInstance.high_nonneg
    (inst : CoinProblemInstance) :
    0 ≤ inst.highBias :=
  le_trans inst.low_nonneg (le_of_lt inst.bias_gap)

/-- Acceptance-gap of an algorithm on a fixed coin-problem instance. -/
noncomputable def acceptanceGap
    (inst : CoinProblemInstance)
    (A : BitVec inst.sampleBits → Bool) : Rat :=
  acceptanceProbability inst.highBias A -
    acceptanceProbability inst.lowBias A

/--
`A` solves the coin problem with advantage at least `adv` if its acceptance
probability under the higher-bias distribution exceeds that under the
lower-bias distribution by at least `adv`.
-/
noncomputable def SolvesCoinProblem
    (inst : CoinProblemInstance)
    (A : BitVec inst.sampleBits → Bool)
    (adv : Rat) : Prop :=
  adv ≤ acceptanceGap inst A

/--
Family of arbitrary Boolean distinguishers for finite coin-problem instances.

This is deliberately not tied to MCSP: translation/rescaling arguments in the
published proof may construct a new distinguisher rather than reusing the same
threshold predicate.
-/
structure CoinDistinguisherFamily where
  sampleBits : Nat → Nat
  lowBias : Nat → Rat
  highBias : Nat → Rat
  low_nonneg : ∀ n : Nat, 0 ≤ lowBias n
  high_le_one : ∀ n : Nat, highBias n ≤ 1
  bias_gap : ∀ n : Nat, lowBias n < highBias n
  advantage : Nat → Rat
  algorithm : ∀ n : Nat, BitVec (sampleBits n) → Bool
  solves :
    ∀ n : Nat,
      SolvesCoinProblem
        {
          sampleBits := sampleBits n
          lowBias := lowBias n
          highBias := highBias n
          low_nonneg := low_nonneg n
          high_le_one := high_le_one n
          bias_gap := bias_gap n
        }
        (algorithm n)
        (advantage n)

/-- The concrete coin instance solved by one slice of a distinguisher family. -/
def CoinDistinguisherFamily.instance
    (family : CoinDistinguisherFamily)
    (n : Nat) :
    CoinProblemInstance where
  sampleBits := family.sampleBits n
  lowBias := family.lowBias n
  highBias := family.highBias n
  low_nonneg := family.low_nonneg n
  high_le_one := family.high_le_one n
  bias_gap := family.bias_gap n

/-- Read back the solved-coin certificate for one slice. -/
theorem CoinDistinguisherFamily.solves_instance
    (family : CoinDistinguisherFamily)
    (n : Nat) :
    SolvesCoinProblem
      (family.instance n)
      (family.algorithm n)
      (family.advantage n) := by
  simpa [CoinDistinguisherFamily.instance] using family.solves n

/--
Non-uniform class version of the same notion: some circuit in the class solves
the coin problem on the given input length.
-/
noncomputable def ClassSolvesCoinProblem
    (C : CircuitFamilyClass)
    (inst : CoinProblemInstance)
    (adv : Rat) : Prop :=
  ∃ c : C.Family inst.sampleBits,
    SolvesCoinProblem inst (fun x => C.eval c x) adv

/--
Size-bounded class version of coin solving: there is a circuit of size at most
`maxSize` with the required distinguishing advantage.
-/
noncomputable def BoundedClassSolvesCoinProblem
    (C : CircuitFamilyClass)
    (inst : CoinProblemInstance)
    (adv : Rat)
    (maxSize : Nat) : Prop :=
  ∃ c : C.Family inst.sampleBits,
    C.size c ≤ maxSize ∧
      SolvesCoinProblem inst (fun x => C.eval c x) adv

/--
Circuit realization of a semantic coin-distinguisher family by one circuit
family class.

The semantic `CoinDistinguisherFamily` records the Boolean algorithms and their
coin-solving facts; this structure records that those algorithms are computed
by circuits in `C`, with an explicit per-slice size schedule.
-/
structure CircuitCoinDistinguisherFamily
    (C : CircuitFamilyClass)
    (family : CoinDistinguisherFamily) where
  circuit : ∀ n : Nat, C.Family (family.sampleBits n)
  computes :
    ∀ n : Nat, ∀ x : BitVec (family.sampleBits n),
      C.eval (circuit n) x = family.algorithm n x
  sizeBound : Nat → Nat
  size_le :
    ∀ n : Nat,
      C.size (circuit n) ≤ sizeBound n

/-- A size-bounded solver is in particular an unbounded class-level solver. -/
theorem classSolvesCoinProblem_of_bounded
    {C : CircuitFamilyClass}
    {inst : CoinProblemInstance}
    {adv : Rat}
    {maxSize : Nat} :
    BoundedClassSolvesCoinProblem C inst adv maxSize →
      ClassSolvesCoinProblem C inst adv := by
  intro h
  rcases h with ⟨c, _hcSize, hSolve⟩
  exact ⟨c, hSolve⟩

/-- Acceptance probability depends only on the extensional Boolean function. -/
theorem acceptanceProbability_congr
    {n : Nat} {bias : Rat}
    {A B : BitVec n → Bool}
    (hAB : A = B) :
    acceptanceProbability bias A = acceptanceProbability bias B := by
  cases hAB
  rfl

/-- Acceptance probability is monotone under pointwise Boolean implication. -/
theorem acceptanceProbability_mono
    {n : Nat}
    {bias : Rat}
    {A B : BitVec n → Bool}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (hAB : ∀ x : BitVec n, A x = true → B x = true) :
    acceptanceProbability bias A ≤ acceptanceProbability bias B := by
  classical
  unfold acceptanceProbability
  refine Finset.sum_le_sum ?_
  intro x _hx
  cases hA : A x
  · cases hB : B x
    · simp
    · simpa using productBiasWeight_nonneg hBias_nonneg hBias_le_one x
  · have hB : B x = true := hAB x hA
    simp [hB]

/-- Low-bias specialization of `acceptanceProbability_mono`. -/
theorem acceptanceProbability_mono_lowBias
    {inst : CoinProblemInstance}
    {A B : BitVec inst.sampleBits → Bool}
    (hAB : ∀ x : BitVec inst.sampleBits, A x = true → B x = true) :
    acceptanceProbability inst.lowBias A ≤
      acceptanceProbability inst.lowBias B :=
  acceptanceProbability_mono inst.low_nonneg inst.low_le_one hAB

/-- High-bias specialization of `acceptanceProbability_mono`. -/
theorem acceptanceProbability_mono_highBias
    {inst : CoinProblemInstance}
    {A B : BitVec inst.sampleBits → Bool}
    (hAB : ∀ x : BitVec inst.sampleBits, A x = true → B x = true) :
    acceptanceProbability inst.highBias A ≤
      acceptanceProbability inst.highBias B :=
  acceptanceProbability_mono inst.high_nonneg inst.high_le_one hAB

/-- Coin-problem solvability is extensional in the underlying Boolean function. -/
theorem solvesCoinProblem_congr
    {inst : CoinProblemInstance}
    {A B : BitVec inst.sampleBits → Bool}
    {adv : Rat}
    (hAB : A = B)
    (hSolve : SolvesCoinProblem inst A adv) :
    SolvesCoinProblem inst B adv := by
  simpa [SolvesCoinProblem, acceptanceGap, hAB] using hSolve

/-- A circuit realization solves each coin instance extensionally. -/
theorem CircuitCoinDistinguisherFamily.solves
    {C : CircuitFamilyClass}
    {family : CoinDistinguisherFamily}
    (realized : CircuitCoinDistinguisherFamily C family)
    (n : Nat) :
    SolvesCoinProblem
      (family.instance n)
      (fun x => C.eval (realized.circuit n) x)
      (family.advantage n) := by
  exact solvesCoinProblem_congr
    (inst := family.instance n)
    (A := family.algorithm n)
    (B := fun x => C.eval (realized.circuit n) x)
    (adv := family.advantage n)
    (funext fun x => (realized.computes n x).symm)
    (family.solves_instance n)

/-- A circuit realization gives a size-bounded class solver for each slice. -/
theorem CircuitCoinDistinguisherFamily.boundedSolves
    {C : CircuitFamilyClass}
    {family : CoinDistinguisherFamily}
    (realized : CircuitCoinDistinguisherFamily C family)
    (n : Nat) :
    BoundedClassSolvesCoinProblem
      C
      (family.instance n)
      (family.advantage n)
      (realized.sizeBound n) := by
  exact ⟨realized.circuit n, realized.size_le n, realized.solves n⟩

/--
A reusable probability-gap criterion for solving one finite coin-problem
instance.

If the algorithm's low-bias acceptance is at most `lowAcceptanceUpper`, its
high-bias acceptance is at least `highAcceptanceLower`, and those bounds leave
the requested advantage gap, then the algorithm solves the coin problem.
-/
theorem solvesCoinProblem_of_acceptanceProbability_bounds
    {inst : CoinProblemInstance}
    {A : BitVec inst.sampleBits → Bool}
    {adv lowAcceptanceUpper highAcceptanceLower : Rat}
    (hLow :
      acceptanceProbability inst.lowBias A ≤ lowAcceptanceUpper)
    (hHigh :
      highAcceptanceLower ≤ acceptanceProbability inst.highBias A)
    (hGap :
      adv + lowAcceptanceUpper ≤ highAcceptanceLower) :
    SolvesCoinProblem inst A adv := by
  unfold SolvesCoinProblem acceptanceGap
  linarith

/--
Standard uniform-vs-biased instance:
distinguish `1/2 - ε` from `1/2` on strings of length `sampleBits`.
-/
def uniformVsBiasedCoinInstance
    (sampleBits : Nat)
    (ε : Rat)
    (hε_pos : 0 < ε)
    (hε_le_half : ε ≤ (1 : Rat) / 2) :
    CoinProblemInstance where
  sampleBits := sampleBits
  lowBias := (1 : Rat) / 2 - ε
  highBias := (1 : Rat) / 2
  low_nonneg := by
    linarith
  high_le_one := by
    norm_num
  bias_gap := by
    linarith

/--
Paper-facing regime used after the Claim 2.4 translation step in
Golovnev-Ilango-Impagliazzo-Kabanets-Kolokolova-Tal:
distinguish bias `(1 - ε) / 2` from the fair coin `1 / 2`.
-/
def halfVsFairCoinInstance
    (sampleBits : Nat)
    (ε : Rat)
    (hε_pos : 0 < ε)
    (hε_le_one : ε ≤ (1 : Rat)) :
    CoinProblemInstance where
  sampleBits := sampleBits
  lowBias := ((1 : Rat) - ε) / 2
  highBias := (1 : Rat) / 2
  low_nonneg := by
    linarith
  high_le_one := by
    norm_num
  bias_gap := by
    linarith

/-- Low-bias side of the paper-facing half-vs-fair regime is nonnegative. -/
theorem halfVsFair_lowBias_nonneg
    {ε : Rat}
    (hε_le_one : ε ≤ (1 : Rat)) :
    0 ≤ ((1 : Rat) - ε) / 2 := by
  linarith

/-- The paper-facing half-vs-fair regime has a genuine gap when `ε > 0`. -/
theorem halfVsFair_lowBias_lt_fair
    {ε : Rat}
    (hε_pos : 0 < ε) :
    ((1 : Rat) - ε) / 2 < (1 : Rat) / 2 := by
  linarith

end AlgorithmsToLowerBounds
end Pnp4
