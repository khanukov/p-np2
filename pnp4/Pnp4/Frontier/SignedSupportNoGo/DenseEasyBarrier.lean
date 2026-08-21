import Pnp4.Frontier.SignedSupportNoGo.FiniteSetDAG

/-!
# Dense/easy signed-support no-go

An explicit finite cover of all `Easy` strings can be hard-coded into the
finite-set avoider.  If the cover is below half the Boolean cube and that
avoider fits the tested DAG size budget, its complement is a dense predicate
accepting no easy string.  This refutes both the dense/easy intersection
premise and any reverse-one-sided signed fooler whose image is easy.

All cover, density, and outer-size inequalities are theorem premises.  The
asymptotic endpoint treats the truth-table geometry `N = 2^n`; it rules out an
all-exponent dense/easy quantifier pattern for eventually linear cover bits.
It does not construct such a cover, prove its sparsity, or imply a complexity
class separation.
-/

open scoped BigOperators

namespace Pnp4.Frontier.SignedSupportNoGo

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-- An explicit finite cover of every string satisfying `Easy`.  `codeBits`
is only a cardinality certificate; no decoder or codec is hidden here. -/
structure FiniteEasyCover (N : Nat) (Easy : Bitstring N → Prop) where
  codeBits : Nat
  tables : Finset (Bitstring N)
  covers : ∀ input, Easy input → input ∈ tables
  card_le : tables.card ≤ 2 ^ codeBits

/-- Witness-set formulation of density strictly above one half. -/
def DenseAboveHalf {N : Nat} (predicate : Bitstring N → Bool) : Prop :=
  ∃ witnesses : Finset (Bitstring N),
    2 ^ N < witnesses.card * 2 ∧
      ∀ input, input ∈ witnesses → predicate input = true

/-- Dense predicates computed by standard DAGs must hit the generator image. -/
def HitsDenseDAGPredicates
    {Seed : Type*} [Fintype Seed] {N : Nat}
    (generator : Seed → Bitstring N) (maxSize : Nat) : Prop :=
  ∀ circuit : DagCircuit N, size circuit ≤ maxSize →
    DenseAboveHalf (fun input => eval circuit input) →
      ∃ seed, eval circuit (generator seed) = true

/-- Generator-free semantic endpoint: every dense bounded-DAG predicate
accepts an explicitly easy string. -/
def EveryDenseDAGPredicateAcceptsEasyTable
    {N : Nat} (Easy : Bitstring N → Prop) (maxSize : Nat) : Prop :=
  ∀ circuit : DagCircuit N, size circuit ≤ maxSize →
    DenseAboveHalf (fun input => eval circuit input) →
      ∃ input, Easy input ∧ eval circuit input = true

/-- A dense-hitting generator with pointwise easy image supplies the
generator-free dense/easy intersection. -/
theorem everyDenseDAGPredicateAcceptsEasyTable_of_hitsDense
    {Seed : Type*} [Fintype Seed] {N : Nat}
    (generator : Seed → Bitstring N) (Easy : Bitstring N → Prop)
    (maxSize : Nat) (hImageEasy : ∀ seed, Easy (generator seed))
    (hHits : HitsDenseDAGPredicates generator maxSize) :
    EveryDenseDAGPredicateAcceptsEasyTable Easy maxSize := by
  intro circuit hSize hDense
  rcases hHits circuit hSize hDense with ⟨seed, hAccepts⟩
  exact ⟨generator seed, hImageEasy seed, hAccepts⟩

/-- A witness-set density certificate implies uniform rational mass above
one half. -/
theorem uniformPredicateAverage_gt_half_of_dense
    {N : Nat} (predicate : Bitstring N → Bool)
    (hDense : DenseAboveHalf predicate) :
    (1 : Rat) / 2 < uniformPredicateAverage predicate := by
  classical
  rcases hDense with ⟨witnesses, hWitnessCard, hAccepts⟩
  have hPointwise : ∀ input : Bitstring N,
      (if input ∈ witnesses then (1 : Rat) else 0) ≤
        boolIndicator (predicate input) := by
    intro input
    by_cases hMem : input ∈ witnesses
    · simp [hMem, boolIndicator, hAccepts input hMem]
    · simp [hMem, boolIndicator_nonneg]
  have hSum : (witnesses.card : Rat) ≤
      ∑ input : Bitstring N, boolIndicator (predicate input) := by
    have hTermwise := Finset.sum_le_sum fun input
      (_ : input ∈ (Finset.univ : Finset (Bitstring N))) =>
        hPointwise input
    simpa using hTermwise
  have hCardRat : ((2 ^ N : Nat) : Rat) < (witnesses.card : Rat) * 2 := by
    exact_mod_cast hWitnessCard
  unfold uniformPredicateAverage
  have hCubeCard : Fintype.card (Bitstring N) = 2 ^ N := by simp
  rw [hCubeCard]
  have hPositive : (0 : Rat) < (2 ^ N : Nat) := by positivity
  apply (lt_div_iff₀ hPositive).2
  linarith

private theorem avoidFiniteSetDAG_dense_of_card
    {N : Nat} (forbidden : Finset (Bitstring N))
    (hSparse : forbidden.card * 2 < 2 ^ N) :
    DenseAboveHalf
      (fun input => eval (avoidFiniteSetDAG forbidden) input) := by
  classical
  let witnesses : Finset (Bitstring N) := Finset.univ \ forbidden
  have hCard : witnesses.card = 2 ^ N - forbidden.card := by
    dsimp [witnesses]
    rw [Finset.card_sdiff (Finset.subset_univ _)]
    simp
  have hDense : 2 ^ N < witnesses.card * 2 := by
    rw [hCard]
    omega
  refine ⟨witnesses, hDense, ?_⟩
  intro input hInput
  have hNotMem : input ∉ forbidden := by
    simpa [witnesses] using hInput
  simp [hNotMem]

private theorem cover_sparse
    {N : Nat} {Easy : Bitstring N → Prop}
    (cover : FiniteEasyCover N Easy)
    (hSparse : (2 ^ cover.codeBits) * 2 < 2 ^ N) :
    cover.tables.card * 2 < 2 ^ N := by
  exact lt_of_le_of_lt (Nat.mul_le_mul_right 2 cover.card_le) hSparse

private theorem avoidCover_rejects_easy
    {N : Nat} {Easy : Bitstring N → Prop}
    (cover : FiniteEasyCover N Easy) {input : Bitstring N}
    (hEasy : Easy input) :
    eval (avoidFiniteSetDAG cover.tables) input = false := by
  simp [cover.covers input hEasy]

/-- Direct dense/easy no-go.  The first premise makes the cover occupy less
than half the cube; the second makes its explicit avoider fit the tested DAG
class. -/
theorem not_everyDenseDAGPredicateAcceptsEasyTable_of_cover_fits
    {N maxSize : Nat} {Easy : Bitstring N → Prop}
    (cover : FiniteEasyCover N Easy)
    (hSparse : (2 ^ cover.codeBits) * 2 < 2 ^ N)
    (hFits : (2 ^ cover.codeBits) * (2 * N + 2) + 3 ≤ maxSize) :
    ¬ EveryDenseDAGPredicateAcceptsEasyTable Easy maxSize := by
  intro hEvery
  let avoider := avoidFiniteSetDAG cover.tables
  have hSize : size avoider ≤ maxSize := by
    apply (size_avoidFiniteSetDAG_le cover.tables).trans
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right (2 * N + 2) cover.card_le) 3 |>.trans hFits
  have hDense : DenseAboveHalf (fun input => eval avoider input) :=
    avoidFiniteSetDAG_dense_of_card cover.tables (cover_sparse cover hSparse)
  rcases hEvery avoider hSize hDense with ⟨input, hEasy, hAccepts⟩
  have hRejects : eval avoider input = false :=
    avoidCover_rejects_easy cover hEasy
  exact Bool.false_ne_true (hRejects.symm.trans hAccepts)

/-- Signed-fooling no-go.  If every generator output is easy, then no signed,
unnormalized rational weights can reverse-one-sided-fool the tested DAG class
at error below one half under the same explicit sparsity and size premises. -/
theorem not_exists_reverseOneSidedFoolsDAG_of_easyImage_cover_fits
    {Seed : Type*} [Fintype Seed] {N maxSize : Nat}
    {Easy : Bitstring N → Prop}
    (generator : Seed → Bitstring N) (hImageEasy : ∀ seed, Easy (generator seed))
    (cover : FiniteEasyCover N Easy) (epsilon : Rat)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hSparse : (2 ^ cover.codeBits) * 2 < 2 ^ N)
    (hFits : (2 ^ cover.codeBits) * (2 * N + 2) + 3 ≤ maxSize) :
    ¬ ∃ weight : Seed → Rat,
      ReverseOneSidedFoolsDAG generator weight maxSize epsilon := by
  rintro ⟨weight, hFools⟩
  let avoider := avoidFiniteSetDAG cover.tables
  have hSize : size avoider ≤ maxSize := by
    apply (size_avoidFiniteSetDAG_le cover.tables).trans
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right (2 * N + 2) cover.card_le) 3 |>.trans hFits
  have hDense : DenseAboveHalf (fun input => eval avoider input) :=
    avoidFiniteSetDAG_dense_of_card cover.tables (cover_sparse cover hSparse)
  have hUniform : (1 : Rat) / 2 <
      uniformPredicateAverage (fun input : Bitstring N => eval avoider input) :=
    uniformPredicateAverage_gt_half_of_dense _ hDense
  rcases lowerWeightedApproximation_support_hits generator weight
      (fun input : Bitstring N => eval avoider input) epsilon
      (hFools avoider hSize) (hEpsilon.trans hUniform) with
    ⟨seed, _, hAccepts⟩
  have hRejects : eval avoider (generator seed) = false :=
    avoidCover_rejects_easy cover (hImageEasy seed)
  exact Bool.false_ne_true (hRejects.symm.trans hAccepts)

private theorem not_everyDense_polynomial_of_coverBudget
    {n exponent : Nat} {Easy : Bitstring (2 ^ n) → Prop}
    (cover : FiniteEasyCover (2 ^ n) Easy)
    (hExponent : 2 ≤ exponent)
    (hSparse : (2 ^ cover.codeBits) * 2 < 2 ^ (2 ^ n))
    (hCoverBudget : cover.codeBits + n + 2 ≤ n * exponent) :
    ¬ EveryDenseDAGPredicateAcceptsEasyTable Easy
      ((2 ^ n) ^ exponent + exponent + 1) := by
  apply not_everyDenseDAGPredicateAcceptsEasyTable_of_cover_fits cover hSparse
  let N := 2 ^ n
  have hFactor : 2 * N + 2 ≤ 4 * N := by
    have hNPositive : 0 < N := by positivity
    omega
  have hPowerExponent :
      2 ^ (cover.codeBits + n + 2) ≤ 2 ^ (n * exponent) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hCoverBudget
  have hCore :
      (2 ^ cover.codeBits) * (2 * N + 2) ≤ N ^ exponent := by
    calc
      (2 ^ cover.codeBits) * (2 * N + 2) ≤
          (2 ^ cover.codeBits) * (4 * N) :=
        Nat.mul_le_mul_left _ hFactor
      _ = 2 ^ (cover.codeBits + n + 2) := by
        simp [N, pow_add]
        ring
      _ ≤ 2 ^ (n * exponent) := hPowerExponent
      _ = N ^ exponent := by simp [N, pow_mul]
  dsimp [N] at hCore ⊢
  omega

/-- Eventual-linear cover-bits obstruction in truth-table geometry.  A finite
prefix is absorbed into the chosen exponent, so the linear hypothesis is
genuinely eventual rather than silently global.  The all-exponent premise
still explicitly supplies cover sparsity at its chosen slice. -/
theorem not_allExponent_everyDenseDAGPredicateAcceptsEasyTable_of_coverBits_eventuallyLinear
    (Easy : ∀ n, Bitstring (2 ^ n) → Prop)
    (cover : ∀ n, FiniteEasyCover (2 ^ n) (Easy n))
    (linearConstant : Nat)
    (hEventuallyLinear : ∃ cutoff, ∀ n, cutoff ≤ n →
      (cover n).codeBits ≤ linearConstant * n) :
    ¬ ∀ exponent, ∃ n,
      (2 ^ (cover n).codeBits) * 2 < 2 ^ (2 ^ n) ∧
      EveryDenseDAGPredicateAcceptsEasyTable (Easy n)
        ((2 ^ n) ^ exponent + exponent + 1) := by
  rcases hEventuallyLinear with ⟨cutoff, hLinear⟩
  let prefixBudget : Nat :=
    ∑ index ∈ Finset.range cutoff,
      ((cover index).codeBits + index + 2)
  let exponent : Nat := linearConstant + prefixBudget + 3
  intro hAll
  rcases hAll exponent with ⟨n, hSparse, hEvery⟩
  have hNPositive : 0 < n := by
    by_contra hNotPositive
    have hZero : n = 0 := by omega
    subst n
    have hPowPositive : 0 < 2 ^ (cover 0).codeBits := by positivity
    norm_num at hSparse
  have hExponent : 2 ≤ exponent := by
    simp [exponent]
  have hCoverBudget :
      (cover n).codeBits + n + 2 ≤ n * exponent := by
    by_cases hLate : cutoff ≤ n
    · have hCode := hLinear n hLate
      have hBase : (cover n).codeBits + n + 2 ≤
          n * (linearConstant + 3) := by
        calc
          (cover n).codeBits + n + 2 ≤
              linearConstant * n + n + 2 := by omega
          _ ≤ n * (linearConstant + 3) := by nlinarith
      have hMonotone : linearConstant + 3 ≤ exponent := by
        dsimp [exponent]
        omega
      exact hBase.trans (Nat.mul_le_mul_left n hMonotone)
    · have hBefore : n < cutoff := by omega
      have hMem : n ∈ Finset.range cutoff := Finset.mem_range.mpr hBefore
      have hTerm : (cover n).codeBits + n + 2 ≤ prefixBudget := by
        dsimp [prefixBudget]
        exact Finset.single_le_sum
          (fun index _ => Nat.zero_le ((cover index).codeBits + index + 2)) hMem
      have hPrefixLe : prefixBudget ≤ exponent := by
        dsimp [exponent]
        omega
      have hOneLeN : 1 ≤ n := Nat.succ_le_iff.mpr hNPositive
      calc
        (cover n).codeBits + n + 2 ≤ prefixBudget := hTerm
        _ ≤ exponent := hPrefixLe
        _ = 1 * exponent := by simp
        _ ≤ n * exponent := Nat.mul_le_mul_right exponent hOneLeN
  exact (not_everyDense_polynomial_of_coverBudget
    (cover n) hExponent hSparse hCoverBudget) hEvery

end Pnp4.Frontier.SignedSupportNoGo
