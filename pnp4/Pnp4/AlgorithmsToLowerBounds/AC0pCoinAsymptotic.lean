import Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative
import Mathlib.Tactic

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Global language attached to one half-vs-fair MCSP coin-reduction contract.

On truth-table lengths `2^n` this is the `n`-th thresholded MCSP slice from the
reduction.  Off those lengths it returns `false`; the lower-bound theorems below
therefore use truth-table-slice growth, not a dense `EventuallySizeLowerBound`.
-/
noncomputable def halfVsFairMCSPCoinAsymptoticLanguage
    {hardness : HalfVsFairTruthTableCoinHardness}
    (reduction : HalfVsFairMCSPCoinReductionContract hardness) :
    BitVecLanguage := by
  classical
  intro m x
  exact if hm : m = Pnp3.Models.Partial.tableLen (Nat.log 2 m) then
      halfVsFairMCSPCoinLanguage reduction (Nat.log 2 m) m x
    else
      false

/--
At canonical truth-table lengths, the global asymptotic language agrees with
the corresponding half-vs-fair MCSP coin slice.
-/
theorem halfVsFairMCSPCoinAsymptoticLanguage_eq_slice_at_tableLen
    {hardness : HalfVsFairTruthTableCoinHardness}
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat)
    (x : BitVec (Pnp3.Models.Partial.tableLen n)) :
    halfVsFairMCSPCoinAsymptoticLanguage reduction
        (Pnp3.Models.Partial.tableLen n) x =
      halfVsFairMCSPCoinLanguage reduction n
        (Pnp3.Models.Partial.tableLen n) x := by
  have hlog :
      Nat.log 2 (Pnp3.Models.Partial.tableLen n) = n := by
    simpa [Pnp3.Models.Partial.tableLen] using Nat.log_pow Nat.one_lt_two n
  have hm :
      Pnp3.Models.Partial.tableLen n =
        Pnp3.Models.Partial.tableLen
          (Nat.log 2 (Pnp3.Models.Partial.tableLen n)) := by
    rw [hlog]
  unfold halfVsFairMCSPCoinAsymptoticLanguage
  have hIf :
      (if hm' :
            Pnp3.Models.Partial.tableLen n =
              Pnp3.Models.Partial.tableLen
                (Nat.log 2 (Pnp3.Models.Partial.tableLen n)) then
          halfVsFairMCSPCoinLanguage reduction
            (Nat.log 2 (Pnp3.Models.Partial.tableLen n))
            (Pnp3.Models.Partial.tableLen n) x
        else
          false) =
        halfVsFairMCSPCoinLanguage reduction
          (Nat.log 2 (Pnp3.Models.Partial.tableLen n))
          (Pnp3.Models.Partial.tableLen n) x := by
    exact if_pos hm
  rw [hIf, hlog]

/--
Truth-table-slice growth condition sufficient to refute polynomial-size
families from slice lower bounds.

This is intentionally weaker and more precise than a dense
`EventuallySizeLowerBound`: it only asks the published size schedule to beat a
candidate polynomial on some truth-table length.
-/
def BeatsEveryPolynomialSizeBoundAtSomeTableLength
    (sizeBound : Nat → Nat) : Prop :=
  ∀ a k : Nat,
    ∃ n : Nat,
      a * (Pnp3.Models.Partial.tableLen n) ^ k < sizeBound n + 1

/--
Stronger table-slice growth condition matching asymptotic published lower-bound
statements: every polynomial bound is beaten at arbitrarily late truth-table
slices.
-/
def BeatsEveryPolynomialSizeBoundAtArbitrarilyLargeTableLengths
    (sizeBound : Nat → Nat) : Prop :=
  ∀ a k n0 : Nat,
    ∃ n : Nat,
      n0 ≤ n ∧
        a * (Pnp3.Models.Partial.tableLen n) ^ k < sizeBound n + 1

/-- Arbitrarily-large table-slice growth implies the one-shot growth condition. -/
theorem BeatsEveryPolynomialSizeBoundAtSomeTableLength.of_arbitrarilyLarge
    {sizeBound : Nat → Nat}
    (hGrowth :
      BeatsEveryPolynomialSizeBoundAtArbitrarilyLargeTableLengths sizeBound) :
    BeatsEveryPolynomialSizeBoundAtSomeTableLength sizeBound := by
  intro a k
  rcases hGrowth a k 0 with ⟨n, _hn0, hBeat⟩
  exact ⟨n, hBeat⟩

private theorem two_mul_add_one_lt_two_pow_of_four_le
    (n : Nat)
    (hn : 4 ≤ n) :
    2 * n + 1 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      have hTwoLePow : 2 ≤ 2 ^ n := by
        have hOneLe : 1 ≤ n := by omega
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hOneLe
      calc
        2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
        _ < 2 ^ n + 2 := Nat.add_lt_add_right ih 2
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left hTwoLePow (2 ^ n)
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

private theorem linear_lt_two_pow_at_arbitrarilyLarge
    (A B nMin : Nat) :
    ∃ t : Nat, nMin ≤ t ∧ A * t + B < 2 ^ t := by
  let r := max 4 (A + B + nMin + 10)
  let q := 2 ^ r
  let t := 2 ^ q
  have hr4 : 4 ≤ r := Nat.le_max_left 4 (A + B + nMin + 10)
  have hRightLeR : A + B + nMin + 10 ≤ r :=
    Nat.le_max_right 4 (A + B + nMin + 10)
  have hALeR : A ≤ r := by
    exact le_trans (by omega) hRightLeR
  have hBLeR : B ≤ r := by
    exact le_trans (by omega) hRightLeR
  have hnMinLeR : nMin ≤ r := by
    exact le_trans (by omega) hRightLeR
  have hrLeQ : r ≤ q := Nat.le_of_lt Nat.lt_two_pow_self
  have hqLeT : q ≤ t := Nat.le_of_lt Nat.lt_two_pow_self
  have hALeT : A ≤ t := le_trans hALeR (le_trans hrLeQ hqLeT)
  have hBLeT : B ≤ t := le_trans hBLeR (le_trans hrLeQ hqLeT)
  have hnMinLeT : nMin ≤ t := le_trans hnMinLeR (le_trans hrLeQ hqLeT)
  have htPos : 0 < t := Nat.two_pow_pos q
  have htLeSquare : t ≤ t * t := Nat.le_mul_of_pos_left t htPos
  have hLinearLe : A * t + B ≤ t * t + t := by
    exact Nat.add_le_add (Nat.mul_le_mul_right t hALeT) hBLeT
  have hSquareLeDoubleSquare : t * t + t ≤ 2 * (t * t) := by
    calc
      t * t + t ≤ t * t + t * t := Nat.add_le_add_left htLeSquare (t * t)
      _ = 2 * (t * t) := by omega
  have hDoubleSquareEq : 2 * (t * t) = 2 ^ (2 * q + 1) := by
    have htSquare : t * t = 2 ^ (q + q) := by
      simp [t, Nat.pow_add]
    calc
      2 * (t * t) = 2 ^ 1 * 2 ^ (q + q) := by
        simp [htSquare]
      _ = 2 ^ (1 + (q + q)) := by
        rw [← Nat.pow_add]
      _ = 2 ^ (2 * q + 1) := by
        congr 1
        omega
  have hq4 : 4 ≤ q := by
    have h16LeQ : 2 ^ 4 ≤ q := by
      simpa [q] using Nat.pow_le_pow_right (by decide : 0 < 2) hr4
    exact le_trans (by decide : 4 ≤ 16) (by simpa using h16LeQ)
  have hExpLt : 2 * q + 1 < t := by
    simpa [t] using two_mul_add_one_lt_two_pow_of_four_le q hq4
  have hPowLt : 2 ^ (2 * q + 1) < 2 ^ t :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hExpLt
  refine ⟨t, hnMinLeT, ?_⟩
  exact lt_of_le_of_lt (le_trans hLinearLe (le_trans hSquareLeDoubleSquare
    (le_of_eq hDoubleSquareEq))) hPowLt

private theorem polynomial_on_tableLen_le_two_pow_linear
    (a k D s : Nat) :
    a * (Pnp3.Models.Partial.tableLen (D * s)) ^ k ≤
      2 ^ ((D * k) * s + (a + 1)) := by
  have haLe : a ≤ 2 ^ (a + 1) := by
    exact Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hTablePow :
      (Pnp3.Models.Partial.tableLen (D * s)) ^ k =
        2 ^ ((D * k) * s) := by
    calc
      (Pnp3.Models.Partial.tableLen (D * s)) ^ k =
          (2 ^ (D * s)) ^ k := by
            simp [Pnp3.Models.Partial.tableLen]
      _ = 2 ^ ((D * s) * k) := by
            rw [← Nat.pow_mul]
      _ = 2 ^ ((D * k) * s) := by
            congr 1
            ac_rfl
  calc
    a * (Pnp3.Models.Partial.tableLen (D * s)) ^ k
        ≤ 2 ^ (a + 1) * 2 ^ ((D * k) * s) := by
          exact Nat.mul_le_mul haLe (le_of_eq hTablePow)
    _ = 2 ^ ((a + 1) + (D * k) * s) := by
          rw [← Nat.pow_add]
    _ = 2 ^ ((D * k) * s + (a + 1)) := by
          congr 1
          omega

/--
The published AC0[p] coin lower-envelope beats every polynomial-size bound on
arbitrarily late truth-table lengths.
-/
theorem ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths
    (envelopeConst depth : Nat) :
    BeatsEveryPolynomialSizeBoundAtArbitrarilyLargeTableLengths
      (fun n => ac0pCoinLowerEnvelope envelopeConst depth n) := by
  intro a k n0
  let D := 100 * (depth + envelopeConst + 1)
  have hDPos : 0 < D := by
    dsimp [D]
    positivity
  rcases linear_lt_two_pow_at_arbitrarilyLarge
      (D * k) (a + 1) n0 with ⟨s, hsMin, hLinearLt⟩
  refine ⟨D * s, ?_, ?_⟩
  · exact le_trans hsMin (Nat.le_mul_of_pos_left s hDPos)
  · have hPolyLe :
        a * (Pnp3.Models.Partial.tableLen (D * s)) ^ k ≤
          2 ^ ((D * k) * s + (a + 1)) :=
      polynomial_on_tableLen_le_two_pow_linear a k D s
    have hPowLt :
        2 ^ ((D * k) * s + (a + 1)) < 2 ^ (2 ^ (49 * s)) :=
      have hsLe : s ≤ 49 * s := Nat.le_mul_of_pos_left s (by decide : 0 < 49)
      have hLinearLt49 :
          (D * k) * s + (a + 1) < 2 ^ (49 * s) :=
        lt_of_lt_of_le hLinearLt
          (Nat.pow_le_pow_right (by decide : 0 < 2) hsLe)
      Nat.pow_lt_pow_right (by decide : 1 < 2) hLinearLt49
    have hDiv :
        (49 * (D * s)) / (100 * (depth + envelopeConst + 1)) = 49 * s := by
      have hDen : 100 * (depth + envelopeConst + 1) = D := rfl
      rw [hDen]
      have hMul : 49 * (D * s) = D * (49 * s) := by ac_rfl
      rw [hMul]
      exact Nat.mul_div_right (49 * s) hDPos
    have hEnvelopeEq :
        ac0pCoinLowerEnvelope envelopeConst depth (D * s) =
          2 ^ (2 ^ (49 * s)) := by
      simp [ac0pCoinLowerEnvelope, hDiv]
    exact lt_of_le_of_lt hPolyLe
      (lt_of_lt_of_le hPowLt (by
        change 2 ^ (2 ^ (49 * s)) ≤
          ac0pCoinLowerEnvelope envelopeConst depth (D * s) + 1
        rw [hEnvelopeEq]
        exact Nat.le_succ _))

/--
One fixed-depth published AC0[p]/coin lower-bound contract, plus truth-table
slice growth, rules out polynomial-size families for the corresponding global
asymptotic MCSP coin language.
-/
theorem not_hasPolynomialSizeFamily_halfVsFairMCSPCoinAsymptoticLanguage
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth : Nat}
    (hp : Nat.Prime p)
    (hGrowth :
      BeatsEveryPolynomialSizeBoundAtSomeTableLength
        (fun n => ac0pCoinLowerEnvelope contract.envelopeConst depth n)) :
    ¬ HasPolynomialSizeFamily
        (model.classOf p depth)
        (halfVsFairMCSPCoinAsymptoticLanguage reduction) := by
  intro hPoly
  rcases hPoly with ⟨a, k, hFamily⟩
  rcases hGrowth a k with ⟨n, hBeat⟩
  let N := Pnp3.Models.Partial.tableLen n
  rcases hFamily N with ⟨circ, hCorrect, hSize⟩
  have hComputesSlice :
      ∀ x : BitVec N,
        (model.classOf p depth).eval circ x =
          halfVsFairMCSPCoinLanguage reduction n N x := by
    intro x
    calc
      (model.classOf p depth).eval circ x =
          halfVsFairMCSPCoinAsymptoticLanguage reduction N x := hCorrect x
      _ = halfVsFairMCSPCoinLanguage reduction n N x := by
        exact halfVsFairMCSPCoinAsymptoticLanguage_eq_slice_at_tableLen
          reduction n x
  have hLowerFull :
      exactTreeMCSPThresholdLowerBound
          n
          (ac0pCoinLowerEnvelope contract.envelopeConst depth n)
          N ≤
        (model.classOf p depth).size circ :=
    MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
      contract
      reduction
      (p := p)
      (depth := depth)
      (n := n)
      hp
      N
      circ
      hComputesSlice
  have hLower :
      ac0pCoinLowerEnvelope contract.envelopeConst depth n + 1 ≤
        (model.classOf p depth).size circ := by
    simpa [N, exactTreeMCSPThresholdLowerBound] using hLowerFull
  have hUpper :
      (model.classOf p depth).size circ ≤ a * N ^ k :=
    hSize
  have hContradiction :
      ac0pCoinLowerEnvelope contract.envelopeConst depth n + 1 ≤
        a * N ^ k :=
    le_trans hLower hUpper
  exact (Nat.not_lt_of_ge hContradiction) hBeat

/--
Published AC0[p]/coin contract compiled into `¬ InAC0p`, provided the published
envelope beats every polynomial on truth-table lengths at each fixed depth.

The theorem name is deliberately `from_published_contract_and_growth`: this is
not a repo-unconditional MCSP lower bound until the published contract and its
growth instantiation are proved internally.
-/
theorem not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    (hGrowth :
      ∀ depth : Nat,
        BeatsEveryPolynomialSizeBoundAtSomeTableLength
          (fun n => ac0pCoinLowerEnvelope contract.envelopeConst depth n))
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p (halfVsFairMCSPCoinAsymptoticLanguage reduction) := by
  intro hIn
  rcases hIn with ⟨depth, hPoly⟩
  exact
    (not_hasPolynomialSizeFamily_halfVsFairMCSPCoinAsymptoticLanguage
      contract
      reduction
      (p := p)
      (depth := depth)
      hp
      (hGrowth depth)) hPoly

/--
Published AC0[p]/coin contract compiled into `¬ InAC0p` for the global
half-vs-fair MCSP coin asymptotic language.

This discharges the arithmetic growth obligation for the concrete published
envelope.  The result is still explicitly `from_published_contract`: the
published coin lower-bound contract and the MCSP-to-coin reduction contract are
the remaining source inputs.
-/
theorem not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p (halfVsFairMCSPCoinAsymptoticLanguage reduction) := by
  exact
    not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
      contract
      reduction
      (fun depth =>
        BeatsEveryPolynomialSizeBoundAtSomeTableLength.of_arbitrarilyLarge
          (ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths
            contract.envelopeConst depth))
      p
      hp

end AlgorithmsToLowerBounds
end Pnp4
