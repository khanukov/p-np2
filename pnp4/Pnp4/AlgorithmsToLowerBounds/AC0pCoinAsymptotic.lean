import Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative

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

end AlgorithmsToLowerBounds
end Pnp4
