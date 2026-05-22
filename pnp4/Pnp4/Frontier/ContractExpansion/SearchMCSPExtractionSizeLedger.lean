import Pnp4.Frontier.ContractExpansion.SearchMCSPTargetSurface

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
Abstract per-length size bound for a prefix-language decider family.

`deciderSize n` is the size of the decider circuit at target parameter `n`.
`deciderExp` records a polynomial envelope against the ambient parser length
`M n` supplied by the parser obligations package.
-/
def PrefixDeciderSizeBound
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (deciderSize : Nat → Nat)
    (deciderExp : Nat) : Prop :=
  ∀ n : Nat, deciderSize n ≤ (obligations.M n) ^ deciderExp + deciderExp

/--
Estimated output-bit size used by the R1-C extraction ledger.

For output coordinate `j` at target parameter `n`, this upper bound consists of:

- one decider call budget (`deciderSize n`),
- `j+1` rounds of prefix-state recomputation (`(j+1) * stepOverhead n`),
- fixed encoder/parser scaffolding (`encoderOverhead n`).

This deliberately over-approximates and keeps every ingredient explicit.
-/
def estimatedOutputBitSize
    (deciderSize stepOverhead encoderOverhead : Nat → Nat)
    (n j : Nat) : Nat :=
  deciderSize n + (j + 1) * stepOverhead n + encoderOverhead n

/--
Extraction-size ledger for the concrete tree-MCSP target.

This structure does not construct extraction circuits; it only records explicit
numeric obligations sufficient to bound per-output-bit circuit size under the
current `BoundedSearchSolver` representation (separate circuits per output bit).
-/
structure PrefixExtractionSizeLedger
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding) where
  deciderSize : Nat → Nat
  stepOverhead : Nat → Nat
  encoderOverhead : Nat → Nat
  deciderExp : Nat
  witnessExp : Nat
  encoderExp : Nat
  deciderPolynomial :
    PrefixDeciderSizeBound threshold encoding obligations deciderSize deciderExp
  witnessBitsPolynomial :
    ∀ n : Nat,
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem.witnessBits n ≤
        (obligations.M n) ^ witnessExp + witnessExp
  encoderOverheadPolynomial :
    ∀ n : Nat,
      encoderOverhead n ≤ (obligations.M n) ^ encoderExp + encoderExp
  outputCircuitSizeBound :
    ∀ n j : Nat,
      j < (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem.witnessBits n →
        estimatedOutputBitSize deciderSize stepOverhead encoderOverhead n j ≤ sizeBound n

/--
Pointwise extraction-size theorem: any landed ledger yields the required per-bit
size bound immediately.
-/
theorem extraction_output_bit_size_bound
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    {sizeBound : Nat → Nat}
    {obligations : TreeMCSPPrefixParserObligations threshold encoding}
    (ledger : PrefixExtractionSizeLedger threshold encoding sizeBound obligations)
    (n j : Nat)
    (hj : j < (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem.witnessBits n) :
    estimatedOutputBitSize
      ledger.deciderSize
      ledger.stepOverhead
      ledger.encoderOverhead
      n j ≤ sizeBound n :=
  ledger.outputCircuitSizeBound n j hj

/--
Packaging theorem: if a caller can furnish all size ingredients and inequalities,
then a concrete extraction ledger exists.
-/
theorem sizeBound_sufficient_for_prefix_extraction
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (deciderSize stepOverhead encoderOverhead : Nat → Nat)
    (deciderExp witnessExp encoderExp : Nat)
    (hDec : PrefixDeciderSizeBound threshold encoding obligations deciderSize deciderExp)
    (hWit :
      ∀ n : Nat,
        (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem.witnessBits n ≤
          (obligations.M n) ^ witnessExp + witnessExp)
    (hEnc : ∀ n : Nat, encoderOverhead n ≤ (obligations.M n) ^ encoderExp + encoderExp)
    (hOut :
      ∀ n j : Nat,
        j < (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem.witnessBits n →
          estimatedOutputBitSize deciderSize stepOverhead encoderOverhead n j ≤ sizeBound n) :
    PrefixExtractionSizeLedger threshold encoding sizeBound obligations :=
  { deciderSize := deciderSize
    stepOverhead := stepOverhead
    encoderOverhead := encoderOverhead
    deciderExp := deciderExp
    witnessExp := witnessExp
    encoderExp := encoderExp
    deciderPolynomial := hDec
    witnessBitsPolynomial := hWit
    encoderOverheadPolynomial := hEnc
    outputCircuitSizeBound := hOut }

/--
Minimal explicit arithmetic lower bound often needed by extraction proofs:
sizeBound dominates one decider call plus one encoder block.
-/
theorem sizeBound_dominates_decider_and_encoder
    {sizeBound deciderSize stepOverhead encoderOverhead : Nat → Nat}
    {n j : Nat}
    (hMain :
      estimatedOutputBitSize deciderSize stepOverhead encoderOverhead n j ≤ sizeBound n) :
    deciderSize n + encoderOverhead n ≤ sizeBound n := by
  unfold estimatedOutputBitSize at hMain
  have hLe : deciderSize n + encoderOverhead n ≤
      deciderSize n + (j + 1) * stepOverhead n + encoderOverhead n := by
    have hMul : 0 ≤ (j + 1) * stepOverhead n := Nat.zero_le _
    omega
  exact le_trans hLe hMain

end ContractExpansion
end Frontier
end Pnp4
