import Pnp4.Frontier.ContractExpansion.SearchMCSPExtractionSizeLedger

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
Prefix state available before extracting witness bit `j`.

This is intentionally lightweight: at R1-C2 we only expose the circuit-theorem
surface and keep the actual recursive extractor construction out of scope.
-/
structure PrefixDecisionState
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (n j : Nat) where
  prefixLength : Nat
  prefixLength_eq : prefixLength = j
  selectedPrefix : PrefixBitVec prefixLength

/--
Concrete one-branch prefix query input for bit extraction.

The query corresponds to extending the already selected prefix by one branch bit
`b` and asking whether this longer prefix is extendable in the extracted
`PrefixExtensionLanguage`.
-/
structure PrefixQueryInput
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (n j : Nat) where
  branchBit : Bool
  ambientLen : Nat
  ambientLen_eq : ambientLen = obligations.M n
  payload : PrefixBitVec ambientLen

/--
Staged query-builder obligation for the `(prefix, branchBit)` encoding.

At R1-C2 we do not build the encoding circuit yet; we only expose the exact
interface needed by the one-bit extraction circuit obligations.
-/
def BuildPrefixQueryForBitObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (n j : Nat) : Type :=
  PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n) →
    PrefixDecisionState threshold encoding (fun _ => 0) obligations n j →
      Bool → PrefixQueryInput threshold encoding obligations n j

/--
Obligation surface for composing the prefix-language decider with query builder.

Given a decider family for the concrete extracted language and a query builder,
produce a `C_DAG` circuit over the original instance bits that decides whether
`prefix ++ branchBit` is extendable.
-/
structure ComposeDeciderWithPrefixQueryObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (deciderExp : Nat) where
  deciderFamily :
    Pnp3.ComplexityInterfaces.DagCircuitFamily
      (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)
  queryBuilder :
    ∀ n j : Nat,
      BuildPrefixQueryForBitObligation threshold encoding obligations n j
  branchDeciderCircuit :
    ∀ n j : Nat,
      C_DAG.Family ((treeMCSPSearchProblem threshold encoding).instanceBits n)
  branchDeciderSoundness : Prop
  branchDeciderSizeBound :
    ∀ n j : Nat,
      C_DAG.size (branchDeciderCircuit n j) ≤
        estimatedOutputBitSize
          (fun k => (obligations.M k) ^ deciderExp + deciderExp)
          (fun _ => obligations.M n)
          (fun _ => obligations.M n)
          n j

/--
One-bit choice circuit obligation.

The circuit should output:
- `false` (bit 0) when branch-0 is accepted;
- `true` (bit 1) otherwise.

This encodes the standard one-step self-reduction choice rule.
-/
structure OneBitChoiceCircuitObligation
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (n j : Nat) where
  oneBitExtractionCircuit :
    C_DAG.Family ((treeMCSPSearchProblem threshold encoding).instanceBits n)
  chooses_zero_if_branch0_accepts : Prop
  chooses_one_if_branch0_rejects : Prop

/--
Packaged R1-C2 one-bit extraction skeleton.

This structure is the landing surface for constructing one witness-bit circuit
without proving the full extraction theorem.
-/
structure OneBitPrefixExtractionSkeleton
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding) where
  deciderExp : Nat
  composed :
    ComposeDeciderWithPrefixQueryObligation
      threshold encoding sizeBound obligations deciderExp
  oneBit :
    ∀ n j : Nat,
      OneBitChoiceCircuitObligation
        threshold encoding sizeBound obligations n j

/--
Size-connection obligation between one-bit skeleton circuits and the R1-C1
extraction ledger.
-/
def oneBitExtractionCircuit_size_accounted_by_ledger
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (ledger : PrefixExtractionSizeLedger threshold encoding sizeBound obligations)
    (skeleton : OneBitPrefixExtractionSkeleton threshold encoding sizeBound obligations) : Prop :=
  ∀ n j : Nat,
    C_DAG.size ((skeleton.oneBit n j).oneBitExtractionCircuit) ≤
      estimatedOutputBitSize
        ledger.deciderSize
        ledger.stepOverhead
        ledger.encoderOverhead
        n j

/--
Correctness-connection obligation for one-bit extraction.

Given promised instance semantics and an extendable-prefix invariant, the one-bit
circuit output should equal the branch selected by the one-step prefix rule.
-/
def oneBitExtractionCircuit_correct
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (sizeBound : Nat → Nat)
    (obligations : TreeMCSPPrefixParserObligations threshold encoding)
    (skeleton : OneBitPrefixExtractionSkeleton threshold encoding sizeBound obligations)
    (branchRule : ∀ n j : Nat, PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n) → Bool) : Prop :=
  ∀ n j : Nat,
    ∀ x : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n),
      C_DAG.eval ((skeleton.oneBit n j).oneBitExtractionCircuit) x = branchRule n j x

end ContractExpansion
end Frontier
end Pnp4
