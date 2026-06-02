import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Pnp4.AlgorithmsToLowerBounds.Growth
import Pnp4.AlgorithmsToLowerBounds.SuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge
import Pnp4.AlgorithmsToLowerBounds.AsymptoticSizeLowerBound
import Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge
import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Pnp4.AlgorithmsToLowerBounds.LocalPRG
import Pnp4.AlgorithmsToLowerBounds.CoinProblem
import Pnp4.AlgorithmsToLowerBounds.CoinMaskingTranslation
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction
import Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative
import Pnp4.AlgorithmsToLowerBounds.AC0pCoinAsymptotic
import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer
import Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final
import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative
import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitAsymptotic
import Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG
import Pnp4.Frontier.PvsNPBridgeRequirements
import Pnp4.Frontier.CompressionMagnification
import Pnp4.Frontier.SearchMCSPMagnification
import Pnp4.Frontier.SearchMCSPConcreteTargets
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter
import Pnp4.Frontier.ContractExpansion.QueryComposition
import Pnp4.Frontier.ContractExpansion.QueryBuilder
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage
import Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixQueryCircuits
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixStateQueryCircuits
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleStep
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleFold
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyOutputCircuits
import Pnp4.Frontier.ContractExpansion.PrefixExtendableSplit
import Pnp4.Frontier.ContractExpansion.TreeMCSPTrueExtensionQuery
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyExtendable
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyTrueOutputCircuits
import Pnp4.Frontier.ContractExpansion.TreeMCSPDeciderCorrect
import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedySolves
import Pnp4.Frontier.ContractExpansion.TreeMCSPBoundedSolver
import Pnp4.Frontier.ContractExpansion.BoundedSolverFromPpoly
import Pnp4.Frontier.ContractExpansion.NoSolverContrapositive
import Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth
import Pnp4.Frontier.ContractExpansion.ConditionalVerifiedSource
import Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction
import Pnp4.Frontier.ContractExpansion.PrefixExtensionNPWitness
import Pnp4.Frontier.ContractExpansion.ExplicitConditionalSource
import Pnp4.Frontier.ContractExpansion.ConcreteCodecGap
import Pnp4.Frontier.ContractExpansion.CircuitTreeBridge
import Pnp4.Frontier.ContractExpansion.CircuitEncodingLength
import Pnp4.Frontier.ContractExpansion.CircuitDecodeDepthFree
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodecSource
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth
import Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation
import Pnp4.Frontier.ContractExpansion.TreeMCSPZeroPrefixBuilder
import Pnp4.Frontier.ContractExpansion.NaiveGreedySizeSpike
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixVerifierLayout
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.PhasedProgramAccepts
import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter

namespace Pnp4
namespace Tests

open AlgorithmsToLowerBounds

def check_C_DAG : CircuitFamilyClass :=
  Pnp4.Frontier.ContractExpansion.C_DAG

#check Pnp4.Frontier.ContractExpansion.treePrefixTag
#check Pnp4.Frontier.ContractExpansion.tagLen
#check Pnp4.Frontier.ContractExpansion.gammaLen
#check Pnp4.Frontier.ContractExpansion.idxWidth
#check Pnp4.Frontier.ContractExpansion.natBEField
#check Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
#check Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput
#check Pnp4.Frontier.ContractExpansion.treeMCSPConcretePrefixParser
#print axioms Pnp4.Frontier.ContractExpansion.bitLength_pos_of_pos
#print axioms Pnp4.Frontier.ContractExpansion.nat_lt_two_pow_bitLength
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_zero
#print axioms Pnp4.Frontier.ContractExpansion.be_digit_step
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_slice
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_zero_prefix
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_terminator
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_gammaBit_payload
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit_from_at
#print axioms Pnp4.Frontier.ContractExpansion.prefixLength_lt_two_pow_idxWidth
#print axioms Pnp4.Frontier.ContractExpansion.tableLen_le_treeMCSPPrefixM
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_bad_tag
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_malformed_rejected

noncomputable def check_InPpolyDAG_to_C_DAG_family
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.InPpolyDAG L) :
    Pnp4.Frontier.ContractExpansion.PolynomiallyBoundedFamily
      Pnp4.Frontier.ContractExpansion.C_DAG L :=
  Pnp4.Frontier.ContractExpansion.InPpolyDAG_to_C_DAG_family h

def check_C_DAG_family_to_InPpolyDAG
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp4.Frontier.ContractExpansion.PolynomiallyBoundedFamily
      Pnp4.Frontier.ContractExpansion.C_DAG L) :
    Pnp3.ComplexityInterfaces.InPpolyDAG L :=
  Pnp4.Frontier.ContractExpansion.C_DAG_family_to_InPpolyDAG h

theorem check_PpolyDAG_decider_as_C_DAG_decider
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.PpolyDAG L) :
    ∃ c : Nat, ∀ n : Nat, ∃ C : Pnp4.Frontier.ContractExpansion.C_DAG.Family n,
      Pnp4.Frontier.ContractExpansion.C_DAG.size C ≤ n ^ c + c ∧
        ∀ x : AlgorithmsToLowerBounds.BitVec n,
          Pnp4.Frontier.ContractExpansion.C_DAG.eval C x = L n x :=
  Pnp4.Frontier.ContractExpansion.PpolyDAG_decider_as_C_DAG_decider h

section QueryCompositionSurface

open Pnp4.Frontier.ContractExpansion

def check_composeDeciderWithQuery
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    C_DAG.Family inputBits :=
  composeDeciderWithQuery decider queryBit

theorem check_eval_composeDeciderWithQuery
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits)
    (x : AlgorithmsToLowerBounds.BitVec inputBits) :
    C_DAG.eval (composeDeciderWithQuery decider queryBit) x =
      C_DAG.eval decider (fun j => C_DAG.eval (queryBit j) x) :=
  eval_composeDeciderWithQuery decider queryBit x

theorem check_size_composeDeciderWithQuery_le
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    C_DAG.size (composeDeciderWithQuery decider queryBit) ≤
      C_DAG.size decider + ∑ j, C_DAG.size (queryBit j) :=
  size_composeDeciderWithQuery_le decider queryBit

end QueryCompositionSurface

section QueryBuilderSurface

open Pnp4.Frontier.ContractExpansion

def check_QueryCircuitBuilder
    (inputBits queryBits : Nat → Nat) : Type :=
  QueryCircuitBuilder inputBits queryBits

def check_QueryCircuitBuilder_compose
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.Family (inputBits n) :=
  builder.compose n decider

theorem check_QueryCircuitBuilder_eval_compose
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n))
    (x : AlgorithmsToLowerBounds.BitVec (inputBits n)) :
    C_DAG.eval (builder.compose n decider) x =
      C_DAG.eval decider (builder.queryValue n x) :=
  builder.eval_compose n decider x

theorem check_QueryCircuitBuilder_size_compose_le
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.size (builder.compose n decider) ≤
      C_DAG.size decider + ∑ i, C_DAG.size (builder.queryBitCircuit n i) :=
  builder.size_compose_le n decider

theorem check_QueryCircuitBuilder_size_compose_le_bound
    {inputBits queryBits : Nat → Nat}
    (builder : QueryCircuitBuilder inputBits queryBits)
    (n : Nat)
    (decider : C_DAG.Family (queryBits n)) :
    C_DAG.size (builder.compose n decider) ≤
      C_DAG.size decider + (queryBits n) * builder.sizeBound n :=
  builder.size_compose_le_bound n decider

end QueryBuilderSurface

section PrefixQueryBuilderSurface

open Pnp4.Frontier.ContractExpansion

def check_PrefixQueryBuilder
    (problem : Frontier.SearchMCSPCompressionProblem)
    (parser : PrefixParser problem) : Type :=
  PrefixQueryBuilder problem parser

def check_PrefixQueryBuilder_compose
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (decider : C_DAG.Family (parser.M n)) :
    C_DAG.Family (problem.instanceBits n) :=
  pqb.compose n decider

theorem check_PrefixQueryBuilder_eval_compose
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (decider : C_DAG.Family (parser.M n))
    (x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n)) :
    C_DAG.eval (pqb.compose n decider) x =
      C_DAG.eval decider (pqb.queryValue n x) :=
  pqb.eval_compose n decider x

theorem check_PrefixQueryBuilder_size_compose_le
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (decider : C_DAG.Family (parser.M n)) :
    C_DAG.size (pqb.compose n decider) ≤
      C_DAG.size decider + ∑ i, C_DAG.size (pqb.builder.queryBitCircuit n i) :=
  pqb.size_compose_le n decider

theorem check_PrefixQueryBuilder_queryValue_parses
    {problem : Frontier.SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (pqb : PrefixQueryBuilder problem parser)
    (n : Nat)
    (x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n)) :
    ∃ input : PrefixInput problem (parser.M n),
      parsePrefixInput parser (pqb.queryValue n x) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  pqb.queryValue_parses n x

end PrefixQueryBuilderSurface

section TreeMCSPPrefixSerializerSurface

open Pnp4.Frontier.ContractExpansion

def check_zeroPrefixQueryValue
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    PrefixBitVec (treeMCSPPrefixM codec n) :=
  zeroPrefixQueryValue codec n x

theorem check_parse_zeroPrefixQueryValue
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    parseTreeMCSPPrefixInput threshold codec (zeroPrefixQueryValue codec n x) =
      some (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
        (zeroPrefixFields codec n x)) :=
  parse_zeroPrefixQueryValue codec n x

theorem check_zeroPrefixQueryValue_parses
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    ∃ input : PrefixInput
        (Frontier.treeMCSPSearchProblem threshold
          (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n),
      parseTreeMCSPPrefixInput threshold codec (zeroPrefixQueryValue codec n x) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  zeroPrefixQueryValue_parses codec n x

end TreeMCSPPrefixSerializerSurface

section TreeMCSPPrefixQueryCircuitsSurface

open Pnp4.Frontier.ContractExpansion

def check_zeroPrefixQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  zeroPrefixQueryBitCircuit codec n j

theorem check_eval_zeroPrefixQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (zeroPrefixQueryBitCircuit codec n j) x =
      zeroPrefixQueryValue codec n x j :=
  eval_zeroPrefixQueryBitCircuit codec n x j

theorem check_size_zeroPrefixQueryBitCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (zeroPrefixQueryBitCircuit codec n j) ≤ 2 :=
  size_zeroPrefixQueryBitCircuit_le codec n j

end TreeMCSPPrefixQueryCircuitsSurface

section TreeMCSPPrefixStateQueryCircuitsSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 4 surface: the prefix-state `(i, p)` query string parses back to a
prefix-input about `x` at target length `n`. -/
theorem check_prefixStateQueryValue_parses
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i) :
    ∃ input : PrefixInput
        (Frontier.treeMCSPSearchProblem threshold
          (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n),
      parseTreeMCSPPrefixInput threshold codec (prefixStateQueryValue codec n i hi x p) = some input
        ∧ input.n = n
        ∧ HEq input.x x :=
  prefixStateQueryValue_parses codec n i hi x p

/-- Block 4 surface: the bundle-shape per-bit query circuit, over
`tableLen n + i` inputs (real instance bits ++ prior bundle outputs). -/
def check_prefixStateQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n + i) :=
  prefixStateQueryBitCircuit codec n i hi j

/-- Block 4 surface: evaluating the per-bit circuit on `Fin.append x p` reproduces
the canonical prefix-state query bit. -/
theorem check_eval_prefixStateQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (prefixStateQueryBitCircuit codec n i hi j) (Fin.append x p) =
      prefixStateQueryValue codec n i hi x p j :=
  eval_prefixStateQueryBitCircuit codec n i hi x p j

/-- Block 4 surface: uniform per-bit size bound (`≤ 2`), independent of `i`. -/
theorem check_size_prefixStateQueryBitCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.size (prefixStateQueryBitCircuit codec n i hi j) ≤ 2 :=
  size_prefixStateQueryBitCircuit_le codec n i hi j

end TreeMCSPPrefixStateQueryCircuitsSurface

section TreeMCSPGreedyBundleStepSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 5 surface: the one-step shared-bundle greedy extension. -/
def check_greedyBundleStep
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i) :
    Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) (i + 1) :=
  greedyBundleStep codec n i hi dec B

/-- Block 5 surface: the step is additive in gate count (prior bundle shared). -/
theorem check_gates_greedyBundleStep
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i) :
    (greedyBundleStep codec n i hi dec B).gates
      = B.gates + (greedyStepHead codec n i hi dec).gates :=
  gates_greedyBundleStep codec n i hi dec B

/-- Block 5 surface: one greedy step adds at most `size dec + 2·M(n)`. -/
theorem check_size_greedyStepHead_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.size (greedyStepHead codec n i hi dec)
      ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n :=
  size_greedyStepHead_le codec n i hi dec

/-- Block 5 surface: prior outputs preserved by the step. -/
theorem check_evalOutput_greedyBundleStep_old
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleStep codec n i hi dec B).evalOutput (Fin.castAdd 1 o) x
      = B.evalOutput o x :=
  evalOutput_greedyBundleStep_old codec n i hi dec B o x

/-- Block 5 surface: the new bit is the decider run on the prefix-state `(i, p)`
query, `p` the prior bundle outputs on `x`. -/
theorem check_evalOutput_greedyBundleStep_new
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (B : Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleStep codec n i hi dec B).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n i hi x (fun k => B.evalOutput k x)) :=
  evalOutput_greedyBundleStep_new codec n i hi dec B x

end TreeMCSPGreedyBundleStepSurface

section TreeMCSPGreedyBundleFoldSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 6 surface: the recursive shared-bundle greedy fold of `i` bits. -/
def check_greedyBundleUpTo
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Nat)
    (hi : i ≤ codec.witnessBits n) :
    Pnp3.ComplexityInterfaces.DagCircuit.DagBundle (Pnp3.Models.Partial.tableLen n) i :=
  greedyBundleUpTo codec n dec i hi

/-- Block 6 surface (headline): the fold of `i` greedy bits has at most
`i · (size dec + 2·M(n))` gates — linear in `i`, the Option ① size payoff. -/
theorem check_gates_greedyBundleUpTo_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Nat)
    (hi : i ≤ codec.witnessBits n) :
    (greedyBundleUpTo codec n dec i hi).gates
      ≤ i * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) :=
  gates_greedyBundleUpTo_le codec n dec i hi

/-- Block 6 surface: old greedy bits preserved across the fold. -/
theorem check_evalOutput_greedyBundleUpTo_old
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (o : Fin i)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.castAdd 1 o) x
      = (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput o x :=
  evalOutput_greedyBundleUpTo_old codec n i dec hi o x

/-- Block 6 surface: the newest greedy bit = decider run on the prefix-state
`(i, p)` query, `p` the previous fold's outputs on `x`. -/
theorem check_evalOutput_greedyBundleUpTo_new
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (greedyBundleUpTo codec n dec (i + 1) hi).evalOutput (Fin.natAdd i (0 : Fin 1)) x
      = C_DAG.eval dec
          (prefixStateQueryValue codec n i (Nat.le_of_succ_le hi) x
            (fun k => (greedyBundleUpTo codec n dec i (Nat.le_of_succ_le hi)).evalOutput k x)) :=
  evalOutput_greedyBundleUpTo_new codec n i dec hi x

end TreeMCSPGreedyBundleFoldSurface

section TreeMCSPGreedyOutputCircuitsSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 7 surface: per-witness-bit output circuit over the instance bits. -/
def check_greedyOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  greedyOutputCircuit codec n dec i

/-- Block 7 surface: the `i`-th output circuit computes the `i`-th greedy bit. -/
theorem check_eval_greedyOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    C_DAG.eval (greedyOutputCircuit codec n dec i) x
      = (fullGreedyBundle codec n dec).evalOutput i x :=
  eval_greedyOutputCircuit codec n dec i x

/-- Block 7 surface (headline): uniform size bound on every output circuit,
independent of `i`. -/
theorem check_size_greedyOutputCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.size (greedyOutputCircuit codec n dec i)
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) + 1 :=
  size_greedyOutputCircuit_le codec n dec i

end TreeMCSPGreedyOutputCircuitsSurface

section PrefixExtendableSplitSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 7.5 surface: `PrefixExtendableInput` is `WitnessPrefixExtendable` on the
parsed `(n, x, i, p)` data. -/
theorem check_prefixExtendableInput_iff_witnessPrefixExtendable
    {problem : Frontier.SearchMCSPCompressionProblem} {m : Nat} (input : PrefixInput problem m) :
    PrefixExtendableInput input ↔
      WitnessPrefixExtendable input.n input.x input.prefixLength_le input.p :=
  prefixExtendableInput_iff_witnessPrefixExtendable input

/-- Block 7.5 surface: the greedy split — an extendable prefix has an extendable
next-bit extension. -/
theorem check_witnessPrefixExtendable_split
    {problem : Frontier.SearchMCSPCompressionProblem}
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p true)
      ∨ WitnessPrefixExtendable n x hi' (Fin.snoc p false) :=
  witnessPrefixExtendable_split n x hi' p hp

/-- Block 7.5 surface: the reject branch (false). -/
theorem check_witnessPrefixExtendable_snoc_false_of_not_true
    {problem : Frontier.SearchMCSPCompressionProblem}
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p)
    (hnt : ¬ WitnessPrefixExtendable n x hi' (Fin.snoc p true)) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p false) :=
  witnessPrefixExtendable_snoc_false_of_not_true n x hi' p hp hnt

/-- Block 7.5 surface: the reject branch (true). -/
theorem check_witnessPrefixExtendable_snoc_true_of_not_false
    {problem : Frontier.SearchMCSPCompressionProblem}
    (n : Nat) (x : PrefixBitVec (problem.instanceBits n))
    {i : Nat} (hi' : i + 1 ≤ problem.witnessBits n) (p : PrefixBitVec i)
    (hp : WitnessPrefixExtendable n x (Nat.le_of_succ_le hi') p)
    (hnf : ¬ WitnessPrefixExtendable n x hi' (Fin.snoc p false)) :
    WitnessPrefixExtendable n x hi' (Fin.snoc p true) :=
  witnessPrefixExtendable_snoc_true_of_not_false n x hi' p hp hnf

end PrefixExtendableSplitSurface

section TreeMCSPGreedyExtendableSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 8a surface: the greedy prefix of length `i` (the bundle outputs on `x`). -/
def check_greedyPrefix
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (i : Nat) (hi : i ≤ codec.witnessBits n) :
    PrefixBitVec i :=
  greedyPrefix codec n dec x i hi

/-- Block 8a surface (headline): on a promise instance, with a correct next-bit
decider, the greedy prefix of every length is extendable to a valid witness. -/
theorem check_greedyPrefix_extendable
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec)
    (i : Nat) (hi : i ≤ codec.witnessBits n) :
    WitnessPrefixExtendable (problem := treeProblem codec) n x hi
      (greedyPrefix codec n dec x i hi) :=
  greedyPrefix_extendable codec n dec x hpromise hdec i hi

/-- Block 8a surface: the true-extension query bit equals the encoded `p ++ true`
prefix-state query bit (the alignment that makes `CorrectNextBitDecider`
dischargeable from an ordinary prefix-extension decider). -/
theorem check_eval_prefixTrueExtensionQueryBitCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (p : PrefixBitVec i)
    (j : Fin (treeMCSPPrefixM codec n)) :
    C_DAG.eval (prefixTrueExtensionQueryBitCircuit codec n i hi j) (Fin.append x p)
      = prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true) j :=
  eval_prefixTrueExtensionQueryBitCircuit codec n i hi x p j

/-- Block 8a surface: one true-extension greedy step adds at most `size dec + 2·M(n)`
gates (feasibility for the corrected greedy). -/
theorem check_size_greedyTrueStepHead_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n i : Nat)
    (hi : i + 1 ≤ codec.witnessBits n)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) :
    C_DAG.size (greedyTrueStepHead codec n i hi dec)
      ≤ C_DAG.size dec + 2 * treeMCSPPrefixM codec n :=
  size_greedyTrueStepHead_le codec n i hi dec

end TreeMCSPGreedyExtendableSurface

section TreeMCSPGreedyTrueOutputCircuitsSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 7′ surface: the correctness-bearing per-witness-bit output circuit. -/
def check_greedyTrueOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.Family (Pnp3.Models.Partial.tableLen n) :=
  greedyTrueOutputCircuit codec n dec i

/-- Block 7′ surface: the `i`-th true-greedy output circuit computes the `i`-th
true-greedy bit. -/
theorem check_eval_greedyTrueOutputCircuit
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    C_DAG.eval (greedyTrueOutputCircuit codec n dec i) x
      = (fullGreedyTrueBundle codec n dec).evalOutput i x :=
  eval_greedyTrueOutputCircuit codec n dec i x

/-- Block 7′ surface (headline): uniform size bound on every true-greedy output
circuit, independent of `i`. -/
theorem check_size_greedyTrueOutputCircuit_le
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (i : Fin (codec.witnessBits n)) :
    C_DAG.size (greedyTrueOutputCircuit codec n dec i)
      ≤ codec.witnessBits n * (C_DAG.size dec + 2 * treeMCSPPrefixM codec n) + 1 :=
  size_greedyTrueOutputCircuit_le codec n dec i

end TreeMCSPGreedyTrueOutputCircuitsSurface

section TreeMCSPDeciderCorrectSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 8b surface: a decider for the prefix-extension language is a correct
next-bit decider (discharges the Block 8a hypothesis). -/
theorem check_correctNextBitDecider_of_decidesLanguage
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hdec : DecidesPrefixExtensionLanguage codec n dec) :
    CorrectNextBitDecider codec n x dec :=
  correctNextBitDecider_of_decidesLanguage codec n dec x hdec

end TreeMCSPDeciderCorrectSurface

section TreeMCSPGreedySolvesSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 8c surface: the full true-greedy prefix is a solving witness. -/
theorem check_greedyPrefix_solves
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    (treeProblem codec).relation n x
      (greedyPrefix codec n dec x (codec.witnessBits n) (Nat.le_refl _)) :=
  greedyPrefix_solves codec n dec x hpromise hdec

/-- Block 8c surface (headline): the joint output of the true-greedy output circuits
satisfies the search relation. -/
theorem check_greedyTrueOutputCircuit_solves
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpromise : (treeProblem codec).promise n x)
    (hdec : CorrectNextBitDecider codec n x dec) :
    (treeProblem codec).relation n x
      (Frontier.searchSolverOutput (problem := treeProblem codec) (greedyTrueOutputCircuit codec n dec) x) :=
  greedyTrueOutputCircuit_solves codec n dec x hpromise hdec

end TreeMCSPGreedySolvesSurface

section TreeMCSPBoundedSolverSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9 surface: a language-correct, size-bounded prefix-extension decider
family assembles into a `BoundedSearchSolver` for the tree-MCSP search problem. -/
def check_boundedSearchSolver_of_deciderFamily
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (dec : ∀ n, C_DAG.Family (treeMCSPPrefixM codec n))
    (decSizeBound : Nat → Nat)
    (hlang : ∀ n, DecidesPrefixExtensionLanguage codec n (dec n))
    (hsize : ∀ n, C_DAG.size (dec n) ≤ decSizeBound n) :
    Frontier.BoundedSearchSolver (treeProblem codec) C_DAG
      (boundedSolverSizeBound codec decSizeBound) :=
  boundedSearchSolver_of_deciderFamily codec dec decSizeBound hlang hsize

end TreeMCSPBoundedSolverSurface

section BoundedSolverFromPpolySurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9b surface: if the prefix-extension language is in `PpolyDAG`, a
`BoundedSearchSolver` with the extracted size schedule exists. -/
theorem check_boundedSearchSolver_of_PpolyDAG_prefixExtension
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hPpoly : Pnp3.ComplexityInterfaces.PpolyDAG
      (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    ∃ c : Nat,
      Nonempty
        (Frontier.BoundedSearchSolver (treeProblem codec) C_DAG
          (fun n =>
            codec.witnessBits n *
                ((treeMCSPPrefixM codec n) ^ c + c + 2 * treeMCSPPrefixM codec n)
              + 1)) :=
  boundedSearchSolver_of_PpolyDAG_prefixExtension codec hPpoly

end BoundedSolverFromPpolySurface

section NoSolverContrapositiveSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9c surface: if no bounded solver exists at any extracted schedule, the
prefix-extension language is not in `PpolyDAG`. -/
theorem check_not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hNo : NoExtractedScheduleSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)) :=
  not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver codec hNo

end NoSolverContrapositiveSurface

section ExtractedScheduleGrowthSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9d surface: `BoundedSearchSolver` monotonicity in its size schedule. -/
theorem check_nonempty_boundedSearchSolver_mono_sizeBound
    {problem : Frontier.SearchMCSPCompressionProblem} {C : AlgorithmsToLowerBounds.CircuitFamilyClass}
    {small big : Nat → Nat}
    (h : Nonempty (Frontier.BoundedSearchSolver problem C small))
    (hle : ∀ n, small n ≤ big n) :
    Nonempty (Frontier.BoundedSearchSolver problem C big) :=
  nonempty_boundedSearchSolver_mono_sizeBound h hle

/-- Block 9d surface (headline): under explicit polynomial growth assumptions, no
polynomial-size bounded search solver implies the prefix-extension language is not in
`PpolyDAG`. -/
theorem check_not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)) :=
  not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly

end ExtractedScheduleGrowthSurface

section ConditionalVerifiedSourceSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 9e surface: under explicit growth assumptions, the open polynomial weak
lower bound, and an explicit `NP`-membership hypothesis, assemble a
`VerifiedNPDAGLowerBoundSource`. -/
noncomputable def check_verifiedSource_of_noPolynomialBoundedSearchSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNP :
      Pnp3.ComplexityInterfaces.NP
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly hNP

/-- Block 9e surface (headline): the same three explicit hypotheses yield the
conditional `NP ⊄ PpolyDAG` separation. -/
theorem check_NP_not_subset_PpolyDAG_of_noPolynomialBoundedSearchSolver
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec)
    (hNP :
      Pnp3.ComplexityInterfaces.NP
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_noPolynomialBoundedSearchSolver codec hGrowth hNoPoly hNP

end ConditionalVerifiedSourceSurface

section WitnessGrowthReductionSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 10a surface: `bitLength m ≤ m`. -/
theorem check_bitLength_le_self (m : Nat) : bitLength m ≤ m :=
  bitLength_le_self m

/-- Block 10a surface: the concrete ambient length is poly-bounded in the
truth-table length given only the witness-length assumption. -/
theorem check_polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hW : PolyBoundedInTable codec.witnessBits) :
    PolyBoundedInTable (treeMCSPPrefixM codec) :=
  polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly codec hW

/-- Block 10a surface (headline): the full extraction growth assumptions follow
from the single witness-length assumption. -/
theorem check_treeMCSPExtractionGrowthAssumptions_of_witnessPoly
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (hW : PolyBoundedInTable codec.witnessBits) :
    TreeMCSPExtractionGrowthAssumptions codec :=
  treeMCSPExtractionGrowthAssumptions_of_witnessPoly codec hW

/-- Block 10a surface: the minimal `PolynomialWitnessCodec` interface yields the
extraction growth assumptions. -/
theorem check_PolynomialWitnessCodec_toGrowthAssumptions
    {threshold : Nat → Nat}
    (P : PolynomialWitnessCodec threshold) :
    TreeMCSPExtractionGrowthAssumptions P.codec :=
  P.toGrowthAssumptions

end WitnessGrowthReductionSurface

section PrefixExtensionNPWitnessSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 11a surface (headline): a concrete TM-witness package yields NP-membership
of the prefix-extension language. -/
theorem check_prefixExtensionLanguage_in_NP_of_witness
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    (W : PrefixExtensionNPWitness parser) :
    Pnp3.ComplexityInterfaces.NP (PrefixExtensionLanguage parser) :=
  prefixExtensionLanguage_in_NP_of_witness parser W

end PrefixExtensionNPWitnessSurface

section ExplicitConditionalSourceSurface

open Pnp4.Frontier.ContractExpansion

/-- Capstone surface: the three explicit interfaces (growth-witness codec, no-poly
solver, NP TM-witness) assemble a `VerifiedNPDAGLowerBoundSource`. -/
noncomputable def check_verifiedSource_of_explicit_interfaces
    {threshold : Nat → Nat}
    (wcodec : PolynomialWitnessCodec threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver wcodec.codec)
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold wcodec.codec)) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_explicit_interfaces wcodec hNoPoly hNPWit

/-- Capstone surface (headline): the three explicit interfaces yield the conditional
`NP ⊄ PpolyDAG` separation. -/
theorem check_NP_not_subset_PpolyDAG_of_explicit_interfaces
    {threshold : Nat → Nat}
    (wcodec : PolynomialWitnessCodec threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver wcodec.codec)
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold wcodec.codec)) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_explicit_interfaces wcodec hNoPoly hNPWit

end ExplicitConditionalSourceSurface

section ConcreteCodecGapSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12a surface: the fixed-width packing round-trip (read-back recovers the
list plus a `false` pad). -/
theorem check_ofFn_listToFixedBitVec
    (l : List Bool) (L : Nat) (hL : l.length ≤ L) :
    List.ofFn (listToFixedBitVec l L) = l ++ List.replicate (L - l.length) false :=
  ofFn_listToFixedBitVec l L hL

/-- Block 12a surface (headline): a self-delimiting circuit code with a width bound
yields a concrete `TreeCircuitWitnessCodec` (the proved padding reduction). -/
def check_SelfDelimitingCircuitCode_toCodec
    {threshold : Nat → Nat}
    (S : SelfDelimitingCircuitCode threshold) :
    Frontier.TreeCircuitWitnessCodec threshold :=
  S.toCodec

end ConcreteCodecGapSurface

section CircuitTreeBridgeSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12b surface: the bridge is a left inverse. -/
theorem check_fromTree_toTree {n : Nat} (c : Pnp3.Models.Circuit n) :
    fromTree (toTree c) = c :=
  fromTree_toTree c

/-- Block 12b surface: the bridge preserves gate count. -/
theorem check_size_toTree {n : Nat} (c : Pnp3.Models.Circuit n) :
    (toTree c).size = Pnp3.Models.Circuit.size c :=
  size_toTree c

/-- Block 12b surface (headline): the native `Circuit` encoder/decoder round-trips
(for all `n`, including `n = 0`). -/
theorem check_decodeCircuit_encodeCircuit (n : Nat) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : Pnp3.Models.Circuit n)
    (d : Nat) (h_d : Pnp3.Models.Circuit.size c ≤ d) (rest : List Bool) :
    decodeCircuit n width d (encodeCircuit width h_width c ++ rest)
      = some (c, rest) :=
  decodeCircuit_encodeCircuit n width h_width c d h_d rest

end CircuitTreeBridgeSurface

section CircuitEncodingLengthSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12c surface (headline): the native `Circuit` encoding has length at most
`(width + 4) · size c`. -/
theorem check_length_encodeCircuit_le {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) :
    (encodeCircuit width h_width c).length ≤ (width + 4) * Pnp3.Models.Circuit.size c :=
  length_encodeCircuit_le width h_width c

end CircuitEncodingLengthSurface

section CircuitDecodeDepthFreeSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12d surface: the native encoding-length lower bound. -/
theorem check_length_encodeCircuit_ge {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) :
    3 * Pnp3.Models.Circuit.size c ≤ (encodeCircuit width h_width c).length :=
  length_encodeCircuit_ge width h_width c

/-- Block 12d surface (headline): the depth-free decoder round-trips with no
`size ≤ d` side condition (for all `n`, including `n = 0`). -/
theorem check_decodeCircuitFull_encodeCircuit (n : Nat) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : Pnp3.Models.Circuit n) (rest : List Bool) :
    decodeCircuitFull n width (encodeCircuit width h_width c ++ rest)
      = some (c, rest) :=
  decodeCircuitFull_encodeCircuit n width h_width c rest

end CircuitDecodeDepthFreeSurface

section ConcreteTreeCodecSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12e surface (headline): a concrete `TreeCircuitWitnessCodec` exists for
every `threshold`. -/
def check_treeCircuitWitnessCodec (threshold : Nat → Nat) :
    Frontier.TreeCircuitWitnessCodec threshold :=
  treeCircuitWitnessCodec threshold

/-- Block 12e surface: under the single threshold-growth premise, the concrete codec
packages as a `PolynomialWitnessCodec`. -/
def check_treePolynomialWitnessCodec (threshold : Nat → Nat)
    (hT : PolyBoundedInTable threshold) :
    PolynomialWitnessCodec threshold :=
  treePolynomialWitnessCodec threshold hT

end ConcreteTreeCodecSurface

section ConcreteTreeCodecSourceSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 12f surface: the concrete-codec verified source from the three explicit
interfaces (threshold growth, no-poly solver, NP TM-witness). -/
noncomputable def check_verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
    (threshold : Nat → Nat)
    (hThresholdPoly : PolyBoundedInTable threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold (treeCircuitWitnessCodec threshold))) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver
    threshold hThresholdPoly hNoPoly hNPWit

/-- Block 12f surface (headline): the concrete-codec conditional `NP ⊄ PpolyDAG`
separation. -/
theorem check_NP_not_subset_PpolyDAG_of_treeCodec_interfaces
    (threshold : Nat → Nat)
    (hThresholdPoly : PolyBoundedInTable threshold)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec threshold))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser threshold (treeCircuitWitnessCodec threshold))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_treeCodec_interfaces
    threshold hThresholdPoly hNoPoly hNPWit

end ConcreteTreeCodecSourceSurface

section ThresholdGrowthSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 13a surface: the quadratic threshold is polynomially bounded in the
truth-table length. -/
theorem check_polyBoundedInTable_thresholdQuadratic :
    PolyBoundedInTable thresholdQuadratic :=
  polyBoundedInTable_thresholdQuadratic

/-- Block 13a surface (headline): every fixed polynomial threshold `nᵏ + k` is
polynomially bounded in the truth-table length. -/
theorem check_polyBoundedInTable_thresholdPoly (k : Nat) :
    PolyBoundedInTable (thresholdPoly k) :=
  polyBoundedInTable_thresholdPoly k

end ThresholdGrowthSurface

section ConsolidatedTreeSeparationSurface

open Pnp4.Frontier.ContractExpansion

/-- Block 13b surface: at a concrete polynomial threshold, the verified source rests
on only the two genuinely-hard inputs (lower bound + NP witness). -/
noncomputable def check_verifiedSource_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser (thresholdPoly k) (treeCircuitWitnessCodec (thresholdPoly k)))) :
    AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource :=
  verifiedSource_treePoly k hNoPoly hNPWit

/-- Block 13b surface (headline): the consolidated conditional `NP ⊄ PpolyDAG` at a
concrete polynomial threshold. -/
theorem check_NP_not_subset_PpolyDAG_treePoly
    (k : Nat)
    (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
    (hNPWit : PrefixExtensionNPWitness
        (treeMCSPConcretePrefixParser (thresholdPoly k) (treeCircuitWitnessCodec (thresholdPoly k)))) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_treePoly k hNoPoly hNPWit

end ConsolidatedTreeSeparationSurface

section TreeMCSPZeroPrefixBuilderSurface

open Pnp4.Frontier.ContractExpansion

def check_zeroPrefixQueryCircuitBuilder
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold) :
    QueryCircuitBuilder
      (fun n => Pnp3.Models.Partial.tableLen n)
      (fun n => treeMCSPPrefixM codec n) :=
  zeroPrefixQueryCircuitBuilder codec

def check_treeMCSPZeroPrefixQueryBuilder
    (threshold : Nat → Nat)
    (codec : Frontier.TreeCircuitWitnessCodec threshold) :
    PrefixQueryBuilder
      (Frontier.treeMCSPSearchProblem threshold
        (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPConcretePrefixParser threshold codec) :=
  treeMCSPZeroPrefixQueryBuilder threshold codec

theorem check_treeMCSPZeroPrefixQueryBuilder_queryValue
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n)) :
    (treeMCSPZeroPrefixQueryBuilder threshold codec).queryValue n x =
      zeroPrefixQueryValue codec n x :=
  treeMCSPZeroPrefixQueryBuilder_queryValue codec n x

end TreeMCSPZeroPrefixBuilderSurface

section NaiveGreedySizeSpikeSurface

open Pnp4.Frontier.ContractExpansion
open Pnp3.ComplexityInterfaces (DagCircuit)

theorem check_geometric_lower_bound (f : Nat → Nat)
    (hstep : ∀ i, (∑ k ∈ Finset.range (i + 1), f k) ≤ f (i + 1)) (i : Nat) :
    f 0 * 2 ^ i ≤ f (i + 1) :=
  geometric_lower_bound f hstep i

theorem check_composeDeciderWithQuery_eq_substInputs
    {inputBits queryBits : Nat}
    (decider : C_DAG.Family queryBits)
    (queryBit : Fin queryBits → C_DAG.Family inputBits) :
    composeDeciderWithQuery decider queryBit
      = DagCircuit.substInputs decider queryBit :=
  composeDeciderWithQuery_eq_substInputs decider queryBit

theorem check_naiveGreedyModel_size_ge (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) :
    seed.gates * 2 ^ i ≤ DagCircuit.size (naiveGreedyModel m seed decider (i + 1)) :=
  naiveGreedyModel_size_ge m seed decider i

theorem check_naiveGreedyModel_size_ge_pow (m : Nat) (seed : DagCircuit m)
    (decider : (q : Nat) → DagCircuit q) (i : Nat) (hseed : 1 ≤ seed.gates) :
    2 ^ i ≤ DagCircuit.size (naiveGreedyModel m seed decider (i + 1)) :=
  naiveGreedyModel_size_ge_pow m seed decider i hseed

theorem check_pow_le_of_linear_witnessBits (W n c : Nat) (h : W ≤ c * n + c) :
    2 ^ W ≤ (2 ^ n) ^ c * 2 ^ c :=
  pow_le_of_linear_witnessBits W n c h

theorem check_pow_quadratic_gt_poly (n c : Nat) (hn : 0 < n) (hc : c < n) :
    (2 ^ n) ^ c < 2 ^ (n * n) :=
  pow_quadratic_gt_poly n c hn hc

end NaiveGreedySizeSpikeSurface

section PrefixExtensionLanguageSurface

open Pnp4.Frontier.ContractExpansion

def check_PrefixParser
    (problem : Frontier.SearchMCSPCompressionProblem) : Type :=
  PrefixParser problem

def check_parsePrefixInput
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m) :
    Option (PrefixInput problem m) :=
  parsePrefixInput parser y

def check_PrefixExtendable
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m) : Prop :=
  PrefixExtendable parser y

noncomputable def check_PrefixExtensionLanguage
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Pnp3.ComplexityInterfaces.Language :=
  PrefixExtensionLanguage parser

theorem check_PrefixExtensionLanguage_rejects_malformed
    {problem : Frontier.SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m)
    (hparse : parsePrefixInput parser y = none) :
    PrefixExtensionLanguage parser m y = false :=
  PrefixExtensionLanguage_rejects_malformed parser y hparse


section PrefixExtensionLanguageRuntimeSurface

open Pnp4.Frontier.ContractExpansion

def check_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) : Nat :=
  treeMCSPPrefixAmbientLength overhead witnessBits padBits n

theorem check_tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n :=
  tableLen_le_treeMCSPPrefixAmbientLength overhead witnessBits padBits n

def check_PolynomiallyBoundedInAmbient
    (M f : Nat → Nat) : Prop :=
  PolynomiallyBoundedInAmbient M f

def check_RuntimeAwareTreeCircuitCodec
    (threshold M : Nat → Nat) : Type :=
  RuntimeAwareTreeCircuitCodec threshold M

def check_RuntimeAwarePrefixParser
    (problem : Frontier.SearchMCSPCompressionProblem)
    (M : Nat → Nat) : Type :=
  RuntimeAwarePrefixParser problem M

def check_TreeMCSPPrefixRuntimeBudget
    (threshold M : Nat → Nat)
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (parser : PrefixParser (Frontier.treeMCSPSearchProblem threshold
      (Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec))) : Type :=
  TreeMCSPPrefixRuntimeBudget threshold M codec parser

end PrefixExtensionLanguageRuntimeSurface

end PrefixExtensionLanguageSurface

def check_NotInClass :
    ∀ (C : CircuitFamilyClass) (L : BitVecLanguage),
      NotInClass C L → NotInClass C L :=
  fun _ _ h => h

def check_maskBit_true (x : Bool) :
    maskBit true x = x :=
  maskBit_true x

def check_maskBit_false (x : Bool) :
    maskBit false x = false :=
  maskBit_false x

def check_maskVec_apply
    {n : Nat} (keep x : AlgorithmsToLowerBounds.BitVec n) (i : Fin n) :
    maskVec keep x i = maskBit (keep i) (x i) :=
  maskVec_apply keep x i

def check_closedUnderInputMasking_eval
    {C : CircuitFamilyClass}
    (closed : ClosedUnderInputMasking C)
    {n : Nat}
    (keep x : AlgorithmsToLowerBounds.BitVec n)
    (c : C.Family n) :
    C.eval (closed.maskCircuit keep c) x = C.eval c (maskVec keep x) :=
  closed.eval_maskCircuit keep c x

def check_closedUnderInputMasking_size
    {C : CircuitFamilyClass}
    (closed : ClosedUnderInputMasking C)
    {n : Nat}
    (keep : AlgorithmsToLowerBounds.BitVec n)
    (c : C.Family n) :
    C.size (closed.maskCircuit keep c) ≤ C.size c :=
  closed.size_maskCircuit keep c

noncomputable def check_expectationProductBias
    {n : Nat}
    (bias : Rat)
    (F : AlgorithmsToLowerBounds.BitVec n → Rat) : Rat :=
  expectationProductBias bias F

theorem check_expectationProductBias_sub
    {n : Nat}
    (bias : Rat)
    (F G : AlgorithmsToLowerBounds.BitVec n → Rat) :
    expectationProductBias bias (fun x => F x - G x) =
      expectationProductBias bias F - expectationProductBias bias G :=
  expectationProductBias_sub bias F G

theorem check_expectationProductBias_le_of_pointwise_le
    {n : Nat}
    {bias bound : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (F : AlgorithmsToLowerBounds.BitVec n → Rat)
    (hF : ∀ x : AlgorithmsToLowerBounds.BitVec n, F x ≤ bound) :
    expectationProductBias bias F ≤ bound :=
  expectationProductBias_le_of_pointwise_le
    hBias_nonneg
    hBias_le_one
    F
    hF

theorem check_exists_max_bitVec_rat
    {n : Nat}
    (F : AlgorithmsToLowerBounds.BitVec n → Rat) :
    ∃ x0 : AlgorithmsToLowerBounds.BitVec n,
      ∀ x : AlgorithmsToLowerBounds.BitVec n, F x ≤ F x0 :=
  exists_max_bitVec_rat F

noncomputable def check_maskedAcceptanceAverage
    {n : Nat}
    (keepBias inputBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) : Rat :=
  maskedAcceptanceAverage keepBias inputBias A

theorem check_maskedAcceptanceAverage_eq_acceptanceProbability_mul
    {n : Nat}
    (keepBias inputBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    maskedAcceptanceAverage keepBias inputBias A =
      acceptanceProbability (keepBias * inputBias) A :=
  maskedAcceptanceAverage_eq_acceptanceProbability_mul keepBias inputBias A

def check_maskingBiasParams_derived
    (params : MaskingBiasParams) :
    Rat × Rat × Rat × Rat × Rat :=
  (params.lowSourceBias,
    params.highSourceBias,
    params.lowTargetBias,
    params.highTargetBias,
    params.keepBias)

theorem check_maskingBiasParams_keepBias_nonneg
    (params : MaskingBiasParams) :
    0 ≤ params.keepBias :=
  params.keepBias_nonneg

theorem check_maskingBiasParams_keepBias_le_one
    (params : MaskingBiasParams) :
    params.keepBias ≤ 1 :=
  params.keepBias_le_one

theorem check_maskingBiasParams_keepBias_mul_highTargetBias
    (params : MaskingBiasParams) :
    params.keepBias * params.highTargetBias = params.highSourceBias :=
  params.keepBias_mul_highTargetBias

theorem check_maskingBiasParams_keepBias_mul_lowTargetBias
    (params : MaskingBiasParams) :
    params.keepBias * params.lowTargetBias = params.lowSourceBias :=
  params.keepBias_mul_lowTargetBias

def check_maskingPushforwardFacts_type
    (n : Nat)
    (params : MaskingBiasParams) : Prop :=
  MaskingPushforwardFacts n params

theorem check_maskingPushforwardFacts_of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    MaskingPushforwardFacts n params :=
  MaskingPushforwardFacts.of_maskingBiasParams params n

noncomputable def check_maskedAcceptanceAdvantage
    {n : Nat}
    (keepBias targetLowBias targetHighBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) : Rat :=
  maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A

noncomputable def check_fixedMaskAcceptanceAdvantage
    {n : Nat}
    (keep : AlgorithmsToLowerBounds.BitVec n)
    (targetLowBias targetHighBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) : Rat :=
  fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A

theorem check_maskedAcceptanceAdvantage_eq_expectation_fixed
    {n : Nat}
    (keepBias targetLowBias targetHighBias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    maskedAcceptanceAdvantage keepBias targetLowBias targetHighBias A =
      expectationProductBias keepBias
        (fun keep =>
          fixedMaskAcceptanceAdvantage keep targetLowBias targetHighBias A) :=
  maskedAcceptanceAdvantage_eq_expectation_fixed
    keepBias
    targetLowBias
    targetHighBias
    A

theorem check_maskingPushforwardFacts_masked_advantage_eq_source
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : MaskingPushforwardFacts n params)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    maskedAcceptanceAdvantage
        params.keepBias
        params.lowTargetBias
        params.highTargetBias
        A =
      acceptanceProbability params.highSourceBias A -
        acceptanceProbability params.lowSourceBias A :=
  facts.masked_advantage_eq_source A

def check_maskAveragingContract_type
    (n : Nat)
    (keepBias : Rat) : Prop :=
  MaskAveragingContract n keepBias

theorem check_maskAveragingContract_of_valid_keepBias
    {n : Nat}
    {keepBias : Rat}
    (hKeep_nonneg : 0 ≤ keepBias)
    (hKeep_le_one : keepBias ≤ 1) :
    MaskAveragingContract n keepBias :=
  MaskAveragingContract.of_valid_keepBias hKeep_nonneg hKeep_le_one

theorem check_maskAveragingContract_of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    MaskAveragingContract n params.keepBias :=
  MaskAveragingContract.of_maskingBiasParams params n

def check_coinMaskingTranslationFacts_type
    (params : MaskingBiasParams)
    (n : Nat) : Prop :=
  CoinMaskingTranslationFacts params n

theorem check_coinMaskingTranslationFacts_of_maskingBiasParams
    (params : MaskingBiasParams)
    (n : Nat) :
    CoinMaskingTranslationFacts params n :=
  CoinMaskingTranslationFacts.of_maskingBiasParams params n

def check_coinMaskingClassTranslationFacts_type
    (C : CircuitFamilyClass)
    (params : MaskingBiasParams)
    (n : Nat) : Type :=
  CoinMaskingClassTranslationFacts C params n

theorem check_coinMaskingTranslationFacts_exists_mask_with_source_advantage
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : CoinMaskingTranslationFacts params n)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool)
    {adv : Rat}
    (hAdv :
      adv ≤
        acceptanceProbability params.highSourceBias A -
          acceptanceProbability params.lowSourceBias A) :
    ∃ keep : AlgorithmsToLowerBounds.BitVec n,
      adv ≤
        fixedMaskAcceptanceAdvantage
          keep
          params.lowTargetBias
          params.highTargetBias
          A :=
  facts.exists_mask_with_source_advantage A hAdv

noncomputable def check_bestMaskForCircuit
    {C : CircuitFamilyClass}
    {n : Nat}
    (targetLowBias targetHighBias : Rat)
    (c : C.Family n) :
    AlgorithmsToLowerBounds.BitVec n :=
  bestMaskForCircuit targetLowBias targetHighBias c

theorem check_bestMaskForCircuit_max
    {C : CircuitFamilyClass}
    {n : Nat}
    (targetLowBias targetHighBias : Rat)
    (c : C.Family n) :
    ∀ keep : AlgorithmsToLowerBounds.BitVec n,
      fixedMaskAcceptanceAdvantage
        keep
        targetLowBias
        targetHighBias
        (fun x => C.eval c x) ≤
      fixedMaskAcceptanceAdvantage
        (bestMaskForCircuit targetLowBias targetHighBias c)
        targetLowBias
        targetHighBias
        (fun x => C.eval c x) :=
  bestMaskForCircuit_max targetLowBias targetHighBias c

theorem check_source_advantage_le_bestMask_fixed_advantage
    {C : CircuitFamilyClass}
    {n : Nat}
    {params : MaskingBiasParams}
    (facts : CoinMaskingTranslationFacts params n)
    (c : C.Family n)
    {adv : Rat}
    (hSourceAdv :
      adv ≤
        acceptanceProbability params.highSourceBias (fun x => C.eval c x) -
          acceptanceProbability params.lowSourceBias (fun x => C.eval c x)) :
    adv ≤
      fixedMaskAcceptanceAdvantage
        (bestMaskForCircuit params.lowTargetBias params.highTargetBias c)
        params.lowTargetBias
        params.highTargetBias
        (fun x => C.eval c x) :=
  source_advantage_le_bestMask_fixed_advantage facts c hSourceAdv

def check_coinMaskingTranslationSetup_type
    (source : CoinDistinguisherFamily)
    (target : HalfVsFairTruthTableCoinHardness) : Type :=
  CoinMaskingTranslationSetup source target

noncomputable def check_coinTranslationPreservesClass_of_maskingSetup
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {target : HalfVsFairTruthTableCoinHardness}
    (closed : ClosedUnderInputMasking C)
    (setup : CoinMaskingTranslationSetup source target)
    (facts :
      ∀ n : Nat,
        CoinMaskingTranslationFacts (setup.params n) (source.sampleBits n)) :
    CoinTranslationPreservesClass C source target :=
  coinTranslationPreservesClass_of_maskingSetup closed setup facts

def check_AC0pFamilyModelWithMasking_to_model
    (model : AC0pFamilyModelWithMasking) :
    AC0pFamilyModel :=
  model.toAC0pFamilyModel

def check_AC0pFamilyModelWithMasking_closed
    (model : AC0pFamilyModelWithMasking)
    (p depth : Nat) :
    ClosedUnderInputMasking (model.toAC0pFamilyModel.classOf p depth) :=
  model.closed p depth

noncomputable def check_coinTranslationPreservesClass_of_maskingSetup_AC0p
    {source : CoinDistinguisherFamily}
    {target : HalfVsFairTruthTableCoinHardness}
    (model : AC0pFamilyModelWithMasking)
    (p depth : Nat)
    (setup : CoinMaskingTranslationSetup source target)
    (facts :
      ∀ n : Nat,
        CoinMaskingTranslationFacts (setup.params n) (source.sampleBits n)) :
    CoinTranslationPreservesClass
      (model.toAC0pFamilyModel.classOf p depth)
      source
      target :=
  coinTranslationPreservesClass_of_maskingSetup_AC0p
    model
    p
    depth
    setup
    facts

theorem check_false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_maskingSetup
    {hardness : HalfVsFairTruthTableCoinHardness}
    (model : AC0pFamilyModelWithMasking)
    (contract :
      AC0pHalfVsFairCoinLowerBoundContract
        model.toAC0pFamilyModel
        hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (setup :
      CoinMaskingTranslationSetup
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (maskFacts :
      ∀ m : Nat,
        CoinMaskingTranslationFacts
          (setup.params m)
          ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).sampleBits m))
    (circuit :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).Family
          (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen m),
        (model.toAC0pFamilyModel.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).size (circuit m) ≤
          sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_maskingSetup
    model
    contract
    facts
    hp
    setup
    maskFacts
    circuit
    computes
    sizeBound
    size_le
    hSize

def check_adjacentBiasToHalfVsFairMaskingSetupFacts_type
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) : Prop :=
  AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness

def check_maskingParams_of_adjacentBiasToHalfVsFair
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (setupFacts :
      AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness)
    (n : Nat) :
    MaskingBiasParams :=
  maskingParams_of_adjacentBiasToHalfVsFair setupFacts n

def check_coinMaskingTranslationSetup_of_adjacentBiasToHalfVsFair
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (setupFacts :
      AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness) :
    CoinMaskingTranslationSetup
      (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
      hardness :=
  CoinMaskingTranslationSetup.of_adjacentBiasToHalfVsFair setupFacts

theorem check_false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_adjacentMaskingSetup
    {hardness : HalfVsFairTruthTableCoinHardness}
    (model : AC0pFamilyModelWithMasking)
    (contract :
      AC0pHalfVsFairCoinLowerBoundContract
        model.toAC0pFamilyModel
        hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (setupFacts :
      AdjacentBiasToHalfVsFairMaskingSetupFacts facts hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (circuit :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).Family
          (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen m),
        (model.toAC0pFamilyModel.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.toAC0pFamilyModel.classOf p depth).size (circuit m) ≤
          sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_adjacentMaskingSetup
    model
    contract
    facts
    setupFacts
    hp
    circuit
    computes
    sizeBound
    size_le
    hSize

def check_quasiPolyLower_superPolynomialGrowth :
    SuperPolynomialGrowth QuasiPolyLower :=
  quasiPolyLower_superPolynomialGrowth

def check_not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : SizeLowerBound C L lower)
    (hGrowth : SuperPolynomialGrowth lower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound hLB hGrowth

def check_not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    (hLB : SizeLowerBound C L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound hLB

def check_not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {lower : Nat → Nat}
    (hLB : EventuallySizeLowerBound C L lower)
    (hGrowth : SuperPolynomialGrowth lower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound hLB hGrowth

def check_not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    (hLB : EventuallySizeLowerBound C L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily C L :=
  not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound hLB

def check_eventuallySizeLowerBound_weaken
    {C : CircuitFamilyClass}
    {L : BitVecLanguage}
    {strong weak : Nat → Nat}
    (hLB : EventuallySizeLowerBound C L strong)
    (hDom : EventuallyDominates strong weak) :
    EventuallySizeLowerBound C L weak :=
  EventuallySizeLowerBound.weaken hLB hDom

def check_not_depth_d_AC0p_of_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (L : BitVecLanguage)
    (hLB : SizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily (model.classOf p depth) L :=
  not_depth_d_AC0p_of_quasiPoly_lowerBound model p depth L hLB

def check_not_in_AC0p_of_depthwise_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage)
    (hLB : ∀ depth : Nat,
      SizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ InAC0p model p L :=
  not_in_AC0p_of_depthwise_quasiPoly_lowerBound model p L hLB

def check_not_in_AC0p_from_quasiPolynomial_contract
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pQuasiPolynomialLowerBoundContract model L)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p L :=
  not_in_AC0p_from_quasiPolynomial_contract contract p hp

def check_not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p depth : Nat)
    (L : BitVecLanguage)
    (hLB :
      EventuallySizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ HasPolynomialSizeFamily (model.classOf p depth) L :=
  not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound model p depth L hLB

def check_not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound
    (model : AC0pFamilyModel)
    (p : Nat)
    (L : BitVecLanguage)
    (hLB : ∀ depth : Nat,
      EventuallySizeLowerBound (model.classOf p depth) L QuasiPolyLower) :
    ¬ InAC0p model p L :=
  not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound model p L hLB

def check_not_in_AC0p_from_asymptotic_quasiPolynomial_contract
    {model : AC0pFamilyModel}
    {L : BitVecLanguage}
    (contract : AC0pAsymptoticQuasiPolynomialLowerBoundContract model L)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p L :=
  not_in_AC0p_from_asymptotic_quasiPolynomial_contract contract p hp

def check_treeMCSPPredicate
    (n s : Nat) (tt : TruthTable n) : Prop :=
  treeMCSPPredicate n s tt

def check_verified_source :
    VerifiedNPDAGLowerBoundSource →
      Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_verified_source

def check_verified_source_to_pne_np :
    VerifiedNPDAGLowerBoundSource →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_verified_source

def check_ac0p_restricted_source_restrictedConclusion
    (src : Frontier.AC0pRestrictedLowerBoundSource) :
    ¬ InAC0p src.model src.p src.L :=
  src.restrictedConclusion

def check_pnp4_bridge_requirement_to_pne_np :
    Frontier.PvsNPBridgeRequirement →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_pnp4_bridge_requirement

def check_restricted_source_with_dag_bridge_to_pne_np
    (restricted : Frontier.AC0pRestrictedLowerBoundSource) :
    Frontier.RestrictedToVerifiedDAGBridge restricted →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_restricted_source_and_dag_bridge restricted

def check_P_ne_NP_of_NP_not_subset_Ppoly :
    Frontier.NP_not_subset_Ppoly →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_NP_not_subset_Ppoly

def check_searchMCSPWeakLowerBound_to_np_not_subset
    (src : Frontier.SearchMCSPWeakLowerBound) :
    Frontier.NP_not_subset_Ppoly :=
  Frontier.NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound src

def check_searchMCSPWeakLowerBound_to_pne_np
    (src : Frontier.SearchMCSPWeakLowerBound) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_searchMCSPWeakLowerBound src

def check_mainlineProgress_of_searchMCSPWeakLowerBound
    (src : Frontier.SearchMCSPWeakLowerBound) :
    Frontier.PvsNPMainlineProgress :=
  Frontier.PvsNPMainlineProgress.of_searchMCSPWeakLowerBound src

def check_mainlineProgress_to_pne_np :
    Frontier.PvsNPMainlineProgress →
      Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_mainlineProgress

def check_searchMCSPWeakCircuitTarget_noBoundedSolver
    (target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget) : Prop :=
  target.noBoundedSolver

def check_searchProblemNoBoundedSolver
    (problem : Frontier.SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) : Prop :=
  Frontier.SearchProblemNoBoundedSolver problem C sizeBound

def check_searchMCSPWeakLowerBound_of_weakCircuitLowerBound
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Frontier.SearchMCSPWeakLowerBound :=
  Frontier.SearchMCSPWeakLowerBound.of_weakCircuitLowerBound hWeak hMag

def check_weakCircuitLowerBound_to_np_not_subset
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Frontier.NP_not_subset_Ppoly :=
  Frontier.NP_not_subset_Ppoly_of_weakCircuitLowerBound hWeak hMag

def check_weakCircuitLowerBound_to_pne_np
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_weakCircuitLowerBound hWeak hMag

def check_mainlineProgress_of_weakCircuitLowerBound
    {target : Frontier.SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : Frontier.SearchMCSPWeakCircuitLowerBound target)
    (hMag : Frontier.SearchMCSPMagnificationContract target) :
    Frontier.PvsNPMainlineProgress :=
  Frontier.PvsNPMainlineProgress.of_weakCircuitLowerBound hWeak hMag

def check_treeMCSPSearchProblem
    (threshold : Nat → Nat)
    (encoding : Frontier.TreeMCSPSearchWitnessEncoding threshold) :
    Frontier.SearchMCSPCompressionProblem :=
  Frontier.treeMCSPSearchProblem threshold encoding

def check_treeCircuitWitnessCodec_verifies
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : AlgorithmsToLowerBounds.BitVec (codec.witnessBits n)) : Prop :=
  codec.verifies n tt w

def check_treeCircuitWitnessCodec_sound
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : AlgorithmsToLowerBounds.BitVec (codec.witnessBits n)) :
    codec.verifies n tt w →
      treeMCSPPredicate n (threshold n) tt :=
  codec.sound n tt w

def check_treeMCSPSearchWitnessEncoding_ofCodec
    {threshold : Nat → Nat}
    (codec : Frontier.TreeCircuitWitnessCodec threshold) :
    Frontier.TreeMCSPSearchWitnessEncoding threshold :=
  Frontier.TreeMCSPSearchWitnessEncoding.ofCodec codec

def check_treeMCSPSearchWeakLowerBoundTarget
    (threshold : Nat → Nat)
    (encoding : Frontier.TreeMCSPSearchWitnessEncoding threshold)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) :
    Frontier.SearchMCSPWeakCircuitLowerBoundTarget :=
  Frontier.treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound

def check_treeMCSPSearchSource_to_np_not_subset
    (src : Frontier.TreeMCSPSearchMagnificationSource) :
    Frontier.NP_not_subset_Ppoly :=
  Frontier.NP_not_subset_Ppoly_of_treeMCSPSearchMagnificationSource src

def check_treeMCSPSearchSource_to_pne_np
    (src : Frontier.TreeMCSPSearchMagnificationSource) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Frontier.P_ne_NP_of_treeMCSPSearchMagnificationSource src

def check_mainlineProgress_of_treeMCSPSearchSource
    (src : Frontier.TreeMCSPSearchMagnificationSource) :
    Frontier.PvsNPMainlineProgress :=
  Frontier.PvsNPMainlineProgress.of_treeMCSPSearchMagnificationSource src

def check_uniform_vs_biased_coin_instance
    (sampleBits : Nat) (ε : Rat)
    (hεpos : 0 < ε) (hεhalf : ε ≤ (1 : Rat) / 2) :
    CoinProblemInstance :=
  uniformVsBiasedCoinInstance sampleBits ε hεpos hεhalf

def check_half_vs_fair_coin_instance
    (sampleBits : Nat) (ε : Rat)
    (hεpos : 0 < ε) (hεone : ε ≤ (1 : Rat)) :
    CoinProblemInstance :=
  halfVsFairCoinInstance sampleBits ε hεpos hεone

def check_truth_table_coin_instance
    (n : Nat) (low high : Rat)
    (hlow : 0 ≤ low) (hhigh : high ≤ 1) (hgap : low < high) :
    CoinProblemInstance :=
  truthTableCoinInstance n low high hlow hhigh hgap

def check_truth_table_local_prg_image_bound
    {n : Nat}
    (prg : TruthTableLocalPRG n) :
    Nat :=
  prg.imageSizeBound

def check_one_sided_fools_of_fools
    {n : Nat}
    {prg : TruthTableLocalPRG n}
    {C : CircuitFamilyClass}
    {maxSize : Nat}
    {epsilon : Rat} :
    FoolsBoundedTruthTableClass prg C maxSize epsilon →
      OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon :=
  oneSidedFoolsBoundedTruthTableClass_of_foolsBounded

def check_class_solves_coin_problem_of_implemented_threshold_oracle
    {C : CircuitFamilyClass} {n : Nat}
    {low high : Rat}
    {hlow : 0 ≤ low}
    {hhigh : high ≤ 1}
    {hgap : low < high}
    {adv : Rat}
    (impl : ImplementedThresholdOracle C n) :
    SolvesCoinProblem
        (truthTableCoinInstance n low high hlow hhigh hgap)
        impl.decide
        adv →
      ClassSolvesCoinProblem
        C
        (truthTableCoinInstance n low high hlow hhigh hgap)
        adv :=
  impl.classSolvesCoinProblem_of_advantage

def check_class_solves_coin_problem_of_bounded
    {C : CircuitFamilyClass}
    {inst : CoinProblemInstance}
    {adv : Rat}
    {maxSize : Nat} :
    BoundedClassSolvesCoinProblem C inst adv maxSize →
      ClassSolvesCoinProblem C inst adv :=
  classSolvesCoinProblem_of_bounded

def check_solvesCoinProblem_of_acceptanceProbability_bounds
    {inst : CoinProblemInstance}
    {A : AlgorithmsToLowerBounds.BitVec inst.sampleBits → Bool}
    {adv lowAcceptanceUpper highAcceptanceLower : Rat}
    (hLow :
      acceptanceProbability inst.lowBias A ≤ lowAcceptanceUpper)
    (hHigh :
      highAcceptanceLower ≤ acceptanceProbability inst.highBias A)
    (hGap :
      adv + lowAcceptanceUpper ≤ highAcceptanceLower) :
    SolvesCoinProblem inst A adv :=
  solvesCoinProblem_of_acceptanceProbability_bounds hLow hHigh hGap

def check_acceptanceProbability_mono
    {n : Nat}
    {bias : Rat}
    {A B : AlgorithmsToLowerBounds.BitVec n → Bool}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1)
    (hAB :
      ∀ x : AlgorithmsToLowerBounds.BitVec n, A x = true → B x = true) :
    acceptanceProbability bias A ≤ acceptanceProbability bias B :=
  acceptanceProbability_mono hBias_nonneg hBias_le_one hAB

def check_productBiasWeight_total
    (bias : Rat)
    (n : Nat) :
    (∑ x : AlgorithmsToLowerBounds.BitVec n, productBiasWeight bias x) = 1 :=
  productBiasWeight_total bias n

def check_acceptanceProbability_true
    {n : Nat}
    (bias : Rat) :
    acceptanceProbability bias (fun _ : AlgorithmsToLowerBounds.BitVec n => true) = 1 :=
  acceptanceProbability_true bias

def check_acceptanceProbability_not
    {n : Nat}
    (bias : Rat)
    (A : AlgorithmsToLowerBounds.BitVec n → Bool) :
    acceptanceProbability bias (fun x => ! A x) =
      1 - acceptanceProbability bias A :=
  acceptanceProbability_not bias A

def check_acceptanceProbability_not_le_of_one_sub_le
    {n : Nat}
    {bias : Rat}
    {A : AlgorithmsToLowerBounds.BitVec n → Bool}
    {q : Rat}
    (hMass : 1 - q ≤ acceptanceProbability bias A) :
    acceptanceProbability bias (fun x => ! A x) ≤ q :=
  acceptanceProbability_not_le_of_one_sub_le hMass

def check_acceptanceProbability_fair_eq_bitVecAcceptanceProbability
    {m : Nat}
    (A : AlgorithmsToLowerBounds.BitVec m → Bool) :
    acceptanceProbability ((1 : Rat) / 2) A =
      bitVecAcceptanceProbability A :=
  acceptanceProbability_fair_eq_bitVecAcceptanceProbability A

def check_bitVecAcceptanceProbability_not
    {m : Nat}
    (A : AlgorithmsToLowerBounds.BitVec m → Bool) :
    bitVecAcceptanceProbability (fun x => ! A x) =
      1 - bitVecAcceptanceProbability A :=
  bitVecAcceptanceProbability_not A

def check_one_sub_upper_le_acceptanceProbability_fair_not
    {m : Nat}
    {A : AlgorithmsToLowerBounds.BitVec m → Bool}
    {q : Rat}
    (hA : acceptanceProbability ((1 : Rat) / 2) A ≤ q) :
    1 - q ≤ acceptanceProbability ((1 : Rat) / 2) (fun x => ! A x) :=
  one_sub_upper_le_acceptanceProbability_fair_not hA

def check_mcspThresholdOracle_accepts_of_treeMCSPPredicate
    {n : Nat}
    (oracle : MCSPThresholdOracle n)
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n oracle.threshold tt) :
    oracle.decide tt = true :=
  MCSPThresholdOracle.accepts_of_treeMCSPPredicate oracle hEasy

def check_mcspThresholdOracle_rejects_of_not_treeMCSPPredicate
    {n : Nat}
    (oracle : MCSPThresholdOracle n)
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n oracle.threshold tt) :
    oracle.decide tt = false :=
  MCSPThresholdOracle.rejects_of_not_treeMCSPPredicate oracle hHard

def check_ac0p_coin_contract_excludes_small_solver
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    :
    ¬ BoundedClassSolvesCoinProblem
        (model.classOf p depth)
        (hardness.instance n)
        (hardness.advantage n)
        (contract.sizeBound depth n) :=
  contract.excludes_small_solver hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
  noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
    contract hp w

def check_size_lower_bound_exact_tree_mcsp_threshold_language_of_ac0p_coin_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (exactTreeMCSPThresholdLanguage n w.oracle.threshold)
      (exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)) :=
  sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (exactTreeMCSPThresholdLanguage n w.oracle.threshold)
      (exactTreeMCSPThresholdLowerBound n (contract.sizeBound depth n)) :=
  MCSP_lower_bound_from_AC0pCoinLowerBound
    contract hp w

def check_half_vs_fair_mcsp_coin_reduction_contract
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness) :
    Nat → Nat :=
  contract.threshold

def check_half_vs_fair_mcsp_coin_acceptance_profile
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinAcceptanceProfile hardness) :
    (Nat → Nat) × (Nat → Rat) × (Nat → Rat) :=
  (profile.threshold, profile.lowAcceptanceUpper, profile.fairAcceptanceLower)

def check_half_vs_fair_mcsp_coin_acceptance_profile_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinAcceptanceProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (profile.threshold n))
      (hardness.advantage n) :=
  profile.exact_solvesCoin n

def check_half_vs_fair_mcsp_coin_rejection_profile_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : HalfVsFairMCSPCoinRejectionProfile hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdHardDecision n (profile.threshold n))
      (hardness.advantage n) :=
  profile.hard_solvesCoin n

def check_half_vs_fair_mcsp_coin_reduction_contract_of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness :=
  HalfVsFairMCSPCoinReductionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_acceptance_le
    fair_acceptance_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_rejection_contract_of_distributionFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_rejection_acceptance_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (exactTreeMCSPThresholdHardDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_rejection_acceptance_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (exactTreeMCSPThresholdHardDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_distributionFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_rejection_acceptance_le
    fair_rejection_acceptance_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_reduction_contract_of_treeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (treeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinReductionContract hardness :=
  HalfVsFairMCSPCoinReductionContract.of_treeMCSPPredicateMassFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_mass_le
    fair_mass_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_rejection_contract_of_notTreeMCSPPredicateMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_not_mass_le :
      ∀ n : Nat,
        acceptanceProbability (hardness.instance n).lowBias
            (notTreeMCSPPredicateDecision n (threshold n)) ≤
          lowAcceptanceUpper n)
    (fair_not_mass_ge :
      ∀ n : Nat,
        fairAcceptanceLower n ≤
          acceptanceProbability (hardness.instance n).highBias
            (notTreeMCSPPredicateDecision n (threshold n)))
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_notTreeMCSPPredicateMassFacts
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_not_mass_le
    fair_not_mass_ge
    advantage_gap

def check_half_vs_fair_mcsp_coin_rejection_contract_of_treeMCSPPredicateBiasedLower_and_fairCounting
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper fairAcceptanceLower : Nat → Rat)
    (low_lowComplexity_mass_ge :
      ∀ n : Nat,
        1 - lowAcceptanceUpper n ≤
          acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n)))
    (fair_count_ratio_le :
      ∀ n : Nat,
        treeMCSPCountRatio n (threshold n) ≤
          1 - fairAcceptanceLower n)
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + lowAcceptanceUpper n ≤ fairAcceptanceLower n) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_treeMCSPPredicateBiasedLower_and_fairCounting
    threshold
    lowAcceptanceUpper
    fairAcceptanceLower
    low_lowComplexity_mass_ge
    fair_count_ratio_le
    advantage_gap

def check_half_vs_fair_biased_low_complexity_mass_facts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (threshold : Nat → Nat)
    (lowAcceptanceUpper : Nat → Rat)
    (low_lowComplexity_mass_ge :
      ∀ n : Nat,
        1 - lowAcceptanceUpper n ≤
          acceptanceProbability (hardness.instance n).lowBias
            (treeMCSPPredicateDecision n (threshold n))) :
    HalfVsFairBiasedLowComplexityMassFacts hardness where
  threshold := threshold
  lowAcceptanceUpper := lowAcceptanceUpper
  low_lowComplexity_mass_ge := low_lowComplexity_mass_ge

def check_adjacent_bias_mcsp_threshold_separation_instance
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    CoinProblemInstance :=
  facts.instance n

def check_adjacent_bias_mcsp_threshold_separation_solves_coin
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    SolvesCoinProblem
      (facts.instance n)
      (exactTreeMCSPThresholdHardDecision n (facts.threshold n))
      (facts.advantage n) :=
  facts.toSolvesCoin n

def check_coin_distinguisher_family_instance
    (family : CoinDistinguisherFamily)
    (n : Nat) :
    CoinProblemInstance :=
  family.instance n

def check_coin_distinguisher_family_solves_instance
    (family : CoinDistinguisherFamily)
    (n : Nat) :
    SolvesCoinProblem
      (family.instance n)
      (family.algorithm n)
      (family.advantage n) :=
  family.solves_instance n

def check_circuit_coin_distinguisher_family_solves
    {C : CircuitFamilyClass}
    {family : CoinDistinguisherFamily}
    (realized : CircuitCoinDistinguisherFamily C family)
    (n : Nat) :
    SolvesCoinProblem
      (family.instance n)
      (fun x => C.eval (realized.circuit n) x)
      (family.advantage n) :=
  realized.solves n

def check_circuit_coin_distinguisher_family_bounded_solves
    {C : CircuitFamilyClass}
    {family : CoinDistinguisherFamily}
    (realized : CircuitCoinDistinguisherFamily C family)
    (n : Nat) :
    BoundedClassSolvesCoinProblem
      C
      (family.instance n)
      (family.advantage n)
      (realized.sizeBound n) :=
  realized.boundedSolves n

def check_boundedClassSolvesCoinProblem_mono_size
    {C : CircuitFamilyClass}
    {inst : CoinProblemInstance}
    {adv : Rat}
    {smallBound largeBound : Nat}
    (hSolve : BoundedClassSolvesCoinProblem C inst adv smallBound)
    (hLe : smallBound ≤ largeBound) :
    BoundedClassSolvesCoinProblem C inst adv largeBound :=
  BoundedClassSolvesCoinProblem.mono_size hSolve hLe

noncomputable def check_coin_distinguisher_family_of_adjacentBiasMCSP
    (facts : AdjacentBiasMCSPThresholdSeparationFacts) :
    CoinDistinguisherFamily :=
  CoinDistinguisherFamily.of_adjacentBiasMCSP facts

noncomputable def check_circuit_coin_distinguisher_family_of_adjacentBiasMCSP_circuit
    (C : CircuitFamilyClass)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (circuit :
      ∀ n : Nat, C.Family (Pnp3.Models.Partial.tableLen n))
    (computes :
      ∀ n : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen n),
        C.eval (circuit n) x =
          exactTreeMCSPThresholdHardDecision n (facts.threshold n) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ n : Nat,
        C.size (circuit n) ≤ sizeBound n) :
    CircuitCoinDistinguisherFamily
      C
      (CoinDistinguisherFamily.of_adjacentBiasMCSP facts) :=
  CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
    C
    facts
    circuit
    computes
    sizeBound
    size_le

noncomputable def check_coin_distinguisher_family_of_adjacentBiasMCSP_solves
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (n : Nat) :
    SolvesCoinProblem
      ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).instance n)
      ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).algorithm n)
      ((CoinDistinguisherFamily.of_adjacentBiasMCSP facts).advantage n) :=
  (CoinDistinguisherFamily.of_adjacentBiasMCSP facts).solves_instance n

def check_coin_distinguisher_to_half_vs_fair_translation_contract
    (source : CoinDistinguisherFamily)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  CoinDistinguisherToHalfVsFairTranslationContract source hardness

def check_coin_translation_preserves_class
    (C : CircuitFamilyClass)
    (source : CoinDistinguisherFamily)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  CoinTranslationPreservesClass C source hardness

def check_coin_distinguisher_to_half_vs_fair_translation_solves
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (translation :
      CoinDistinguisherToHalfVsFairTranslationContract source hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (translation.translatedAlgorithm n)
      (hardness.advantage n) :=
  translation.solvesCoin n

noncomputable def check_half_vs_fair_coin_distinguisher_family
    (hardness : HalfVsFairTruthTableCoinHardness)
    (A : ∀ n : Nat, AlgorithmsToLowerBounds.BitVec (hardness.instance n).sampleBits → Bool)
    (hSolves :
      ∀ n : Nat,
        SolvesCoinProblem
          (hardness.instance n)
          (A n)
          (hardness.advantage n)) :
    CoinDistinguisherFamily :=
  halfVsFairCoinDistinguisherFamily hardness A hSolves

noncomputable def check_circuit_coin_distinguisher_family_translate_to_halfVsFair
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (realized : CircuitCoinDistinguisherFamily C source)
    (translation : CoinTranslationPreservesClass C source hardness) :
    CircuitCoinDistinguisherFamily
      C
      (halfVsFairCoinDistinguisherFamily
        hardness
        (fun n x =>
          C.eval (translation.translateCircuit n (realized.circuit n)) x)
        (fun n =>
          translation.solvesTarget_of_solvesSource
            n
            (realized.circuit n)
            (realized.solves n))) :=
  realized.translate_to_halfVsFair translation

def check_boundedClassSolvesCoinProblem_of_translated_realization
    {C : CircuitFamilyClass}
    {source : CoinDistinguisherFamily}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (realized : CircuitCoinDistinguisherFamily C source)
    (translation : CoinTranslationPreservesClass C source hardness)
    (n : Nat) :
    BoundedClassSolvesCoinProblem
      C
      (hardness.instance n)
      (hardness.advantage n)
      (realized.sizeBound n) :=
  BoundedClassSolvesCoinProblem_of_translated_realization
    realized
    translation
    n

def check_false_of_translated_realization_and_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    {source : CoinDistinguisherFamily}
    {p depth n : Nat}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hp : Nat.Prime p)
    (realized :
      CircuitCoinDistinguisherFamily
        (model.classOf p depth)
        source)
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        source
        hardness)
    (hSize :
      realized.sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_translated_realization_and_AC0pCoinLowerBound
    contract
    hp
    realized
    translation
    hSize

def check_false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    {facts : AdjacentBiasMCSPThresholdSeparationFacts}
    {p depth n : Nat}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (hp : Nat.Prime p)
    (realized :
      CircuitCoinDistinguisherFamily
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts))
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (hSize :
      realized.sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
    contract
    hp
    realized
    translation
    hSize

def check_false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (translation :
      CoinTranslationPreservesClass
        (model.classOf p depth)
        (CoinDistinguisherFamily.of_adjacentBiasMCSP facts)
        hardness)
    (circuit :
      ∀ m : Nat,
        (model.classOf p depth).Family (Pnp3.Models.Partial.tableLen m))
    (computes :
      ∀ m : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (Pnp3.Models.Partial.tableLen m),
        (model.classOf p depth).eval (circuit m) x =
          exactTreeMCSPThresholdHardDecision m (facts.threshold m) x)
    (sizeBound : Nat → Nat)
    (size_le :
      ∀ m : Nat,
        (model.classOf p depth).size (circuit m) ≤ sizeBound m)
    (hSize :
      sizeBound n ≤ contract.sizeBound depth n) :
    False :=
  false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
    contract
    facts
    hp
    translation
    circuit
    computes
    sizeBound
    size_le
    hSize

noncomputable def check_adjacent_bias_to_half_vs_fair_coin_solver_translation_contract
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  AdjacentBiasToHalfVsFairCoinSolverTranslationContract facts hardness

def check_adjacent_bias_to_half_vs_fair_rejection_translation_contract
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (hardness : HalfVsFairTruthTableCoinHardness) :
    Type :=
  AdjacentBiasToHalfVsFairRejectionTranslationContract facts hardness

def check_half_vs_fair_mcsp_coin_rejection_contract_of_adjacentBiasSeparation_and_translation
    {hardness : HalfVsFairTruthTableCoinHardness}
    (facts : AdjacentBiasMCSPThresholdSeparationFacts)
    (translation :
      AdjacentBiasToHalfVsFairRejectionTranslationContract facts hardness) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_adjacentBiasSeparation_and_translation
    facts
    translation

def check_treeMCSPCountRatio_le_one_sub_self_fairLower
    (n threshold : Nat) :
    treeMCSPCountRatio n threshold ≤
      1 - (1 - treeMCSPCountRatio n threshold) :=
  treeMCSPCountRatio_le_one_sub_self_fairLower n threshold

noncomputable def check_half_vs_fair_mcsp_coin_rejection_contract_of_biasedLowComplexityMassFacts
    {hardness : HalfVsFairTruthTableCoinHardness}
    (facts : HalfVsFairBiasedLowComplexityMassFacts hardness)
    (advantage_gap :
      ∀ n : Nat,
        hardness.advantage n + facts.lowAcceptanceUpper n ≤
          1 - treeMCSPCountRatio n (facts.threshold n)) :
    HalfVsFairMCSPCoinRejectionContract hardness :=
  HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts
    facts
    advantage_gap

def check_halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    acceptanceProbability (hardness.instance n).highBias
        (treeMCSPPredicateDecision n threshold) ≤
      treeMCSPCountRatio n threshold :=
  halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio n threshold

def check_one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    1 - treeMCSPCountRatio n threshold ≤
      acceptanceProbability (hardness.instance n).highBias
        (notTreeMCSPPredicateDecision n threshold) :=
  one_sub_countRatio_le_halfVsFair_highBias_notTreeMCSPPredicateDecision
    n threshold

def check_one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
    {hardness : HalfVsFairTruthTableCoinHardness}
    (n threshold : Nat) :
    1 - treeMCSPCountRatio n threshold ≤
      acceptanceProbability (hardness.instance n).highBias
        (exactTreeMCSPThresholdHardDecision n threshold) :=
    one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
    n threshold

def check_halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hMass :
      1 - q ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n threshold)) :
    acceptanceProbability (hardness.instance n).lowBias
        (notTreeMCSPPredicateDecision n threshold) ≤ q :=
  halfVsFair_lowBias_notTreeMCSPPredicateDecision_le_of_treeMCSPPredicate_mass_lower
    hMass

def check_halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n threshold : Nat}
    {q : Rat}
    (hMass :
      1 - q ≤
        acceptanceProbability (hardness.instance n).lowBias
          (treeMCSPPredicateDecision n threshold)) :
    acceptanceProbability (hardness.instance n).lowBias
        (exactTreeMCSPThresholdHardDecision n threshold) ≤ q :=
  halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
    hMass

def check_half_vs_fair_mcsp_coin_reduction_contract_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.exact_solvesCoin n

def check_half_vs_fair_mcsp_coin_rejection_contract_solves
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinRejectionContract hardness)
    (n : Nat) :
    SolvesCoinProblem
      (hardness.instance n)
      (exactTreeMCSPThresholdHardDecision n (contract.threshold n))
      (hardness.advantage n) :=
  contract.hard_solvesCoin n

noncomputable def check_half_vs_fair_mcsp_coin_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n : Nat) : BitVecLanguage :=
  halfVsFairMCSPCoinLanguage contract n

noncomputable def check_half_vs_fair_mcsp_coin_asymptotic_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness) :
    BitVecLanguage :=
  halfVsFairMCSPCoinAsymptoticLanguage contract

def check_half_vs_fair_mcsp_coin_lower_bound
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : HalfVsFairMCSPCoinReductionContract hardness)
    (n maxSize : Nat) : Nat → Nat :=
  halfVsFairMCSPCoinLowerBound contract n maxSize

def check_mcsp_lower_bound_from_ac0p_coin_lower_bound_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (lowerBound : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (halfVsFairMCSPCoinLowerBound reduction n (lowerBound.sizeBound depth n)) :=
  MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
    lowerBound reduction hp

def check_not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
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
    ¬ InAC0p model p (halfVsFairMCSPCoinAsymptoticLanguage reduction) :=
  not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
    contract reduction hGrowth p hp

def check_ac0pCoinLowerEnvelope_beatsEveryPolynomial
    (envelopeConst depth : Nat) :
    BeatsEveryPolynomialSizeBoundAtArbitrarilyLargeTableLengths
      (fun n => ac0pCoinLowerEnvelope envelopeConst depth n) :=
  ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths
    envelopeConst depth

def check_not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    (p : Nat)
    (hp : Nat.Prime p) :
    ¬ InAC0p model p (halfVsFairMCSPCoinAsymptoticLanguage reduction) :=
  not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
    contract reduction p hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_lower_bound_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (lowerBound : AC0pHalfVsFairCoinLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ lowerBound.sizeBound depth n ∧
        impl.threshold = reduction.threshold n :=
  noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound_and_reduction
    lowerBound reduction hp

def check_ac0p_coin_lower_envelope
    (c depth n : Nat) : Nat :=
  ac0pCoinLowerEnvelope c depth n

def check_eventually_at_least_ac0p_coin_lower_envelope
    (sizeBound : Nat → Nat → Nat) : Prop :=
  EventuallyAtLeastAC0pCoinLowerEnvelope sizeBound

def check_eventually_at_least_ac0p_coin_lower_envelope_self
    (c : Nat) : Prop :=
  EventuallyAtLeastAC0pCoinLowerEnvelope (ac0pCoinLowerEnvelope c)

def check_ac0p_coin_bias_gap_envelope
    (c n : Nat) : Rat :=
  ac0pCoinBiasGapEnvelope c n

def check_eventually_at_most_ac0p_coin_bias_gap_envelope
    (biasGap : Nat → Rat) : Prop :=
  EventuallyAtMostAC0pCoinBiasGapEnvelope biasGap

def check_eventually_at_least_positive_coin_advantage
    (advantage : Nat → Rat) : Prop :=
  EventuallyAtLeastPositiveCoinAdvantage advantage

def check_ac0p_coin_published_half_vs_fair_regime
    {hardness : HalfVsFairTruthTableCoinHardness}
    (profile : AC0pCoinPublishedHalfVsFairRegime hardness) :
    EventuallyAtMostAC0pCoinBiasGapEnvelope hardness.biasGap ∧
      EventuallyAtLeastPositiveCoinAdvantage hardness.advantage :=
  ⟨profile.biasGap_profile, profile.advantage_profile⟩

def check_ac0p_coin_quantitative_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness) :
    Prop :=
  EventuallyAtLeastAC0pCoinLowerEnvelope contract.sizeBound

def check_ac0p_coin_published_exp_lower_bound_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness) :
    contract.base.sizeBound = ac0pCoinLowerEnvelope contract.envelopeConst ∧
      EventuallyAtMostAC0pCoinBiasGapEnvelope hardness.biasGap ∧
      EventuallyAtLeastPositiveCoinAdvantage hardness.advantage :=
  ⟨contract.sizeBound_eq,
    contract.hardness_profile.biasGap_profile,
    contract.hardness_profile.advantage_profile⟩

noncomputable def check_ac0p_coin_quantitative_language
    {hardness : HalfVsFairTruthTableCoinHardness}
    {n : Nat}
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    BitVecLanguage :=
  AC0pCoinQuantitativeLanguage w

def check_ac0p_coin_quantitative_lower_bound
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (depth n : Nat) : Nat → Nat :=
  AC0pCoinQuantitativeLowerBound contract depth n

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_quantitative_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
  noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_quantitative_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (AC0pCoinQuantitativeLanguage w)
      (AC0pCoinQuantitativeLowerBound contract depth n) :=
  MCSP_lower_bound_from_AC0pCoinQuantitativeContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_quantitative_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (halfVsFairMCSPCoinLowerBound reduction n (contract.sizeBound depth n)) :=
  MCSP_lower_bound_from_AC0pCoinQuantitativeContract_and_reduction
    contract reduction hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_quantitative_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pHalfVsFairCoinQuantitativeContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤ contract.sizeBound depth n ∧
        impl.threshold = reduction.threshold n :=
  noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract_and_reduction
    contract reduction hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_published_exp_lower_bound_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤
          ac0pCoinLowerEnvelope contract.envelopeConst depth n ∧
        impl.threshold = w.oracle.threshold ∧
        (∀ tt : TruthTable n, impl.decide tt = w.oracle.decide tt) :=
  noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_published_exp_lower_bound_contract
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p)
    (w : HalfVsFairMCSPCoinReductionWitness hardness n) :
    SizeLowerBound
      (model.classOf p depth)
      (AC0pCoinQuantitativeLanguage w)
      (exactTreeMCSPThresholdLowerBound
        n
        (ac0pCoinLowerEnvelope contract.envelopeConst depth n)) :=
  MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract
    contract hp w

def check_mcsp_lower_bound_from_ac0p_coin_published_exp_lower_bound_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    SizeLowerBound
      (model.classOf p depth)
      (halfVsFairMCSPCoinLanguage reduction n)
      (exactTreeMCSPThresholdLowerBound
        n
        (ac0pCoinLowerEnvelope contract.envelopeConst depth n)) :=
  MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
    contract reduction hp

def check_no_small_implemented_threshold_oracle_of_ac0p_coin_published_exp_lower_bound_contract_and_reduction
    {model : AC0pFamilyModel}
    {hardness : HalfVsFairTruthTableCoinHardness}
    (contract : AC0pCoinPublishedExpLowerBoundContract model hardness)
    (reduction : HalfVsFairMCSPCoinReductionContract hardness)
    {p depth n : Nat}
    (hp : Nat.Prime p) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf p depth) n,
        (model.classOf p depth).size impl.circuit ≤
          ac0pCoinLowerEnvelope contract.envelopeConst depth n ∧
        impl.threshold = reduction.threshold n :=
  noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract_and_reduction
    contract reduction hp

def check_exact_tree_mcsp_threshold_decision_accepts
    {n threshold : Nat}
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdDecision n threshold tt = true :=
  exactTreeMCSPThresholdDecision_accepts_of_treeMCSPPredicate hEasy

noncomputable def check_treeMCSPPredicateDecision
    (n threshold : Nat) :
    TruthTable n → Bool :=
  treeMCSPPredicateDecision n threshold

def check_treeMCSPPredicateDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    treeMCSPPredicateDecision n threshold tt = true ↔
      treeMCSPPredicate n threshold tt :=
  treeMCSPPredicateDecision_spec tt

def check_notTreeMCSPPredicateDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    notTreeMCSPPredicateDecision n threshold tt = true ↔
      ¬ treeMCSPPredicate n threshold tt :=
  notTreeMCSPPredicateDecision_spec tt

def check_exactTreeMCSPThresholdHardDecision_spec
    {n threshold : Nat}
    (tt : TruthTable n) :
    exactTreeMCSPThresholdHardDecision n threshold tt = true ↔
      ¬ treeMCSPPredicate n threshold tt :=
  exactTreeMCSPThresholdHardDecision_spec tt

def check_exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision
    (n threshold : Nat) :
    exactTreeMCSPThresholdHardDecision n threshold =
      notTreeMCSPPredicateDecision n threshold :=
  exactTreeMCSPThresholdHardDecision_eq_notTreeMCSPPredicateDecision n threshold

noncomputable def check_treeMCSPPredicateOracle
    (n threshold : Nat) :
    MCSPThresholdOracle n :=
  treeMCSPPredicateOracle n threshold

def check_uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    (n threshold : Nat) :
    uniformTruthTableAcceptanceProbability (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
  uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    n threshold

def check_fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
    (n threshold : Nat) :
    acceptanceProbability ((1 : Rat) / 2) (treeMCSPPredicateDecision n threshold) ≤
      (Pnp3.Models.circuitCountBound n threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
  fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio n threshold

def check_one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
    (n threshold : Nat) :
    1 -
        (Pnp3.Models.circuitCountBound n threshold : Rat) /
          (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) ≤
      acceptanceProbability ((1 : Rat) / 2)
        (notTreeMCSPPredicateDecision n threshold) :=
  one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
    n threshold

def check_exact_tree_mcsp_threshold_decision_rejects
    {n threshold : Nat}
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdDecision n threshold tt = false :=
  exactTreeMCSPThresholdDecision_rejects_of_not_treeMCSPPredicate hHard

def check_exact_tree_mcsp_threshold_hard_decision_accepts
    {n threshold : Nat}
    {tt : TruthTable n}
    (hHard : ¬ treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdHardDecision n threshold tt = true :=
  exactTreeMCSPThresholdHardDecision_accepts_of_not_treeMCSPPredicate hHard

def check_exact_tree_mcsp_threshold_hard_decision_rejects
    {n threshold : Nat}
    {tt : TruthTable n}
    (hEasy : treeMCSPPredicate n threshold tt) :
    exactTreeMCSPThresholdHardDecision n threshold tt = false :=
  exactTreeMCSPThresholdHardDecision_rejects_of_treeMCSPPredicate hEasy

def check_acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
    {n threshold : Nat}
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1) :
    acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) ≤
      acceptanceProbability bias (treeMCSPPredicateDecision n threshold) :=
  acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
    hBias_nonneg hBias_le_one

def check_treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
    {n threshold : Nat}
    {bias : Rat}
    (hBias_nonneg : 0 ≤ bias)
    (hBias_le_one : bias ≤ 1) :
    acceptanceProbability bias (treeMCSPPredicateDecision n threshold) ≤
      acceptanceProbability bias (exactTreeMCSPThresholdDecision n threshold) :=
  treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
    hBias_nonneg hBias_le_one

def check_uniform_truth_table_acceptance_probability_le_count_ratio_of_tree_mcsp_oracle
    {n : Nat}
    (oracle : MCSPThresholdOracle n) :
    uniformTruthTableAcceptanceProbability oracle.decide ≤
      (Pnp3.Models.circuitCountBound n oracle.threshold : Rat) /
        (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat) :=
  uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle oracle

def check_no_small_implemented_threshold_oracle_of_local_prg_transfer
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
                (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) :=
  noSmallImplementedThresholdOracle_of_localPRGTransfer prg hFool

def check_no_small_implemented_threshold_oracle_of_fools_local_prg_transfer
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
                (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)) :=
  noSmallImplementedThresholdOracle_of_foolsLocalPRGTransfer prg hFool

noncomputable def check_tree_mcsp_count_ratio
    (n threshold : Nat) : Rat :=
  treeMCSPCountRatio n threshold

noncomputable def check_exact_tree_mcsp_threshold_language
    (n threshold : Nat) : BitVecLanguage :=
  exactTreeMCSPThresholdLanguage n threshold

def check_exact_tree_mcsp_threshold_lower_bound
    (n maxSize : Nat) : Nat → Nat :=
  exactTreeMCSPThresholdLowerBound n maxSize

def check_size_lower_bound_exact_tree_mcsp_threshold_language_of_local_prg_transfer
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
      (exactTreeMCSPThresholdLowerBound n maxSize) :=
  sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer
    prg hThreshold hFool hEpsSmall

def check_published_local_prg_route_to_one_sided
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec} :
    PublishedLocalPRGRouteContract model spec →
      PublishedOneSidedLocalPRGRouteContract model spec :=
  PublishedLocalPRGRouteContract.toOneSided

def check_formulaCircuit_target_family_model :
    LocalPRGTargetFamilyModel :=
  formulaCircuitTargetFamilyModel

def check_formulaCircuit_published_local_prg_route_contract
    (spec : LocalPRGHardnessSpec) :
    Type :=
  FormulaCircuitPublishedLocalPRGRouteContract spec

def check_formulaCircuit_slice_spec
    (threshold sizeBound : Nat → Nat) :
    FormulaCircuitSliceSpec :=
  ⟨threshold, sizeBound⟩

def check_formulaCircuit_published_lower_bound_contract
    (spec : FormulaCircuitSliceSpec) :
    Prop :=
  FormulaCircuitPublishedLowerBoundContract spec

def check_CKLM_formulaCircuit_published_route_contract
    (spec : CKLMFormulaCircuitHardnessSpec) :
    Type :=
  CKLMFormulaCircuitPublishedRouteContract spec

def check_CKLM_formulaCircuit_theorem2_contract
    (spec : CKLMFormulaCircuitHardnessSpec) :
    Prop :=
  CKLMFormulaCircuitPublishedTheorem2Contract spec

def check_cklm_formula_theorem2_lower_envelope
    (c n : Nat) : Nat :=
  cklmFormulaTheorem2LowerEnvelope c n

def check_eventually_at_least_cklm_formula_theorem2_lower_envelope
    (sizeBound : Nat → Nat) : Prop :=
  EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound

def check_CKLM_formulaCircuit_theorem2_hardness
    (threshold sizeBound : Nat → Nat)
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound) :
    CKLMFormulaCircuitTheorem2Hardness :=
  ⟨threshold, sizeBound, hProfile⟩

def check_CKLM_formulaCircuit_localPRG_source_spec
    (threshold sizeBound : Nat → Nat)
    (epsilon : Nat → Rat)
    (hEpsSmall :
      ∀ n : Nat, epsilon n < 1 - treeMCSPCountRatio n (threshold n))
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound) :
    CKLMFormulaCircuitLocalPRGSourceSpec where
  threshold := threshold
  sizeBound := sizeBound
  epsilon := epsilon
  epsilon_small := hEpsSmall
  theorem2_profile := hProfile

def check_CKLM_formulaCircuit_localPRG_source_contract
    (source : CKLMFormulaCircuitLocalPRGSourceSpec) :
    Type :=
  CKLMFormulaCircuitLocalPRGSourceContract source

def check_CKLM_formulaCircuit_localPRG_source_to_route
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    FormulaCircuitPublishedLocalPRGRouteContract
      source.toLocalPRGHardnessSpec :=
  contract.toPublishedRoute

def check_CKLM_formulaCircuit_theorem2_contract_of_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    CKLMFormulaCircuitPublishedTheorem2Contract
      source.toCKLMFormulaCircuitHardnessSpec :=
  CKLMFormulaCircuitPublishedTheorem2Contract.ofLocalPRGSource contract

def check_CKLM_formulaCircuit_theorem2_quantitative_contract_of_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
      source.toTheorem2Hardness :=
  CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofLocalPRGSource
    contract

def check_CKLM_formulaCircuit_theorem2_quantitative_contract
    (hardness : CKLMFormulaCircuitTheorem2Hardness) :
    Prop :=
  CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness

noncomputable def check_CKLM_formulaCircuit_language
    (spec : CKLMFormulaCircuitHardnessSpec)
    (n : Nat) : BitVecLanguage :=
  CKLMFormulaCircuitLanguage spec n

def check_CKLM_formulaCircuit_lower_bound
    (spec : CKLMFormulaCircuitHardnessSpec)
    (n : Nat) : Nat → Nat :=
  CKLMFormulaCircuitLowerBound spec n

noncomputable def check_CKLM_formulaCircuit_quantitative_language
    (hardness : CKLMFormulaCircuitTheorem2Hardness)
    (n : Nat) : BitVecLanguage :=
  CKLMFormulaCircuitQuantitativeLanguage hardness n

def check_CKLM_formulaCircuit_quantitative_lower_bound
    (hardness : CKLMFormulaCircuitTheorem2Hardness)
    (n : Nat) : Nat → Nat :=
  CKLMFormulaCircuitQuantitativeLowerBound hardness n

noncomputable def check_formulaCircuit_asymptotic_language
    (spec : LocalPRGHardnessSpec) :
    Pnp3.ComplexityInterfaces.Language :=
  formulaCircuitAsymptoticLanguage spec

def check_beats_every_ppoly_bound_at_some_table_length
    (sizeBound : Nat → Nat) :
    Prop :=
  BeatsEveryPpolyBoundAtSomeTableLength sizeBound

def check_mcsp_lower_bound_from_published_local_prg_route
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedLocalPRGRouteContract model spec)
    (n : Nat) :
    SizeLowerBound
      (model.classOf n)
      (thresholdMCSPLanguage spec n)
      (thresholdMCSPLowerBound spec n) :=
  MCSP_lower_bound_from_publishedLocalPRGRoute contract n

def check_formulaCircuit_mcsp_lower_bound_from_published_local_prg_route
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (thresholdMCSPLanguage spec n)
      (thresholdMCSPLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_publishedLocalPRGRoute contract n

def check_formulaCircuit_mcsp_lower_bound_from_published_lower_bound_contract
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (formulaCircuitThresholdLanguage spec n)
      (formulaCircuitThresholdLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_formula_route
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitRoute
    contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_formula_theorem2_contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract
    contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_formula_theorem2_quantitative_contract
    {hardness : CKLMFormulaCircuitTheorem2Hardness}
    (contract : CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitQuantitativeLanguage hardness n)
      (CKLMFormulaCircuitQuantitativeLowerBound hardness n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract
    contract n

def check_formulaCircuit_mcsp_lower_bound_from_CKLM_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitQuantitativeLanguage source.toTheorem2Hardness n)
      (CKLMFormulaCircuitQuantitativeLowerBound source.toTheorem2Hardness n) :=
  formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitLocalPRGSource
    contract n

def check_no_small_implemented_threshold_oracle_of_published_local_prg_route
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedLocalPRGRouteContract model spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf n) n,
        (model.classOf n).size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_publishedLocalPRGRoute contract n

def check_no_small_implemented_threshold_oracle_of_formulaCircuit_published_local_prg_route
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_formulaCircuitPublishedLocalPRGRoute
    contract n

def check_no_small_implemented_threshold_oracle_of_published_formulaCircuit_lower_bound_contract
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_formula_route
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitRoute
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_formula_theorem2_contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2Contract
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_formula_theorem2_quantitative_contract
    {hardness : CKLMFormulaCircuitTheorem2Hardness}
    (contract : CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ hardness.sizeBound n ∧
        impl.threshold = hardness.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2QuantitativeContract
    contract n

def check_no_small_implemented_threshold_oracle_of_CKLM_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ source.sizeBound n ∧
        impl.threshold = source.threshold n :=
  noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitLocalPRGSource
    contract n

def check_no_ppolyFormula_of_formulaCircuit_published_local_prg_route
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec) :=
  no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
    contract hGrowth

def check_no_ppolyFormula_of_cklm_formula_or_branching_program_route
    {spec : FormulaOrBranchingProgramLocalPRGHardnessSpec}
    (contract :
      FormulaCircuitPublishedLocalPRGRouteContract spec.toLocalPRGHardnessSpec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec.toLocalPRGHardnessSpec) :=
  no_PpolyFormula_of_CKLM_formulaOrBranchingProgramRoute_and_growth
    contract hGrowth

def check_no_ppolyFormula_of_CKLM_localPRG_source
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength source.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage source.toLocalPRGHardnessSpec) :=
  no_PpolyFormula_of_CKLMFormulaCircuitLocalPRGSource_and_growth
    contract hGrowth

def check_not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope
    (c : Nat) :
    ¬ BeatsEveryPpolyBoundAtSomeTableLength (cklmFormulaTheorem2LowerEnvelope c) :=
  not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope c

def check_not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope
    (c : Nat) :
    ¬ BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
        (cklmFormulaTheorem2LowerEnvelope c) :=
  not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope c

def check_no_uniform_cklmEnvelopeFrequentEscape :
    (∀ c : Nat,
      BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
        (cklmFormulaTheorem2LowerEnvelope c)) → False :=
  no_uniform_cklmEnvelopeFrequentEscape

#print axioms AlgorithmsToLowerBounds.NP_not_subset_PpolyDAG_of_verified_source
#print axioms AlgorithmsToLowerBounds.P_ne_NP_of_verified_source
#print axioms AlgorithmsToLowerBounds.maskBit_true
#print axioms AlgorithmsToLowerBounds.maskBit_false
#print axioms AlgorithmsToLowerBounds.maskVec_apply
#print axioms AlgorithmsToLowerBounds.expectationProductBias_sub
#print axioms AlgorithmsToLowerBounds.expectationProductBias_le_of_pointwise_le
#print axioms AlgorithmsToLowerBounds.exists_max_bitVec_rat
#print axioms AlgorithmsToLowerBounds.maskedAcceptanceAverage_eq_acceptanceProbability_mul
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_nonneg
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_le_one
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_mul_highTargetBias
#print axioms AlgorithmsToLowerBounds.MaskingBiasParams.keepBias_mul_lowTargetBias
#print axioms AlgorithmsToLowerBounds.maskedAcceptanceAdvantage_eq_expectation_fixed
#print axioms AlgorithmsToLowerBounds.MaskAveragingContract.of_valid_keepBias
#print axioms AlgorithmsToLowerBounds.MaskAveragingContract.of_maskingBiasParams
#print axioms AlgorithmsToLowerBounds.MaskingPushforwardFacts.of_maskingBiasParams
#print axioms AlgorithmsToLowerBounds.CoinMaskingTranslationFacts.of_maskingBiasParams
#print axioms AlgorithmsToLowerBounds.MaskingPushforwardFacts.masked_advantage_eq_source
#print axioms AlgorithmsToLowerBounds.CoinMaskingTranslationFacts.exists_mask_with_source_advantage
#print axioms AlgorithmsToLowerBounds.bestMaskForCircuit
#print axioms AlgorithmsToLowerBounds.bestMaskForCircuit_max
#print axioms AlgorithmsToLowerBounds.source_advantage_le_bestMask_fixed_advantage
#print axioms AlgorithmsToLowerBounds.coinTranslationPreservesClass_of_maskingSetup
#print axioms AlgorithmsToLowerBounds.AC0pFamilyModelWithMasking.closed
#print axioms AlgorithmsToLowerBounds.coinTranslationPreservesClass_of_maskingSetup_AC0p
#print axioms AlgorithmsToLowerBounds.false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_maskingSetup
#print axioms AlgorithmsToLowerBounds.maskingParams_of_adjacentBiasToHalfVsFair
#print axioms AlgorithmsToLowerBounds.CoinMaskingTranslationSetup.of_adjacentBiasToHalfVsFair
#print axioms AlgorithmsToLowerBounds.false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision_of_adjacentMaskingSetup
#print axioms AlgorithmsToLowerBounds.quasiPolyLower_superPolynomialGrowth
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_superPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_quasiPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.EventuallySizeLowerBound.weaken
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_eventual_superPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_of_eventual_quasiPolynomial_lowerBound
#print axioms AlgorithmsToLowerBounds.not_depth_d_AC0p_of_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_of_depthwise_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_from_quasiPolynomial_contract
#print axioms AlgorithmsToLowerBounds.not_depth_d_AC0p_of_eventual_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_of_depthwise_eventual_quasiPoly_lowerBound
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_from_asymptotic_quasiPolynomial_contract
#print axioms AlgorithmsToLowerBounds.productBiasWeight_total
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_true
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_not
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_not_le_of_one_sub_le
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_mono
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_mono_lowBias
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_mono_highBias
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_fair_eq_bitVecAcceptanceProbability
#print axioms AlgorithmsToLowerBounds.bitVecAcceptanceProbability_not
#print axioms AlgorithmsToLowerBounds.one_sub_upper_le_acceptanceProbability_fair_not
#print axioms AlgorithmsToLowerBounds.solvesCoinProblem_of_acceptanceProbability_bounds
#print axioms AlgorithmsToLowerBounds.MCSPThresholdOracle.accepts_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.MCSPThresholdOracle.rejects_of_not_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.ImplementedThresholdOracle.classSolvesCoinProblem_of_advantage
#print axioms AlgorithmsToLowerBounds.classSolvesCoinProblem_of_bounded
#print axioms AlgorithmsToLowerBounds.BoundedClassSolvesCoinProblem.mono_size
#print axioms AlgorithmsToLowerBounds.AC0pHalfVsFairCoinLowerBoundContract.excludes_small_solver
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinReductionContract.of_distributionFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinReductionContract.of_treeMCSPPredicateMassFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionProfile.hard_solvesCoin
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_notTreeMCSPPredicateMassFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_treeMCSPPredicateBiasedLower_and_fairCounting
#print axioms AlgorithmsToLowerBounds.CoinDistinguisherFamily.solves_instance
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.solves
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.boundedSolves
#print axioms AlgorithmsToLowerBounds.AdjacentBiasMCSPThresholdSeparationFacts.toSolvesCoin
#print axioms AlgorithmsToLowerBounds.CoinDistinguisherFamily.of_adjacentBiasMCSP
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
#print axioms AlgorithmsToLowerBounds.CoinDistinguisherToHalfVsFairTranslationContract.solvesCoin
#print axioms AlgorithmsToLowerBounds.halfVsFairCoinDistinguisherFamily
#print axioms AlgorithmsToLowerBounds.CircuitCoinDistinguisherFamily.translate_to_halfVsFair
#print axioms AlgorithmsToLowerBounds.BoundedClassSolvesCoinProblem_of_translated_realization
#print axioms AlgorithmsToLowerBounds.false_of_translated_realization_and_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.false_of_adjacentBias_realization_translation_and_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_adjacentBiasSeparation_and_translation
#print axioms AlgorithmsToLowerBounds.treeMCSPCountRatio_le_one_sub_self_fairLower
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts
#print axioms AlgorithmsToLowerBounds.HalfVsFairMCSPCoinRejectionContract.hard_solvesCoin
#print axioms AlgorithmsToLowerBounds.treeMCSPPredicateDecision_spec
#print axioms AlgorithmsToLowerBounds.notTreeMCSPPredicateDecision_spec
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdHardDecision_spec
#print axioms AlgorithmsToLowerBounds.uniformTruthTableAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
#print axioms AlgorithmsToLowerBounds.fairAcceptanceProbability_treeMCSPPredicateDecision_le_countRatio
#print axioms AlgorithmsToLowerBounds.one_sub_countRatio_le_fairAcceptanceProbability_notTreeMCSPPredicateDecision
#print axioms AlgorithmsToLowerBounds.halfVsFair_highBias_treeMCSPPredicateDecision_le_countRatio
#print axioms AlgorithmsToLowerBounds.one_sub_countRatio_le_halfVsFair_highBias_exactTreeMCSPThresholdHardDecision
#print axioms AlgorithmsToLowerBounds.halfVsFair_lowBias_exactTreeMCSPThresholdHardDecision_le_of_treeMCSPPredicate_mass_lower
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdDecision_accepts_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdDecision_rejects_of_not_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdHardDecision_accepts_of_not_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.exactTreeMCSPThresholdHardDecision_rejects_of_treeMCSPPredicate
#print axioms AlgorithmsToLowerBounds.acceptanceProbability_exactTreeMCSPThresholdDecision_le_treeMCSPPredicateDecision
#print axioms AlgorithmsToLowerBounds.treeMCSPPredicateDecision_le_acceptanceProbability_exactTreeMCSPThresholdDecision
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.sizeLowerBound_exactTreeMCSPThresholdLanguage_of_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinLowerBound
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinLowerBound_and_reduction
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinLowerBound_and_reduction
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinQuantitativeContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinQuantitativeContract_and_reduction
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinQuantitativeContract_and_reduction
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_AC0pCoinPublishedExpLowerBoundContract_and_reduction
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_AC0pCoinPublishedExpLowerBoundContract_and_reduction
#print axioms AlgorithmsToLowerBounds.halfVsFairMCSPCoinAsymptoticLanguage_eq_slice_at_tableLen
#print axioms AlgorithmsToLowerBounds.ac0pCoinLowerEnvelope_beatsEveryPolynomial_at_arbitrarilyLarge_tableLengths
#print axioms AlgorithmsToLowerBounds.not_hasPolynomialSizeFamily_halfVsFairMCSPCoinAsymptoticLanguage
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract_and_growth
#print axioms AlgorithmsToLowerBounds.not_in_AC0p_halfVsFairMCSPCoinAsymptoticLanguage_from_published_contract
#print axioms AlgorithmsToLowerBounds.uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_localPRGTransfer
#print axioms AlgorithmsToLowerBounds.sizeLowerBound_exactTreeMCSPThresholdLanguage_of_localPRGTransfer
#print axioms AlgorithmsToLowerBounds.MCSP_lower_bound_from_publishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_publishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_publishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_formulaCircuitPublishedLocalPRGRoute
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitRoute
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitRoute
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2Contract
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2QuantitativeContract
#print axioms AlgorithmsToLowerBounds.formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitLocalPRGSource
#print axioms AlgorithmsToLowerBounds.noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitLocalPRGSource
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_CKLM_formulaOrBranchingProgramRoute_and_growth
#print axioms AlgorithmsToLowerBounds.no_PpolyFormula_of_CKLMFormulaCircuitLocalPRGSource_and_growth
#print axioms AlgorithmsToLowerBounds.not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope
#print axioms AlgorithmsToLowerBounds.not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope
#print axioms AlgorithmsToLowerBounds.no_uniform_cklmEnvelopeFrequentEscape

#check Pnp4.Frontier.ContractExpansion.CanonicalRawTreeMCSPPrefixFields
#check Pnp4.Frontier.ContractExpansion.encodeTreeMCSPPrefixFields
#check Pnp4.Frontier.ContractExpansion.CanonicalRawTreeMCSPPrefixFields.toPrefixInput
#print axioms Pnp4.Frontier.ContractExpansion.encodeTreeMCSPPrefixFields_length_convention
#print axioms Pnp4.Frontier.ContractExpansion.bitLength_pos_of_pos
#print axioms Pnp4.Frontier.ContractExpansion.nat_lt_two_pow_bitLength
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_eq_of_readBit_eq
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_tail
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_zero
#print axioms Pnp4.Frontier.ContractExpansion.be_digit_step
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_natBEField_slice
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_zero_prefix
#print axioms Pnp4.Frontier.ContractExpansion.gammaBit_terminator
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_gammaBit_payload
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGamma_gammaBit
#print axioms Pnp4.Frontier.ContractExpansion.decodeGammaAux_gammaBit_from_at
#print axioms Pnp4.Frontier.ContractExpansion.prefixLength_lt_two_pow_idxWidth
#print axioms Pnp4.Frontier.ContractExpansion.readNatBE_encode_tag
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits_encode_x
#print axioms Pnp4.Frontier.ContractExpansion.sliceBits_encode_p
#print axioms Pnp4.Frontier.ContractExpansion.parse_encodeTreeMCSPPrefixFields_partial_obligation
#print axioms Pnp4.Frontier.ContractExpansion.parse_encodeTreeMCSPPrefixFields
#print axioms Pnp4.Frontier.ContractExpansion.parseTreeMCSPPrefixInput_length_convention
#check Pnp4.Frontier.ContractExpansion.treeMCSPRuntimeAwarePrefixParser

-- Semantic verifier for the prefix-extension language (NP-verifier track, PR 1).
#check @Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts
#check @Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts_correct
#check @Pnp4.Frontier.ContractExpansion.treePrefixSemanticAccepts_rejects_malformed
#check @Pnp4.Frontier.ContractExpansion.witnessBits_le_treeMCSPPrefixM
#check @Pnp4.Frontier.ContractExpansion.prefixAgreesBool
#check @Pnp4.Frontier.ContractExpansion.verifiesBool
#check @Pnp4.Frontier.ContractExpansion.extractWitness?

-- Verifier input-tape layout (NP-verifier track, Phase 6).
#check @Pnp4.Frontier.ContractExpansion.prefixVerifierInputLen
#check @Pnp4.Frontier.ContractExpansion.prefixVerifierInputLen_eq
#check @Pnp4.Frontier.ContractExpansion.prefixVerifierCertStart
#check @Pnp4.Frontier.ContractExpansion.prefixVerifierWitnessRegion_within_input
#check @Pnp4.Frontier.ContractExpansion.concatBitstring_left
#check @Pnp4.Frontier.ContractExpansion.concatBitstring_right
#check @Pnp4.Frontier.ContractExpansion.verifierTape_left
#check @Pnp4.Frontier.ContractExpansion.verifierTape_right
#check @Pnp4.Frontier.ContractExpansion.queryXOffset
#check @Pnp4.Frontier.ContractExpansion.queryIdxOffset
#check @Pnp4.Frontier.ContractExpansion.queryPrefixOffset
#check @Pnp4.Frontier.ContractExpansion.queryPrefixOffset_add_witnessBits
#check @Pnp4.Frontier.ContractExpansion.queryXOffset_le_treeMCSPPrefixM
#check @Pnp4.Frontier.ContractExpansion.queryIdxOffset_le_treeMCSPPrefixM
#check @Pnp4.Frontier.ContractExpansion.gammaLen_le_treeMCSPPrefixM
#check @Pnp4.Frontier.ContractExpansion.instanceSize_lt_treeMCSPPrefixM

-- Bounded-loop primitive (NP-verifier track, the row-iteration construct).
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.repeatProgram
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.repeatProgram_succ
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.repeatProgram_timeBound
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.repeatProgram_timeBound_le
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.repeatProgram_run_succ
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.repeatProgram_run_zero
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seqList_timeBound_sum
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seqList_timeBound_le
-- Compositional never-moves-left (head-bound tracking for the assembled seqList verifier).
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_neverMovesLeft
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.idleCS_neverMovesLeft
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seqList_neverMovesLeft
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seqList_runConfig_head_bounds
-- Single-step simulation of seq in the P1 region (run-simulation backbone for composition).
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_normal_phase
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_normal_state
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_normal_tape
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_normal_head
-- Handoff (P1→P2) and P2-region single-step simulation (completes seq single-step characterization).
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_accept_phase
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_accept_state
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_accept_tape
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P1_accept_head
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P2_phase
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P2_state
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P2_tape
#check @Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram.seq_stepConfig_P2_head
#check @Pnp3.Internal.PsubsetPpoly.TM.PhasedProgram.accepts_toTM
-- First verifier parse-phase program (NP-verifier track).
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_timeBound
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_transition_move
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_neverMovesLeft
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_stepConfig_phase
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_stepConfig_head
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_stepConfig_tape
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_stepConfig_state
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_runConfig_scan
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_accepts_eq_state
-- Tag-check semantic characterization (NP-verifier track): accepts ⇔ leading bits match the tag.
#check @Pnp4.Frontier.ContractExpansion.tagBitAt
#check @Pnp4.Frontier.ContractExpansion.natBitBE_tag_eq
#check @Pnp4.Frontier.ContractExpansion.tagCheckInputBit
#check @Pnp4.Frontier.ContractExpansion.tagMatchPrefix
#check @Pnp4.Frontier.ContractExpansion.tagMatchPrefix_succ
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_tape_read
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_runConfig_matched
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_accepts_eq_tagMatch
#check @Pnp4.Frontier.ContractExpansion.tagMatchPrefix_eq_true_iff
#check @Pnp4.Frontier.ContractExpansion.tagCheckProgram_accepts_iff
-- Gamma-decode phase, first brick: count-zeros scan program (locate the unary terminator).
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_timeBound
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_transition_move
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_neverMovesLeft
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_stepConfig_phase
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_stepConfig_state
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_stepConfig_tape
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_stepConfig_head
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_runConfig_scanning
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_runConfig_terminator
#check @Pnp4.Frontier.ContractExpansion.gammaZeroScanProgram_locates_gamma_terminator
-- M-compatible self-loop scan (back-edge construct, brick 0): fixed 2-phase structure.
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_timeBound
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_neverMovesLeft
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_scan_zero_phase
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_scan_zero_head
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_scan_zero_tape
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_runConfig_scanning
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_scan_one_phase
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_scan_one_head
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_scan_one_tape
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_runConfig_terminator
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_locates_gamma_terminator
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_stepConfig_done
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_runConfig_done
#check @Pnp4.Frontier.ContractExpansion.gammaSelfLoopScan_run_locates_terminator
-- Self-loop binary increment (brick 0: variable-width counter machinery).
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_timeBound
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_neverMovesLeft
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_stepConfig_carry_phase
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_stepConfig_carry_head
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_stepConfig_carry_tape
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_stepConfig_stop_phase
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_stepConfig_stop_head
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_stepConfig_stop_tape
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_runConfig_carry
#check @Pnp4.Frontier.ContractExpansion.selfLoopIncrement_runConfig_stop

end Tests
end Pnp4
