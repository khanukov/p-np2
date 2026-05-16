import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
The concrete tree-MCSP search problem used by the R1-B1 prefix-language budget
work, with the threshold and witness encoding kept explicit.

R1-B1 deliberately does **not** pick a fake threshold or a fake encoding.  The
current repository exposes tree-MCSP witnesses through the parameterized
`TreeMCSPSearchWitnessEncoding` interface, so every parser or verifier-budget
artifact below remains parameterized by exactly those inputs.
-/
abbrev TreeMCSPPrefixProblem
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) :
    SearchMCSPCompressionProblem :=
  treeMCSPSearchProblem threshold encoding

/--
Serialization data sufficient to obtain a `PrefixParser` for the explicit
`treeMCSPSearchProblem threshold encoding` target.

This is intentionally an interface, not a hidden parser implementation.  The
R1-B module already fixed the semantic shape of parsed inputs, but the current
codebase has no byte-level codec for the tuple `⟨tag,n,x,i,p,pad⟩`.  R1-B1 can
therefore make the missing serialization boundary precise without pretending
that parsing, padding validation, or a length convention has been discharged.
-/
structure TreeMCSPPrefixParserSpec
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) where
  /-- Domain separator for the tree-MCSP prefix language. -/
  tag : Nat
  /-- Intended ambient length convention for target length `n`. -/
  M : Nat → Nat
  /-- Actual parser supplied by a future codec/serialization implementation. -/
  parse :
    ∀ {m : Nat},
      PrefixBitVec m →
        Option (PrefixInput (TreeMCSPPrefixProblem threshold encoding) m)
  /-- Audit statement for the tuple encoding `⟨tag,n,x,i,p,pad⟩`. -/
  tuple_codec_specified : Prop
  /-- Audit statement that `parse = none` is exactly the malformed-input path. -/
  malformed_inputs_rejected : Prop
  /-- Audit statement that accepted inputs obey the advertised `M(n)` policy. -/
  length_convention_sound : Prop

/--
Parameterized tree-MCSP prefix parser.

A concrete worker may instantiate `TreeMCSPPrefixParserSpec` once a real
serialization of `⟨tag,n,x,i,p,pad⟩` is available.  This definition contributes
no hardness assumption and no endpoint: it simply exposes the parser expected
by `PrefixExtensionLanguage` at the tree-MCSP target.
-/
def treeMCSPPrefixParser
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (spec : TreeMCSPPrefixParserSpec threshold encoding) :
    PrefixParser (TreeMCSPPrefixProblem threshold encoding) where
  tag := spec.tag
  M := spec.M
  parse := spec.parse

/-- The parameterized parser delegates parsing exactly to its specification. -/
theorem treeMCSPPrefixParser_parse_eq
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (spec : TreeMCSPPrefixParserSpec threshold encoding)
    {m : Nat}
    (y : PrefixBitVec m) :
    parsePrefixInput (treeMCSPPrefixParser spec) y = spec.parse y :=
  rfl

/--
Explicit relation-decidability assumption for the parameterized tree-MCSP
witness encoding.

The base `TreeMCSPSearchWitnessEncoding` interface stores `verifies` as a
`Prop` and does not require a computable decision procedure.  R1-B1 therefore
keeps decidability as a named input instead of manufacturing it via classical
choice.
-/
structure TreeMCSPSearchRelationDecidable
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) : Type where
  decidable_relation :
    ∀ n : Nat,
      ∀ x : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).instanceBits n),
        ∀ w : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).witnessBits n),
          Decidable ((TreeMCSPPrefixProblem threshold encoding).relation n x w)

/--
Tree-MCSP relation decidability follows exactly from an explicit decidability
provider for the witness encoding.

This is the honest R1-B1 decidability landing: without such a provider, the
current repository surface is only `Prop`-level and does not expose a verifier
algorithm for `encoding.verifies`.
-/
def treeMCSPSearchRelation_decidable_of_encoding_decidable
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (h : TreeMCSPSearchRelationDecidable threshold encoding)
    (n : Nat)
    (x : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).instanceBits n))
    (w : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).witnessBits n)) :
    Decidable ((TreeMCSPPrefixProblem threshold encoding).relation n x w) :=
  h.decidable_relation n x w

/--
Core R1-B1 verifier-budget obligations for a tree-MCSP prefix parser.

This structure is intentionally **not** a `PrefixExtensionNPVerifierBudget`.
The remaining runtime fields are kept as obligations and are not filled with
`True`.  A future worker may convert these obligations into a full
`PrefixExtensionNPVerifierBudget parser` only after the parser and relation
runtime facts are proved in the repository's eventual polynomial-time model.
-/
structure TreeMCSPPrefixVerifierCoreObligations
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (parser : PrefixParser (TreeMCSPPrefixProblem threshold encoding)) : Type where
  /-- A real polynomial-time parser theorem for the chosen serialization. -/
  parser_polynomial_time : Prop
  /-- A computable decision procedure for the concrete search relation. -/
  relation_decidable :
    ∀ n : Nat,
      ∀ x : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).instanceBits n),
        ∀ w : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).witnessBits n),
          Decidable ((TreeMCSPPrefixProblem threshold encoding).relation n x w)
  /-- A real polynomial-time theorem for checking the concrete relation. -/
  relation_polynomial_time : Prop
  /-- A real polynomial witness-length bound for full target witnesses. -/
  witness_length_polynomial : Prop

/--
Extract the decidability component from the explicit core obligations.

This theorem is useful for downstream workers because it shows precisely which
non-runtime part of the staged budget can be reused once supplied, while still
not claiming any polynomial-time verifier theorem.
-/
def treeMCSPPrefixVerifierCore_relationDecidable
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    {parser : PrefixParser (TreeMCSPPrefixProblem threshold encoding)}
    (obligations : TreeMCSPPrefixVerifierCoreObligations parser)
    (n : Nat)
    (x : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).instanceBits n))
    (w : PrefixBitVec ((TreeMCSPPrefixProblem threshold encoding).witnessBits n)) :
    Decidable ((TreeMCSPPrefixProblem threshold encoding).relation n x w) :=
  obligations.relation_decidable n x w

/--
R1-B1 blocker classification for the current repository surface.

`localIssue` covers ordinary implementation work such as a missing parser or
missing import.  `globalInterfaceIssue` records the stronger obstruction found
when the available search-MCSP interfaces are too `Prop`-level or lack a
polynomial-time verifier formalism.
-/
inductive R1B1VerifierBudgetBlocker where
  | localIssue
  | globalInterfaceIssue
  deriving DecidableEq, Repr

/--
The current parameterized tree-MCSP relation is blocked at the global interface
level unless an explicit `TreeMCSPSearchRelationDecidable` provider is supplied.

This is an audit marker, not a theorem that proves impossibility: it records the
concrete reason R1-B1 cannot honestly construct `relation_decidable` from the
existing `TreeMCSPSearchWitnessEncoding` fields alone.
-/
def treeMCSPRelationDecidabilityBlocker : R1B1VerifierBudgetBlocker :=
  R1B1VerifierBudgetBlocker.globalInterfaceIssue

end ContractExpansion
end Frontier
end Pnp4
