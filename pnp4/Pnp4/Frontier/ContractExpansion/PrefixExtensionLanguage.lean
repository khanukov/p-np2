import Pnp4.Frontier.SearchMCSPConcreteTargets

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- Local abbreviation to avoid ambiguity with Lean's root `BitVec`. -/
abbrev PrefixBitVec (n : Nat) := AlgorithmsToLowerBounds.BitVec n

/--
Parsed input for the R1-B prefix-extension language.

The actual byte-level serialization is intentionally not fixed here.  R1-B only
needs a small, auditable interface that exposes the fields used by the language:

* `tag` selects the prefix-language version;
* `n` is the underlying search-problem length;
* `x` is the target instance at that length;
* `i` is the active prefix length;
* `p` is a fixed-width prefix area, indexed by all witness coordinates;
* `pad` is inert padding used only by the parser/length convention.

Using a fixed-width `p` avoids dependent variable-length payloads in the
language interface: only coordinates `k < i` are semantically active.
-/
structure PrefixInput (problem : SearchMCSPCompressionProblem) where
  tag : Nat
  n : Nat
  x : PrefixBitVec (problem.instanceBits n)
  i : Nat
  p : PrefixBitVec (problem.witnessBits n)
  padBits : Nat
  pad : PrefixBitVec padBits

namespace PrefixInput

/-- The active prefix length must not exceed the target witness length. -/
def indexInRange {problem : SearchMCSPCompressionProblem}
    (input : PrefixInput problem) : Prop :=
  input.i ≤ problem.witnessBits input.n

/--
The full witness `w` agrees with the active prefix carried by `input`.

The inactive suffix of `input.p` is deliberately ignored here.  A concrete
parser may additionally constrain inactive bits for canonicity, but hardness
must not be hidden in those padding bits.
-/
def prefixAgreement {problem : SearchMCSPCompressionProblem}
    (input : PrefixInput problem)
    (w : PrefixBitVec (problem.witnessBits input.n)) : Prop :=
  ∀ k : Fin (problem.witnessBits input.n), (k : Nat) < input.i → w k = input.p k

/--
Prefix extendability for an already-parsed input.

This is the core R1-B predicate: a full target witness must extend the active
prefix and satisfy the target relation.  There is no solver, no nonuniform
advice, no lower-bound contradiction, and no endpoint witness in this predicate.
-/
def extendable {problem : SearchMCSPCompressionProblem}
    (input : PrefixInput problem) : Prop :=
  input.indexInRange ∧
    ∃ w : PrefixBitVec (problem.witnessBits input.n),
      input.prefixAgreement w ∧ problem.relation input.n input.x w

/-- Relation witnesses for parsed extendable inputs satisfy the target relation. -/
theorem relation_of_extendable {problem : SearchMCSPCompressionProblem}
    {input : PrefixInput problem}
    (h : input.extendable) :
    ∃ w : PrefixBitVec (problem.witnessBits input.n),
      input.prefixAgreement w ∧ problem.relation input.n input.x w :=
  h.2

/-- Parsed extendable inputs always have an in-range prefix index. -/
theorem indexInRange_of_extendable {problem : SearchMCSPCompressionProblem}
    {input : PrefixInput problem}
    (h : input.extendable) :
    input.indexInRange :=
  h.1

end PrefixInput

/--
Parser/length-policy interface for the prefix-extension language.

`parsePrefixInput` is intentionally a function rather than a relation, so
malformed behavior is deterministic.  The parser is responsible for checking the
chosen tag, length convention `M(n)`, field widths, and syntactic padding.  Its
proof fields record the R1-B contract without committing to a concrete codec in
this module.
-/
structure PrefixParser (problem : SearchMCSPCompressionProblem) where
  tag : Nat
  M : Nat → Nat
  parsePrefixInput : ∀ m : Nat, PrefixBitVec m → Option (PrefixInput problem)
  wellFormed : PrefixInput problem → Prop
  parse_wellFormed :
    ∀ {m : Nat} {y : PrefixBitVec m} {input : PrefixInput problem},
      parsePrefixInput m y = some input → wellFormed input
  parse_length :
    ∀ {m : Nat} {y : PrefixBitVec m} {input : PrefixInput problem},
      parsePrefixInput m y = some input → m = M input.n
  parse_tag :
    ∀ {m : Nat} {y : PrefixBitVec m} {input : PrefixInput problem},
      parsePrefixInput m y = some input → input.tag = tag
  wellFormed_index :
    ∀ {input : PrefixInput problem}, wellFormed input → input.indexInRange

/-- Compatibility alias using the exact parser name requested by the R1-B pack. -/
def parsePrefixInput {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    (m : Nat)
    (y : PrefixBitVec m) : Option (PrefixInput problem) :=
  parser.parsePrefixInput m y

/-- Compatibility alias using the exact well-formedness name requested by R1-B. -/
def wellFormed {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    (input : PrefixInput problem) : Prop :=
  parser.wellFormed input

/--
Prefix extendability of an encoded language input.

Malformed inputs are nonmembers because they have no parsed `PrefixInput`.  For
well-formed inputs, the only semantic content is existence of a full relation
witness extending the active prefix.
-/
def PrefixExtendable {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : PrefixBitVec m) : Prop :=
  ∃ input : PrefixInput problem,
    parser.parsePrefixInput m y = some input ∧ input.extendable

/--
The R1-B prefix-extension language associated with a parser.

`pnp3` languages are Boolean-valued.  Since the target relation is currently a
`Prop` and the repository has not yet supplied decidable codec/runtime data, the
Boolean coercion is classical.  This is acceptable for the language skeleton;
the NP-verifier theorem is intentionally not claimed below.
-/
noncomputable def PrefixExtensionLanguage {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Pnp3.ComplexityInterfaces.Language := by
  classical
  exact fun _m y => if PrefixExtendable parser y then true else false

/-- Boolean language membership is exactly the staged prefix-extendability predicate. -/
theorem PrefixExtensionLanguage_accept_iff {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    (m : Nat)
    (y : PrefixBitVec m) :
    PrefixExtensionLanguage parser m y = true ↔ PrefixExtendable parser y := by
  classical
  unfold PrefixExtensionLanguage
  by_cases h : PrefixExtendable parser y <;> simp [h]

/-- Malformed inputs, represented by parser failure, are nonmembers. -/
theorem PrefixExtensionLanguage_malformed_nonmember
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    {y : PrefixBitVec m}
    (hParse : parser.parsePrefixInput m y = none) :
    PrefixExtensionLanguage parser m y = false := by
  have hNot : ¬ PrefixExtendable parser y := by
    intro hExt
    rcases hExt with ⟨input, hSome, _hInput⟩
    rw [hParse] at hSome
    cases hSome
  classical
  unfold PrefixExtensionLanguage
  simp [hNot]

/-- Parsed inputs accepted by the language have the parser's canonical length. -/
theorem PrefixExtendable.length_eq
    {problem : SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    {m : Nat}
    {y : PrefixBitVec m}
    (h : PrefixExtendable parser y) :
    ∃ input : PrefixInput problem,
      parser.parsePrefixInput m y = some input ∧ m = parser.M input.n := by
  rcases h with ⟨input, hParse, _hInput⟩
  exact ⟨input, hParse, parser.parse_length hParse⟩

/-- Parsed inputs accepted by the language carry the parser's fixed tag. -/
theorem PrefixExtendable.tag_eq
    {problem : SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    {m : Nat}
    {y : PrefixBitVec m}
    (h : PrefixExtendable parser y) :
    ∃ input : PrefixInput problem,
      parser.parsePrefixInput m y = some input ∧ input.tag = parser.tag := by
  rcases h with ⟨input, hParse, _hInput⟩
  exact ⟨input, hParse, parser.parse_tag hParse⟩

/--
Audit record for the missing data needed to upgrade the skeleton to an honest
`NP` theorem.

For the tree-MCSP codec route, these fields correspond to the operator-visible
gaps from D0/D0.1: serialization, decoding, witness-length bounds, decidability
of the relation, and runtime of truth-table verification.  This structure is not
an endpoint and does not assert that `PrefixExtensionLanguage` is in `NP`.
-/
structure PrefixNPVerifierPlan (problem : SearchMCSPCompressionProblem)
    (parser : PrefixParser problem) where
  witnessLengthBoundAvailable : Prop
  parserRuntimeBoundAvailable : Prop
  relationDecidableAvailable : Prop
  relationRuntimeBoundAvailable : Prop
  codecSerializationAvailable : Prop
  codecDecodeAvailable : Prop
  truthTableVerificationRuntimeAvailable : Prop

/--
Audit-only statement of the verifier budget still needed before proving `NP`.

This is a proposition-valued projection, not a proof that the codec/runtime gaps
have been discharged.
-/
def PrefixNPVerifierPlan.codecRequirements
    {problem : SearchMCSPCompressionProblem}
    {parser : PrefixParser problem}
    (plan : PrefixNPVerifierPlan problem parser) : Prop :=
  plan.codecSerializationAvailable ∧
    plan.codecDecodeAvailable ∧
      plan.truthTableVerificationRuntimeAvailable

end ContractExpansion
end Frontier
end Pnp4
