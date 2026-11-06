import Pnp4.Frontier.SearchMCSPConcreteTargets

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- Local spelling to avoid clashes with other imported `BitVec` names. -/
abbrev PrefixBitVec (n : Nat) := AlgorithmsToLowerBounds.BitVec n

/--
Parsed input for the R1-B prefix-extension language.

The ambient language input has length `m`; parsing is intentionally factored out
because R1-B is about the mathematical contract, not a committed byte-level
serialization.  A successful parser must recover exactly the fields requested
by the seed pack:

* `tag`: a version/domain separator for this language;
* `n`: the underlying search-target length;
* `x`: the target instance, already coerced to `problem.instanceBits n` bits;
* `i`: the active prefix length;
* `p`: the prefix payload on the first `i` witness coordinates;
* `pad`: padding bits used only to realize the chosen ambient length convention.

The bound `prefixLength_le` is the crucial well-formedness invariant: it makes
prefix comparison with a full witness type-safe and prevents malformed encodings
from smuggling out-of-range witness coordinates into the language predicate.
-/
structure PrefixInput
    (problem : SearchMCSPCompressionProblem)
    (m : Nat) where
  tag : Nat
  n : Nat
  x : PrefixBitVec (problem.instanceBits n)
  i : Nat
  prefixLength_le : i ≤ problem.witnessBits n
  p : PrefixBitVec i
  padBits : Nat
  pad : PrefixBitVec padBits

namespace PrefixInput

/--
The decoded prefix agrees with a full witness.

Only coordinates below the active prefix length `i` are checked.  Any inactive
padding carried by the parser is deliberately ignored here; parser
well-formedness, not semantic hardness, is responsible for rejecting bad padding.
-/
def prefixAgrees
    {problem : SearchMCSPCompressionProblem}
    {m : Nat}
    (input : PrefixInput problem m)
    (w : PrefixBitVec (problem.witnessBits input.n)) : Prop :=
  ∀ k : Fin input.i,
    w ⟨k.1, Nat.lt_of_lt_of_le k.2 input.prefixLength_le⟩ = input.p k

end PrefixInput

/--
Parser interface for the prefix-extension language.

`M` records the intended single-length-per-target convention from the seed pack.
The parser remains abstract in this module: later serialization work may prove
that `parse` accepts exactly strings of length `M n` with the right tag and
padding.  R1-B only needs the parser boundary so malformed strings can be made
nonmembers without hiding a promise or lower-bound assumption.
-/
structure PrefixParser
    (problem : SearchMCSPCompressionProblem) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)

/-- The staged parser entry point named in the R1-B seed pack. -/
def parsePrefixInput
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : PrefixBitVec m) : Option (PrefixInput problem m) :=
  parser.parse y

/-- A string is well-formed exactly when the parser accepts it. -/
def wellFormed
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : PrefixBitVec m) : Prop :=
  ∃ input : PrefixInput problem m, parsePrefixInput parser y = some input

/--
Semantic prefix extendability for an already parsed input.

This is the core R1-B predicate.  It uses only the search problem relation and a
full witness extending the decoded prefix; it does not mention `PpolyDAG`, a
bounded search solver, `target.noBoundedSolver`, or any endpoint object.
-/
def PrefixExtendableInput
    {problem : SearchMCSPCompressionProblem}
    {m : Nat}
    (input : PrefixInput problem m) : Prop :=
  ∃ w : PrefixBitVec (problem.witnessBits input.n),
    input.prefixAgrees w ∧ problem.relation input.n input.x w

/-- Prefix extendability for an ambient language input. -/
def PrefixExtendable
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : PrefixBitVec m) : Prop :=
  ∃ input : PrefixInput problem m,
    parsePrefixInput parser y = some input ∧ PrefixExtendableInput input

/--
The R1-B prefix-extension language as a pnp3 language.

The boolean wrapper uses classical decidability for the staged semantic
predicate.  This is acceptable for the R1-B skeleton because the actual NP
verifier proof is intentionally separated into explicit parser/codec/runtime
budgets below rather than being hidden in this definition.
-/
noncomputable def PrefixExtensionLanguage
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Pnp3.ComplexityInterfaces.Language := by
  classical
  exact fun _m y => if PrefixExtendable parser y then true else false

/-- The language accepts exactly the prefix-extendable parsed inputs. -/
theorem PrefixExtensionLanguage_accepts_iff
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : PrefixBitVec m) :
    PrefixExtensionLanguage parser m y = true ↔ PrefixExtendable parser y := by
  classical
  by_cases h : PrefixExtendable parser y
  · unfold PrefixExtensionLanguage
    simp [h]
  · unfold PrefixExtensionLanguage
    simp [h]

/-- Malformed inputs, represented by parser failure, are nonmembers. -/
theorem PrefixExtensionLanguage_rejects_malformed
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    (y : PrefixBitVec m)
    (hparse : parsePrefixInput parser y = none) :
    PrefixExtensionLanguage parser m y = false := by
  classical
  have hNot : ¬ PrefixExtendable parser y := by
    intro hExt
    rcases hExt with ⟨input, hInput, _hWitness⟩
    rw [hparse] at hInput
    cases hInput
  unfold PrefixExtensionLanguage
  simp [hNot]

/-- A parsed prefix and a full relation witness force language membership. -/
theorem PrefixExtensionLanguage_accepts_of_parse_and_witness
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    {m : Nat}
    {y : PrefixBitVec m}
    {input : PrefixInput problem m}
    (hparse : parsePrefixInput parser y = some input)
    {w : PrefixBitVec (problem.witnessBits input.n)}
    (hagrees : input.prefixAgrees w)
    (hrel : problem.relation input.n input.x w) :
    PrefixExtensionLanguage parser m y = true := by
  classical
  have hExt : PrefixExtendable parser y :=
    ⟨input, hparse, ⟨w, hagrees, hrel⟩⟩
  unfold PrefixExtensionLanguage
  exact if_pos hExt

/--
Explicit budget checklist for turning `PrefixExtensionLanguage` into an NP
language theorem.

The present repository exposes `TreeMCSPSearchWitnessEncoding` and
`TreeCircuitWitnessCodec` as relation-level interfaces, but it does not yet
provide all parser and runtime facts required for a theorem of the form
`PrefixExtensionLanguage_in_NP`.  Keeping these facts as named fields prevents
R1-B from hiding verifier work inside a promise or inside classical
noncomputability.
-/
structure PrefixExtensionNPVerifierBudget
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Type where
  parser_polynomial_time : Prop
  witness_length_polynomial : Prop
  prefix_agreement_polynomial_time : Prop
  relation_decidable : Prop
  relation_polynomial_time : Prop
  codec_serialization_available : Prop
  codec_decode_available : Prop
  codec_witness_length_bound : Prop
  truth_table_verification_runtime : Prop

/--
Audit-local statement of the intended NP verifier, kept as data rather than as
an unproved theorem.

A future worker may replace this plan by an actual
`PrefixExtensionLanguage_in_NP` theorem only after instantiating every budget
field above with concrete parser, codec, and runtime proofs.
-/
structure PrefixExtensionNPVerifierPlan
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Type where
  budget : PrefixExtensionNPVerifierBudget parser
  witness_is_full_target_witness : Prop
  verifier_checks_prefix_agreement : Prop
  verifier_checks_problem_relation : Prop

end ContractExpansion
end Frontier
end Pnp4
