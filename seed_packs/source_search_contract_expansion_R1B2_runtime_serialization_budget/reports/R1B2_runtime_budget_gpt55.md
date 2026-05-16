# R1-B2 Runtime / Serialization Budget Report — GPT-5.5

## Executive summary

Outcome: **REPORT_LANDED**.

R1-B2 can plausibly make the R1-B / R1-B1 prefix-extension language an NP
language, but **not with the current generic codec and parser surfaces alone**.
The load-bearing runtime distinction resolves as follows:

- `TreeCircuitWitnessCodec.verifiesDecidable` is **exponential in the target
  parameter `n`** because it decides `ComputesTruthTable` by finite universal
  quantification over all `n`-bit assignments.
- This enumeration is **not automatically disqualifying for NP membership** if
  the ambient encoded input length `M(n)` includes the full truth-table instance
  length `tableLen n = 2^n`; then the assignment loop has at most `tableLen n`
  iterations, so the loop count is linear in the truth-table component of the
  input.
- The current repository still lacks enough concrete data to conclude a real
  polynomial-time verifier: `TreeCircuitWitnessCodec.decode` and
  `codec.witnessBits` are abstract, the bit-level parser is not fixed, and
  `PrefixExtensionNPVerifierBudget` is a Prop-level checklist rather than a
  bridge to the canonical TM-based `NP` definition.

Therefore this report does **not** claim `PrefixExtensionLanguage_in_NP` and does
**not** instantiate `PrefixExtensionNPVerifierBudget` with placeholder fields.
It records the exact local assumptions and global formalism needed for a later
Lean landing.

## 1. What was attempted

I inspected the R1-B2 seed-pack instructions and the R1-A/R1-B/R1-B1 Lean
surfaces to determine whether the prefix-extension language can honestly be
shown to be in NP under a concrete runtime and serialization budget.

The attempt focused on four questions:

1. What ambient length convention `M(n)` is sufficient for tree-MCSP prefix
   instances?
2. Does the existing parser surface define a concrete parser, or only a staged
   interface?
3. Is the codec relation polynomial-time when measured against `M(n)` rather
   than `n`?
4. Can the repository currently connect local runtime predicates to
   `ComplexityInterfaces.NP`?

## 2. Exact signatures inspected

### Prefix-extension language and budget surface

`PrefixInput` stores the decoded fields `tag`, `n`, `x`, `i`, prefix payload
`p`, and padding; in particular, `x` has type
`PrefixBitVec (problem.instanceBits n)` and `p` has type `PrefixBitVec i`.
The invariant `prefixLength_le : i ≤ problem.witnessBits n` is already present
and is the right type-level guard for prefix agreement.

Relevant signatures:

```lean
structure PrefixInput (problem : SearchMCSPCompressionProblem) (m : Nat) where
  tag : Nat
  n : Nat
  x : PrefixBitVec (problem.instanceBits n)
  i : Nat
  prefixLength_le : i ≤ problem.witnessBits n
  p : PrefixBitVec i
  padBits : Nat
  pad : PrefixBitVec padBits
```

```lean
structure PrefixParser (problem : SearchMCSPCompressionProblem) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)
```

```lean
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
```

### R1-B1 parser and codec relation surface

R1-B1 exposes `treeMCSPPrefixParser` as a constructor from an explicit `tag`,
`M`, and `parse`, and it exposes `TreeMCSPPrefixParserObligations` as a staging
record. This is not a concrete serialization.

Relevant signatures:

```lean
def treeMCSPPrefixParser
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (tag : Nat)
    (M : Nat → Nat)
    (parse : ∀ {m : Nat},
      PrefixBitVec m →
        Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)) :
    PrefixParser (treeMCSPSearchProblem threshold encoding)
```

```lean
structure TreeMCSPPrefixParserObligations
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat},
    PrefixBitVec m →
      Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)
  parser_polynomial_time : Prop
  malformed_inputs_rejected_by_parse : Prop
  length_convention_matches_M : Prop
```

The codec relation is also abstract in the decode and witness-size components:

```lean
structure TreeCircuitWitnessCodec
    (threshold : Nat → Nat) where
  witnessBits : Nat → Nat
  encode :
    ∀ n : Nat,
      Pnp3.Models.Circuit n →
        AlgorithmsToLowerBounds.BitVec (witnessBits n)
  decode :
    ∀ n : Nat,
      AlgorithmsToLowerBounds.BitVec (witnessBits n) →
        Option (Pnp3.Models.Circuit n)
  decode_encode :
    ∀ n : Nat, ∀ c : Pnp3.Models.Circuit n,
      Pnp3.Models.Circuit.size c ≤ threshold n →
        decode n (encode n c) = some c
```

```lean
def TreeCircuitWitnessCodec.verifies
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : AlgorithmsToLowerBounds.BitVec (codec.witnessBits n)) : Prop :=
  ∃ c : Pnp3.Models.Circuit n,
    codec.decode n w = some c ∧
      Pnp3.Models.Circuit.size c ≤ threshold n ∧
        ComputesTruthTable treeCircuitClass c tt
```

R1-B1 proves only decidability:

```lean
def TreeCircuitWitnessCodec.verifiesDecidable
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) :
    Decidable (codec.verifies n tt w)
```

The deciding step uses decidability for `ComputesTruthTable`, whose definition
quantifies over every assignment:

```lean
def ComputesTruthTable
    (C : CircuitFamilyClass)
    {n : Nat}
    (c : C.Family n)
    (tt : TruthTable n) : Prop :=
  ∀ x : BitVec n, C.eval c x = truthTableFunction tt x
```

### Tree-MCSP length and NP formalism

Tree-MCSP instances use the existing truth-table length:

```lean
abbrev TruthTable (n : Nat) := Pnp3.Core.BitVec (Pnp3.Models.Partial.tableLen n)
```

```lean
def treeMCSPSearchProblem
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) :
    SearchMCSPCompressionProblem where
  instanceBits := fun n => Pnp3.Models.Partial.tableLen n
  witnessBits := encoding.witnessBits
  promise := fun n tt => treeMCSPPredicate n (threshold n) tt
  relation := encoding.verifies
  totalOnPromise := encoding.complete
```

`tableLen` is exactly exponential in `n`:

```lean
def tableLen (n : Nat) : Nat := Nat.pow 2 n
```

The repository's canonical `NP` is TM-based, not a local Prop checklist:

```lean
def NP_TM (L : Language) : Prop :=
  ∃ (M : Internal.PsubsetPpoly.TM.{0}) (c k : Nat),
    (∀ n,
      M.runTime (n + certificateLength n k) ≤
        (n + certificateLength n k) ^ c + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (certificateLength n k),
          Internal.PsubsetPpoly.TM.accepts
              (M := M)
              (n := n + certificateLength n k)
              (concatBitstring x w) = true)
```

## 3. Ambient length convention status

### Recommended R1-B2 convention

For a tree-MCSP prefix input at target parameter `n`, use an ambient length of
the following shape:

```text
M(n) = tagBits
     + nCodeBits(n)
     + iCodeBits(n)
     + problem.instanceBits n
     + problem.witnessBits n
     + padBits(n)
```

For the tree-MCSP target:

```text
problem.instanceBits n = tableLen n = 2^n.
```

A minimal useful convention therefore requires:

```text
tableLen n ≤ M(n).
```

This is immediate if `M(n)` includes the full `x : TruthTable n` component as a
contiguous payload and all other components have nonnegative length.

### Consequence for the all-assignments loop

The truth-table agreement check enumerates all `x : BitVec n`, i.e. `2^n`
assignments. This is exponential in `n`, but the loop count is bounded by the
ambient input length when `tableLen n ≤ M(n)`:

```text
2^n = tableLen n ≤ M(n).
```

So the enumeration count itself is **linear in `M(n)`**, not exponential in the
actual encoded input length.

### Remaining arithmetic obligations

A future Lean module can land small arithmetic facts such as:

```lean
def treeMCSPPrefixAmbientLength
    (witnessBits overhead padBits : Nat → Nat) (n : Nat) : Nat :=
  overhead n + Pnp3.Models.Partial.tableLen n + witnessBits n + padBits n
```

with lemmas of the form:

```lean
lemma tableLen_le_treeMCSPPrefixAmbientLength
    (witnessBits overhead padBits : Nat → Nat) (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength witnessBits overhead padBits n
```

This arithmetic is local and should be straightforward once the exact `M(n)`
shape is chosen.

## 4. Parser serialization status

No concrete parser currently exists for R1-B2. The repository has only the
`PrefixParser` interface and the R1-B1 `treeMCSPPrefixParser` constructor from
an externally supplied parse function.

A concrete parser still needs to specify all of the following bit-level choices:

- tag layout and tag width;
- self-delimiting or fixed-width encoding of `n`;
- encoding of `i`, including proof/guard that `i ≤ witnessBits n`;
- exact slice occupied by `x : BitVec (tableLen n)`;
- exact slice occupied by `p : BitVec i`;
- whether the ambient record reserves a full witness-width prefix area or uses a
  variable prefix slice plus padding;
- padding policy, including whether padding must be all-zero or ignored;
- malformed-input behavior.

The existing R1-B theorem `PrefixExtensionLanguage_rejects_malformed` is already
the right semantic endpoint for parser failures: if `parsePrefixInput parser y =
none`, then the language rejects. What is missing is the concrete theorem that
malformed byte strings really make the concrete parser return `none`.

Precise parser theorem list for a later Lean landing:

1. `parseTreeMCSPPrefix_length_sound`:
   if `parseTreeMCSPPrefix y = some input`, then the ambient length is compatible
   with the chosen `M(input.n)` convention.
2. `parseTreeMCSPPrefix_tag_sound`:
   successful parsing implies the decoded tag is the R1-B2 tag.
3. `parseTreeMCSPPrefix_fields_sound`:
   successful parsing recovers `n`, `x`, `i`, `p`, and `pad` from the fixed
   slices specified by the serialization convention.
4. `parseTreeMCSPPrefix_prefixLength_le`:
   successful parsing establishes `i ≤ codec.witnessBits n`.
5. `parseTreeMCSPPrefix_malformed_none`:
   tag mismatch, length mismatch, out-of-range `i`, or invalid padding returns
   `none`.
6. `parseTreeMCSPPrefix_polynomial_time_in_M`:
   the parser scans and slices at most `M(n)` bits plus polynomial overhead.

## 5. Relation runtime status

### What R1-B1 already gives

R1-B1 gives a decidability theorem for the codec relation. It does not give a
runtime theorem. This is an honest separation: a finite exhaustive truth-table
check is decidable, but decidability is weaker than polynomial-time
verification.

### Runtime decomposition for `codec.verifies n tt w`

For a concrete codec, verification decomposes into:

1. Decode `w` into an optional tree circuit `c`.
2. If decode fails, reject.
3. Compute/check `Circuit.size c ≤ threshold n`.
4. For every assignment `a : BitVec n`, evaluate `c a` and compare with
   `truthTableFunction tt a`.

The fourth step performs `tableLen n = 2^n` iterations. Measured in `n`, this is
exponential. Measured in an ambient input length `M(n)` that includes the full
truth table, this loop has at most `M(n)` iterations.

### Conditional polynomial-in-`M(n)` statement

The relation is plausibly polynomial-time in `M(n)` under the following local
assumptions:

1. `tableLen n ≤ M(n)`.
2. `threshold n ≤ M(n)^a + a` for some fixed exponent/constant `a`.
3. The decoded circuit representation has size bounded by `threshold n` after
   the size check, and evaluating a tree circuit costs polynomial time in its
   syntax size.
4. `codec.decode n w` runs in polynomial time in `M(n)`.
5. Truth-table lookup `truthTableFunction tt a` is polynomial time in `M(n)`.

Under those assumptions, the all-assignments part has the schematic bound:

```text
number of assignments × per-assignment cost
≤ tableLen n × poly(threshold n + n + M(n))
≤ M(n) × poly(M(n))
= poly(M(n)).
```

This is the central R1-B2 resolution: the truth-table loop is not the global
obstruction if `M(n)` really contains the truth table. The remaining blockers are
codec concreteness and the absence of a formal runtime bridge.

### What cannot be proved for the current generic codec

For arbitrary `TreeCircuitWitnessCodec`, no polynomial-time theorem follows.
The fields `decode` and `witnessBits` are arbitrary functions with no cost or
size guarantees. The type of `decode` alone permits computationally expensive or
non-canonical decoders, even though the proof-level `decode_encode` law ensures
completeness for small circuits.

Therefore a valid R1-B2 Lean module must either:

- instantiate a concrete codec and prove decode/runtime/length bounds for it; or
- define a runtime-aware codec record with explicit fields for decode cost,
  witness length, and evaluation/serialization compatibility.

It must not use `True` placeholders for `relation_polynomial_time`.

## 6. Witness-length status

For the NP verifier, the certificate should contain a full target witness `w`
for the prefix-extension predicate. Therefore the witness length is controlled
by:

```text
codec.witnessBits n
```

For a tree-circuit codec, a natural witness encoding should be polynomial in the
size of the decoded circuit, hence polynomial in `threshold n`, times logarithmic
or fixed-width overhead for variable indices and tags. A typical target
assumption would be:

```text
codec.witnessBits n ≤ M(n)^b + b
```

or more structurally:

```text
codec.witnessBits n ≤ poly(threshold n + n)
threshold n ≤ poly(M(n))
```

However, the current `TreeCircuitWitnessCodec` record does not contain such a
bound. Therefore `witness_length_polynomial` is blocked locally on a concrete
codec bound, not on the truth-table enumeration issue.

## 7. Polynomial-time formalism status

The repository already has a canonical `NP` definition, namely `NP_TM`, where a
single TM verifier must run in polynomial time in the combined input/certificate
length. This is the correct global target.

What is missing for R1-B2 is a reusable local compiler or bridge from the staged
Prop-level budget fields to `NP_TM`. In particular, the following local
predicates would be useful but are not yet present as executable bridges:

```lean
/-- Parser runs in polynomial time in the ambient input length. -/
def ParserPolyTime
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Prop :=
  -- should be backed by an actual TM/algorithmic model, not `True`
  ...

/-- Relation verifier runs in polynomial time in ambient input plus witness. -/
def RelationPolyTime
    (problem : SearchMCSPCompressionProblem) : Prop :=
  -- should quantify over a concrete verifier algorithm/TM
  ...

/-- Target witnesses have polynomial length in the ambient input convention. -/
def WitnessLengthPoly
    (problem : SearchMCSPCompressionProblem)
    (M : Nat → Nat) : Prop :=
  ∃ c, ∀ n, problem.witnessBits n ≤ M n ^ c + c
```

The critical caveat is that `ParserPolyTime` and `RelationPolyTime` should not
be inert Prop labels. To prove `ComplexityInterfaces.NP`, they must either be
implemented directly as TMs or come with a theorem that compiles the local
algorithmic model to the existing TM model.

## 8. Proposed R1-B2 budget object

A useful non-fake R1-B2 record should separate arithmetic facts, codec facts,
and global compiler facts. For example:

```lean
structure TreeMCSPPrefixRuntimeBudget
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (M : Nat → Nat) : Type where
  tableLen_le_M : ∀ n, Pnp3.Models.Partial.tableLen n ≤ M n
  threshold_poly_in_M : ∃ c, ∀ n, threshold n ≤ M n ^ c + c
  witnessBits_poly_in_M : ∃ c, ∀ n, codec.witnessBits n ≤ M n ^ c + c
  decode_polynomial_time_in_M : Prop
  parser_polynomial_time_in_M : Prop
  circuit_eval_polynomial_time_in_size : Prop
  relation_polynomial_time_in_M : Prop
```

This record is intentionally not an NP theorem. It exposes which fields are
real arithmetic theorems and which fields still require a concrete computational
model.

## 9. Local vs global obstruction

### Local blockers

- No fixed bit-level serialization for `tag`, `n`, `x`, `i`, `p`, and `pad`.
- No concrete `parseTreeMCSPPrefix` implementation.
- No concrete `TreeCircuitWitnessCodec` with a proved polynomial witness-size
  bound.
- No proved runtime bound for `codec.decode`.
- No formal bound connecting `threshold n` to `M(n)`.

### Global blockers

- `PrefixExtensionNPVerifierBudget` is a checklist of Prop fields, not a theorem
  that constructs a verifier TM for `ComplexityInterfaces.NP`.
- The repository does not yet expose a local algorithm-cost formalism that can
  compile parser/relation runtime proofs into `NP_TM`.

The largest mathematical misconception is now resolved: exhaustive truth-table
verification is exponential in `n`, but it can be polynomial in the actual input
length `M(n)` for truth-table-encoded MCSP. The remaining problem is formal and
engineering-heavy rather than a fatal runtime asymptotic contradiction.

## 10. What R1-C must know

R1-C must not assume an NP theorem for `PrefixExtensionLanguage` until R1-B2 or a
successor lands a real parser/codec/runtime bridge. In particular, R1-C may rely
only on a budget object that explicitly includes:

- `tableLen n ≤ M(n)`;
- polynomial bound on `threshold n` in `M(n)`;
- polynomial bound on `codec.witnessBits n` in `M(n)`;
- concrete parser correctness and malformed-input rejection;
- polynomial decode and relation-verifier runtime;
- a bridge from local runtime facts to the TM-based `NP` definition.

R1-C must not use `PpolyDAG L → BoundedSearchSolver` or any extraction step from
this R1-B2 report. This report is only about the NP-verifier budget.

## 11. Recommended next move

Recommended next seed/task: **R1-B2a — concrete runtime-aware codec and parser
interface**.

Scope:

1. Define a concrete or parameterized `M(n)` with an explicit `tableLen_le_M`
   lemma.
2. Introduce a runtime-aware codec refinement extending `TreeCircuitWitnessCodec`
   with non-placeholder fields:
   - `witnessBits_poly_in_M`;
   - `decode_polynomial_time_in_M`;
   - circuit syntax-size bound for decoded witnesses.
3. Define a parser theorem list or a concrete `parseTreeMCSPPrefix` for the
   selected serialization.
4. Separately decide whether to build a direct TM verifier for the concrete
   serialization or introduce a small verified algorithm-cost layer that compiles
   to `NP_TM`.

Do not open R1-C until at least these R1-B2a fields have non-placeholder
inhabitants.
