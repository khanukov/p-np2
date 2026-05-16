# R1-B2 Runtime Budget Report — gpt55

**Slot:** R1-B2 — runtime / serialization / NP verifier budget  
**Handle:** gpt55  
**Outcome:** REPORT_LANDED  
**Classification:** Infrastructure / contract-expansion staging  
**Scope:** R1-B2 only; R1-C remains gated.

## Executive verdict

`PrefixExtensionLanguage` cannot honestly be promoted to a repository `NP`
theorem in the current state of the tree-MCSP prefix-extension stack.

The important distinction is now clear:

- `TreeCircuitWitnessCodec.verifiesDecidable` performs truth-table agreement by
  finite universal quantification over `BitVec n`, so the direct verifier is
  exponential in the target parameter `n`.
- For the tree-MCSP target, the instance component has length
  `problem.instanceBits n = tableLen n = 2^n`. Therefore the same truth-table
  scan can be polynomial in an ambient input length `M(n)` whenever the
  serialization convention proves `tableLen n ≤ M(n)` and the remaining work is
  polynomial in `M(n)`.

This is not enough for `NP`: pnp3's exposed `NP` is `NP_TM`, a concrete
Turing-machine verifier with polynomial runtime on the concatenated input and
certificate. The current R1-B/R1-B1 interfaces expose Prop-valued parser and
runtime fields, an abstract codec `decode`, and an abstract witness length
`codec.witnessBits`; they do not provide a TM-level parser/verifier or runtime
compiler from those Lean functions and propositions.

## Required signatures inspected

### Prefix-extension language surface

The R1-B surface defines parsed inputs as:

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

and the parser boundary as:

```lean
structure PrefixParser (problem : SearchMCSPCompressionProblem) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)
```

The language is intentionally semantic: a parsed input is accepted when there
exists a full target witness that extends the prefix and satisfies
`problem.relation`. The module already contains malformed-input rejection via
parser failure.

### R1-B verifier-budget surface

R1-B records, but does not prove, the necessary NP-verifier budget fields:

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

These fields are correctly not filled by `True` placeholders.

### R1-B1 tree-MCSP parser and decidability surface

R1-B1 provides a staged constructor:

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

It also proves relation decidability for codec-induced encodings, but the proof
uses finite enumeration rather than a runtime theorem:

```lean
def TreeCircuitWitnessCodec.verifiesDecidable
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) :
    Decidable (codec.verifies n tt w)
```

Inside that proof, `ComputesTruthTable` is unfolded and decided by
`Fintype.decidableForallFintype`, i.e. by quantifying over all `BitVec n`.

### Tree-MCSP concrete target surface

The concrete tree-MCSP search problem sets:

```lean
instanceBits := fun n => Pnp3.Models.Partial.tableLen n
witnessBits := encoding.witnessBits
relation := encoding.verifies
```

and `tableLen n` is defined as `2^n` in the pnp3 partial truth-table model.

The codec interface is deliberately abstract:

```lean
structure TreeCircuitWitnessCodec (threshold : Nat → Nat) where
  witnessBits : Nat → Nat
  encode : ∀ n : Nat, Pnp3.Models.Circuit n → BitVec (witnessBits n)
  decode : ∀ n : Nat, BitVec (witnessBits n) → Option (Pnp3.Models.Circuit n)
  decode_encode : ...
```

There is no runtime field for `decode`, no bit-level syntax size theorem for the
encoded circuit, and no polynomial bound on `witnessBits`.

### Repository NP surface

The active pnp3 interface defines `NP` as `NP_TM`. A witness is a Turing machine
`M` plus constants `c` and `k`, with certificate length `n^k + k`, such that
`M.runTime (n + certificateLength n k)` is polynomial and accepts exactly the
concatenated input/certificate strings.

Therefore a Prop-level budget object is not itself an `NP` proof. To prove
`PrefixExtensionLanguage parser ∈ NP`, R1-B2 or a follow-up must provide or
invoke a concrete TM verifier and a compilation argument from the chosen parser,
codec decoder, prefix check, and truth-table scan into the TM model.

## Ambient length convention status

A sufficient R1-B2 convention should make the ambient input length at target
parameter `n` satisfy:

```text
M(n) = overhead(n) + problem.instanceBits n + prefix-block(n) + padding(n)
```

For tree-MCSP, this specializes to:

```text
problem.instanceBits n = tableLen n = 2^n
M(n) ≥ tableLen n
```

A concrete bit layout should reserve fields for:

1. a fixed tag/domain separator;
2. an encoding of `n`;
3. the truth table `x : BitVec (tableLen n)`;
4. the prefix length `i`;
5. the prefix payload `p : BitVec i`;
6. padding with a canonical policy.

With `M(n) ≥ tableLen n`, enumerating all assignments costs `2^n = tableLen n`
iterations, hence is linear in `tableLen n` and at most linear in `M(n)` before
accounting for per-assignment circuit evaluation and table lookup.

The convention is not landed in Lean yet. The current `PrefixParser.M` is only
an uninterpreted `Nat → Nat`, and there is no theorem tying parser success to
`m = M n`, tag layout, canonical padding, or the extracted `x/i/p` slices.

## Parser serialization status

No concrete `parseTreeMCSPPrefix` or `treeMCSPPrefixParser_concrete` exists yet.
The existing parser field can stage such a parser, and the R1-B theorem
`PrefixExtensionLanguage_rejects_malformed` already gives the semantic rejection
behavior once parse failure is proven.

A precise parser theorem list needed for an honest R1-B2 Lean landing is:

1. **Length soundness:** if `parse y = some input`, then `m = M input.n` or the
   chosen variable-length convention's equivalent.
2. **Tag soundness:** accepted inputs have the R1-B2 tree-MCSP prefix tag.
3. **Field slicing soundness:** accepted inputs decode `n`, `x`, `i`, `p`, and
   `pad` from disjoint, documented bit ranges.
4. **Prefix bound soundness:** accepted inputs carry/prove
   `input.i ≤ problem.witnessBits input.n` without hiding a promise.
5. **Padding canonicality:** noncanonical padding is either rejected or is proven
   semantically irrelevant under a documented policy.
6. **Malformed rejection:** every ill-tagged, badly sized, out-of-range, or
   noncanonical input makes `parse` return `none`.
7. **Parser runtime:** the parser runs in time polynomial in the ambient input
   length `m`, or in `M(n)` under a single-length-per-target convention.

## Relation runtime status

For a codec witness, relation verification decomposes into:

1. decode `w` into a tree circuit `c`;
2. check `Circuit.size c ≤ threshold n`;
3. check `ComputesTruthTable treeCircuitClass c tt`, i.e. for every
   assignment `a : BitVec n`, compare `Circuit.eval c a` with the truth-table
   bit selected by `truthTableFunction tt a`.

The third step has `2^n = tableLen n` iterations. Thus:

- it is exponential in `n`;
- it is polynomial in `M(n)` if `M(n) ≥ tableLen n` and if each iteration is
  polynomial in `M(n)`.

The current code supports the first two bullets semantically, but not as a Lean
runtime theorem. To make `relation_polynomial_time` honest, R1-B2 needs these
additional assumptions or proofs:

1. `decode` runs in polynomial time in `M(n)` and returns a circuit whose syntax
   size is bounded by a polynomial in `M(n)` whenever it accepts;
2. `Circuit.size` can be computed in polynomial time in the decoded syntax size;
3. `Circuit.eval` on one assignment runs in polynomial time in the decoded
   syntax size;
4. `truthTableFunction` lookup for one assignment is polynomial in `M(n)`;
5. `threshold n` and the size comparison are representable/checkable in
   polynomial time in `M(n)`;
6. the `tableLen n` assignments can be enumerated in time polynomial in `M(n)`.

Under the natural `M(n) ≥ tableLen n` convention and a polynomial-size decoded
circuit, the truth-table agreement scan is plausibly polynomial in `M(n)`.
Without a concrete codec and TM-level cost model, this remains a staged runtime
claim, not an NP proof.

## Witness-length status

For `PrefixExtendable`, the NP certificate should be the full target witness
`w : BitVec (problem.witnessBits input.n)` extending the parsed prefix. In the
codec case this length is `codec.witnessBits n`.

The current codec interface leaves `witnessBits` abstract. Therefore
`witness_length_polynomial` cannot be discharged without an additional theorem
or assumption such as:

```text
∃ d C, ∀ n, codec.witnessBits n ≤ M(n)^d + C
```

or, more structurally, a concrete circuit serialization theorem bounding the
number of witness bits by a polynomial in `tableLen n` or `M(n)` for all decoded
circuits of interest.

A bound polynomial in `n` is sufficient because `n ≤ M(n)` under any sane
layout with an encoded `n` field and nonempty truth table, but the more relevant
R1-B2 target is polynomial in ambient input length `M(n)`. A circuit encoding of
size polynomial in `threshold n` is also sufficient if `threshold n` is bounded
by a polynomial in `M(n)`.

## Polynomial-time formalism status

The repository has two different levels:

1. pnp3 has a concrete `NP_TM` definition using a Turing machine, certificate
   length `n^k + k`, and runtime bound on the concatenated input/certificate.
2. R1-B/R1-B1 have Prop-valued fields named like `parser_polynomial_time`,
   `relation_polynomial_time`, and `witness_length_polynomial`.

What is missing is the bridge between these levels. There is no local predicate
in the contract-expansion modules that packages an executable parser/relation
verifier together with a theorem compiling it into the pnp3 TM model.

A minimal local predicate, without editing specs, would be a record of the
following shape in an R1-B2 Lean module:

```lean
structure TreeMCSPPrefixRuntimeBudget
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    (parser : PrefixParser
      (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec))) : Type where
  ambientLength : Nat → Nat
  ambientLength_ge_tableLen : ∀ n, Pnp3.Models.Partial.tableLen n ≤ ambientLength n
  parser_runtime_poly_in_M : Prop
  decode_runtime_poly_in_M : Prop
  decoded_circuit_size_poly_in_M : Prop
  threshold_check_poly_in_M : Prop
  truth_table_scan_poly_in_M : Prop
  relation_runtime_poly_in_M : Prop
  witness_length_poly_in_M : Prop
  malformed_inputs_rejected : Prop
```

This record would still not be an `NP` theorem. It would be an honest R1-B2
audit/budget object showing exactly which operational facts are available before
a later TM-compilation proof is attempted.

## Budget fields discharged

No `PrefixExtensionNPVerifierBudget` field is discharged by this report as a
Lean proof.

Clarified, but not discharged:

- `truth_table_verification_runtime`: polynomial in `M(n)` is plausible under
  `M(n) ≥ tableLen n` plus polynomial per-assignment work; false if interpreted
  as polynomial in `n`.
- `relation_polynomial_time`: blocked by abstract `decode`, abstract circuit
  serialization size, and missing TM-level runtime formalism.
- `witness_length_polynomial`: blocked by abstract `codec.witnessBits`.
- `parser_polynomial_time` and `codec_serialization_available`: blocked by the
  absence of a concrete bit-level parser/serialization.

## Local vs global obstruction

### Local blockers

- No concrete `M(n)` theorem proving `tableLen n ≤ M(n)` for the selected
  layout.
- No `parseTreeMCSPPrefix` implementation or parser soundness theorem suite.
- No polynomial bound on `codec.witnessBits n`.
- No runtime contract for `codec.decode`.
- No bound connecting decoded circuit size, `threshold n`, and `M(n)`.

### Global blockers

- The repository's active `NP` target is TM-based, but the R1-B/R1-B1 budget
  fields are Prop-level placeholders. There is currently no compiler theorem
  from those local budget fields to a pnp3 `NP_TM` verifier.
- The tree-circuit codec interface is intentionally semantic/abstract, so Lean
  cannot infer executable polynomial-time verification from it.

The global blocker is the reason not to add a theorem named like
`PrefixExtensionLanguage_in_NP` in this round.

## What R1-C must know

R1-C must remain gated. Before R1-C can use the prefix-extension language, it
must know at least:

1. which ambient length convention is used;
2. that malformed encodings are rejected by the concrete parser;
3. that the full-witness certificate length is polynomial in the ambient input
   length;
4. that the parser, prefix check, codec decode, size check, and relation check
   form a polynomial-time verifier in the repository's `NP_TM` sense or via an
   explicitly approved bridge;
5. that truth-table enumeration is budgeted against `M(n)`, not against `n`.

R1-C still must not infer any extraction theorem, `PpolyDAG L →
BoundedSearchSolver`, `target.noBoundedSolver`, `VerifiedNPDAGLowerBoundSource`,
`ResearchGapWitness`, endpoint, `SourceTheorem`, `gap_from`, or P-vs-NP claim
from this report.

## Recommended next move

Open a narrow R1-B2 Lean follow-up that does **not** attempt `NP` membership.
It should define a local runtime-budget record and prove only structural
arithmetic facts that are already justified, starting with:

1. a concrete or parameterized `M(n)` convention for tree-MCSP prefix inputs;
2. `tableLen n ≤ M(n)`;
3. a staged parser-soundness theorem list;
4. explicit assumptions for `codec.witnessBits` and `codec.decode` runtime;
5. an honest `truth_table_scan_poly_in_M` field or theorem statement that says
   precisely that the scan is polynomial in `M(n)`, not in `n`.

Only after that should a separate task consider a TM-compilation bridge from the
budget object to pnp3 `NP_TM`.
