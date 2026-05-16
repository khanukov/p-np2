# R1-B2 runtime budget report — gpt55

## Outcome

`REPORT_LANDED`.

This report does **not** prove `PrefixExtensionLanguage_in_NP`, does **not**
instantiate `PrefixExtensionNPVerifierBudget`, and does **not** open R1-C.  It
resolves the main R1-B2 runtime distinction at the level currently supported by
repository interfaces and identifies the exact local/global blockers that remain
before an honest NP-membership theorem can be stated.

## 1. What was attempted

I inspected the R1-B/R1-B1 prefix-extension interfaces and the concrete
Tree-MCSP target to answer the R1-B2 question:

> Can the R1-B / R1-B1 prefix-extension language be shown to be an NP language
> under a concrete serialization and runtime budget, without hiding verifier
> work in staged `Prop` fields?

The answer is:

- **Mathematically plausible relative to the ambient input length `M(n)`**, not
  relative to the target parameter `n` alone.
- **Not currently formalizable as an honest `NP` theorem in this repository**
  without additional local runtime predicates, a concrete parser, and concrete
  codec bounds.
- The present R1-B1 result is correctly limited to decidability: it does not
  provide a polynomial-time verifier.

## 2. Exact signatures inspected

### Prefix language surface

- `PrefixInput` stores the parsed fields `tag`, `n`, `x`, `i`, bounded prefix
  proof `prefixLength_le`, prefix payload `p`, and padding payload `pad`.
- `PrefixParser` stores a tag, an intended length convention `M : Nat → Nat`,
  and an abstract parser
  `parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)`.
- `PrefixExtendableInput` asks for a full witness extending the parsed prefix
  and satisfying `problem.relation input.n input.x w`.
- `PrefixExtensionLanguage` is currently a noncomputable Boolean wrapper over
  `PrefixExtendable`; the concrete verifier work is intentionally staged.
- `PrefixExtensionNPVerifierBudget` contains the still-undischarged runtime and
  codec fields:
  `parser_polynomial_time`, `witness_length_polynomial`,
  `prefix_agreement_polynomial_time`, `relation_decidable`,
  `relation_polynomial_time`, `codec_serialization_available`,
  `codec_decode_available`, `codec_witness_length_bound`, and
  `truth_table_verification_runtime`.

### R1-B1 parser / codec surface

- `treeMCSPPrefixParser` is a parameterized parser constructor; it does not fix
  bit-level serialization.
- `TreeMCSPPrefixParserObligations` records parser obligations as real fields,
  not as `True` fillers.
- `TreeCircuitWitnessCodec.verifiesDecidable` proves decidability by decoding
  a witness and checking a finite universal quantification over all assignments.
- `TreeMCSPPrefixCoreBudgetProgress` records decidability plus staged runtime
  fields; R1-B1 deliberately does not discharge those runtime fields.

### Concrete Tree-MCSP target

- `TreeMCSPSearchWitnessEncoding` is abstract: it exposes `witnessBits` and a
  proof-level verifier relation `verifies`, but no runtime contract.
- `TreeCircuitWitnessCodec` adds `encode`, `decode`, and `decode_encode`, but
  still does not state a bit-level syntax, decode runtime, circuit-size bound,
  or witness-length polynomial.
- `treeMCSPSearchProblem` fixes `instanceBits n := Pnp3.Models.Partial.tableLen n`.
- `TruthTable n` is `BitVec (tableLen n)`.
- `ComputesTruthTable` is proof-level agreement over every `x : BitVec n`.

### NP formalism

- `ComplexityInterfaces.NP` abbreviates `NP_TM`.
- `NP_TM` requires an explicit Turing machine verifier and a polynomial runtime
  bound in the **ambient language input length** `m`, with certificate length
  fixed as `certificateLength m k = m^k + k`.
- There is no currently exposed local bridge from a high-level parser/relation
  runtime budget to an `NP_TM` witness.

## 3. Ambient length convention status

A usable R1-B2 convention should be parameterized by target length `n` and should
make the ambient input long enough to include the full truth table instance and
the active prefix payload.  The minimal shape is:

```text
M(n) = overhead(n) + problem.instanceBits n + problem.witnessBits n + prefix/padding overhead
```

For Tree-MCSP this specializes to:

```text
problem.instanceBits n = tableLen n = 2^n
M(n) ≥ tableLen n
```

A concrete serialization can choose, for example:

```text
M(n) = tagBits + nBits(n) + iBits(n) + tableLen n + codec.witnessBits n + padBits(n)
```

where:

- `tagBits` is a fixed domain/version separator;
- `nBits(n)` is a self-delimiting or fixed-slice encoding of `n`;
- `iBits(n)` encodes an integer `i ≤ codec.witnessBits n`;
- `tableLen n` bits encode the truth table `x`;
- `codec.witnessBits n` slots are reserved so a prefix `p` of any length can be
  stored with a length marker and padding;
- `padBits(n)` enforces a single ambient length for the slice, if needed.

### Load-bearing inequality

Since `tableLen n ≤ M(n)`, any verifier loop that enumerates exactly
`tableLen n = 2^n` assignments has runtime linear in `tableLen n` up to the cost
of one circuit evaluation and one table lookup.  Therefore the enumeration is:

- exponential in `n`;
- polynomial in `M(n)` **provided the per-assignment work is polynomial in
  `M(n)` and the decoded circuit size is polynomial in `M(n)`**.

This is the central R1-B2 resolution: the truth-table loop is not an obstruction
by itself when the language input contains the full truth table.

## 4. Parser serialization status

No exact bit-level parser exists yet.  The current parser interface is abstract:

```lean
parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)
```

A concrete R1-B2 parser should implement or specify:

```text
parseTreeMCSPPrefix
```

with fields:

```text
tag | n | x : BitVec (tableLen n) | i | p : BitVec i | pad
```

and then package it as:

```text
treeMCSPPrefixParser_concrete
```

### Required parser theorem list

The following theorems are the minimum useful parser contract; none is present
for a concrete serialization today:

1. **Length convention**

   ```text
   parseTreeMCSPPrefix y = some input → m = M(input.n)
   ```

   or an equivalent theorem connecting accepted inputs to the slice convention.

2. **Field soundness**

   ```text
   parseTreeMCSPPrefix (encode tag n x i p pad) = some input
   ```

   with `input.n = n`, `input.x = x`, `input.i = i`, and `input.p = p`.

3. **Prefix bound soundness**

   ```text
   parseTreeMCSPPrefix y = some input → input.i ≤ problem.witnessBits input.n
   ```

   This is currently stored inside `PrefixInput.prefixLength_le`, but a concrete
   parser proof must show that malformed encodings cannot create an out-of-range
   prefix.

4. **Malformed-input behavior**

   ```text
   parseTreeMCSPPrefix y = none → PrefixExtensionLanguage parser y = false
   ```

   R1-B already provides the general language-level malformed rejection theorem;
   R1-B2 needs the parser-specific facts that cause malformed strings to return
   `none`.

5. **Parser runtime**

   ```text
   parser_polynomial_time relative to m = M(n)
   ```

   The parser may scan the full truth table and prefix payload, so linear or
   near-linear runtime in `M(n)` is acceptable.

## 5. Relation runtime status

For a concrete `TreeCircuitWitnessCodec`, relation verification has the shape:

1. Decode `w` to an optional circuit `c`.
2. Check `Circuit.size c ≤ threshold n`.
3. Check truth-table agreement:

   ```text
   ∀ x : BitVec n, Circuit.eval c x = truthTableFunction tt x
   ```

R1-B1 proves this is decidable using finite enumeration over `BitVec n`.  Since
`|BitVec n| = tableLen n = 2^n`, this is **not polynomial in `n`**.

However, if `M(n) ≥ tableLen n`, then the enumeration count is `≤ M(n)`.  The
relation can therefore be polynomial in `M(n)` under the following concrete
codec/runtime assumptions:

- `decode n w` runs in time polynomial in `M(n)`;
- decoded circuits accepted by the codec have size polynomial in `M(n)`;
- `Circuit.eval c x` runs in time polynomial in `Circuit.size c + n`, hence in
  polynomial time in `M(n)` for accepted decoded circuits;
- table lookup through `truthTableFunction tt x` is polynomial in `n` or in
  `log(tableLen n)`, and therefore polynomial in `M(n)`;
- size computation `Circuit.size c` is polynomial in the encoded witness length,
  hence polynomial in `M(n)`.

### Relation-runtime verdict

`TreeCircuitWitnessCodec.verifiesDecidable` is **potentially polynomial in
`M(n)`**, but only after the codec is strengthened with runtime and size
contracts.  The current signature is too abstract to prove this because
`decode` is an arbitrary function and `codec.witnessBits n` is arbitrary.

## 6. Witness-length status

For NP membership of the ambient language, the certificate is the full target
witness `w : BitVec (problem.witnessBits input.n)`.  The R1-B2 witness-length
obligation is therefore:

```text
problem.witnessBits n ≤ poly(M(n))
```

For the codec specialization:

```text
codec.witnessBits n ≤ poly(M(n))
```

This bound is easy if the serialization convention defines
`M(n) ≥ codec.witnessBits n`.  But this is only a convention unless one commits
to a concrete `M` and proves the accepted inputs have length `M(n)`.

### Witness-length verdict

The witness-length field is a **local codec/serialization blocker**, not a
mathematical obstruction.  The current repository cannot discharge it because
`TreeCircuitWitnessCodec.witnessBits` is abstract and has no polynomial bound.

## 7. Polynomial-time formalism status

The repository already has the final semantic target for NP:

```text
ComplexityInterfaces.NP = NP_TM
```

But R1-B2 currently lacks a middle layer that turns high-level budget facts into
an `NP_TM` verifier.  In particular, there is no local predicate package of the
following form:

```text
RuntimePolynomialInM (M : Nat → Nat) (work : Nat → Nat) : Prop
ParserPolynomialTime parser M : Prop
RelationPolynomialTimeInM relation M : Prop
WitnessLengthPolynomialInM witnessBits M : Prop
```

A minimal local R1-B2 predicate package should be **audit-only** and should not
pretend to construct a Turing machine.  It should expose exactly the quantities
that a later TM bridge must compile:

```text
TreeMCSPPrefixRuntimeBudget where
  M : Nat → Nat
  tableLen_le_M : ∀ n, tableLen n ≤ M n
  parser_polynomial_time_in_M : Prop
  decode_polynomial_time_in_M : Prop
  decoded_circuit_size_polynomial_in_M : Prop
  circuit_eval_polynomial_time_in_M : Prop
  truth_table_loop_polynomial_in_M : Prop
  relation_polynomial_time_in_M : Prop
  witness_length_polynomial_in_M : Prop
```

The important restriction is that these fields must not be filled with `True`.
They must be either proved for a concrete parser/codec or deliberately left as
undischarged obligations.

### Formalism verdict

This is a **global interface blocker** for a final Lean theorem of the form
`PrefixExtensionLanguage_in_NP`: the repository's public `NP` is TM-based, but
R1-B2 currently only has high-level parser/relation propositions.  A later bridge
from these propositions to `NP_TM` is needed, or the parser/relation must be
implemented directly as a Turing machine verifier.

## 8. Budget fields discharged

No `PrefixExtensionNPVerifierBudget` fields are formally discharged in this
report.  The honest status is:

| Field | Status |
| --- | --- |
| `parser_polynomial_time` | staged; concrete parser absent |
| `witness_length_polynomial` | local blocker; needs `codec.witnessBits n ≤ poly(M(n))` or `M(n)` including witness capacity |
| `prefix_agreement_polynomial_time` | plausible linear in prefix/witness length; not formalized |
| `relation_decidable` | discharged in R1-B1 for codec case |
| `relation_polynomial_time` | clarified: false/unsupported as polynomial in `n`; plausible in `M(n)` under codec runtime/size assumptions |
| `codec_serialization_available` | absent |
| `codec_decode_available` | decode function exists, but executable serialization/runtime contract absent |
| `codec_witness_length_bound` | absent |
| `truth_table_verification_runtime` | clarified: table loop has `tableLen n` iterations, hence polynomial in `M(n)` if `tableLen n ≤ M(n)` |

## 9. Local vs global obstruction

### Local blockers

- Concrete bit layout for `tag`, `n`, `x`, `i`, `p`, and `pad`.
- Concrete `parseTreeMCSPPrefix` and `treeMCSPPrefixParser_concrete`.
- Parser length theorem tying accepted strings to `M(n)`.
- Codec witness-length bound.
- Codec decode runtime bound.
- Decoded circuit size bound relative to `M(n)`.
- Arithmetic lemmas such as `tableLen n ≤ M(n)` for the chosen convention.

### Global blockers

- No bridge from a high-level runtime-budget record to
  `ComplexityInterfaces.NP = NP_TM`.
- No repository-wide local formalism for polynomial-time parser/relation
  verification that compiles to the TM-based `NP` definition.

The current encoding does **not** appear globally impossible: full truth-table
verification is compatible with polynomial time in the ambient length because the
input contains the truth table.  The global blocker is formal-interface support,
not the `2^n` loop itself.

## 10. What R1-C must know

R1-C must remain gated until R1-B2 supplies at least an audit-stable budget with
these facts:

1. accepted prefix-language inputs have length `M(n)`;
2. `tableLen n ≤ M(n)`;
3. prefix parser and malformed-input behavior are concrete;
4. full-witness certificate length is polynomial in `M(n)`;
5. relation verification is polynomial in `M(n)` for the chosen codec;
6. no step assumes polynomial time in `n` for the truth-table loop.

R1-C must not consume a fake `PrefixExtensionLanguage_in_NP` theorem or a budget
record whose missing runtime fields are inhabited by vacuous `True` values.

## 11. Recommended next move

Open a narrow R1-B2 follow-up to add a Lean audit module, not a final NP theorem:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

Recommended contents:

1. Define a parameterized ambient-length convention record:

   ```text
   TreeMCSPPrefixAmbientLength
   ```

   with `M`, `tableLen_le_M`, and `witnessBits_le_M` fields.

2. Define a runtime-budget record:

   ```text
   TreeMCSPPrefixRuntimeBudget
   ```

   whose fields are real obligations, not `True` placeholders.

3. Add arithmetic lemmas showing that, under `tableLen_le_M`, the truth-table
   enumeration count is bounded by `M(n)`.

4. Keep `PrefixExtensionLanguage_in_NP` out of scope until the TM bridge or a
   concrete verifier implementation exists.

## Final classification

- Outcome: `REPORT_LANDED`.
- Ambient length status: resolved at audit level; `M(n)` must dominate
  `tableLen n` and preferably `codec.witnessBits n`.
- Parser status: concrete parser absent; exact theorem list above.
- Relation runtime status: decidable already; polynomial in `M(n)` is plausible
  under concrete codec runtime/size assumptions; polynomial in `n` is false for
  the truth-table loop.
- Witness length status: local codec/serialization blocker.
- Polynomial-time formalism status: global bridge to `NP_TM` missing.
- R1-C readiness: **not ready**.
