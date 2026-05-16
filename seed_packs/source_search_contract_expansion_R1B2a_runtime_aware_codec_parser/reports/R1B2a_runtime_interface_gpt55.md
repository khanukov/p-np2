# R1-B2a Runtime-Aware Codec / Parser Interface Report — GPT-5.5

## Outcome

**LEAN_PROGRESS_LANDED.**

Lean module landed at:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

This is R1-B2a only.  It is a runtime-budget interface, not an NP-membership
result and not R1-C.

## Ambient length status

The module defines:

```lean
treeMCSPPrefixAmbientLength
  (overhead witnessBits padBits : Nat → Nat) (n : Nat) : Nat
```

as the sum of the parameterized overhead, the tree-MCSP truth-table component
`treeMCSPTableLen n`, the witness/prefix budget, and padding.  The explicit
truth-table summand is the important R1-B2 distinction: the relation may be
exponential in `n` while still being polynomial in the ambient encoded length
once the input contains the full truth table.

A real Lean arithmetic lemma landed:

```lean
tableLen_le_treeMCSPPrefixAmbientLength
```

and a projection-style helper:

```lean
tableLen_le_M_of_treeMCSPPrefixAmbientLength
```

## Runtime-aware codec status

The module defines `RuntimeAwareTreeCircuitCodec`, wrapping the existing
`TreeCircuitWitnessCodec threshold`.  It records the following obligations:

- `witnessBits_poly_in_M`;
- `decode_polynomial_time_in_M`;
- `threshold_poly_in_M`;
- `circuit_eval_polynomial_time_in_size`;
- `truth_table_lookup_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`.

The size bounds are formalized through `PolynomiallyBoundedIn`.  The runtime
fields remain `Prop` obligations because the repository does not yet provide a
canonical polynomial-time machine model for the local codec decode, parser, and
truth-table lookup algorithms.

## Parser runtime status

The module defines `RuntimeAwarePrefixParser`, containing:

- the existing `PrefixParser problem`;
- `parser_polynomial_time_in_M` as a staged runtime obligation;
- malformed-input soundness against `PrefixExtensionLanguage`;
- length-convention soundness stating successful parses have ambient length
  `M input.n`.

This does not fix a concrete bit-level serialization.  It makes explicit what a
future parser must prove.

## Budget object status

The module defines `TreeMCSPPrefixRuntimeBudget`, with the requested fields:

- `tableLen_le_M`;
- `threshold_poly_in_M`;
- `witnessBits_poly_in_M`;
- `decode_polynomial_time_in_M`;
- `parser_polynomial_time_in_M`;
- `circuit_eval_polynomial_time_in_size`;
- `truth_table_lookup_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`.

This object is deliberately not an NP theorem.

## Polynomial-time formalism status

**Blocker:** no canonical local polynomial-time formalism exists yet for the
parser, codec decoder, truth-table lookup, or combined relation.  Therefore the
runtime fields are explicit `Prop` obligations, not fake `True` fields.

## R1-C readiness

R1-C remains gated.  A future R1-C worker would still need a concrete parser,
concrete codec serialization, machine-time proofs for the staged runtime fields,
and a bridge from these local runtime facts to the repository's `NP`/`NP_TM`
interface.
