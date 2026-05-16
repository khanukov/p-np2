# R1-B2a Runtime-Aware Codec/Parser Interface Report — GPT-5.5

## Outcome

**LEAN_PROGRESS_LANDED.**

Lean module landed at:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

This is R1-B2a only.  It does not open R1-C and does not prove
`PrefixExtensionLanguage_in_NP`.

## Ambient length status

The module defines:

```lean
treeMCSPPrefixAmbientLength
  (overhead witnessBits padBits : Nat → Nat) (n : Nat) : Nat
```

with the `tableLen n` component included explicitly.  The module also proves the
real arithmetic lemma:

```lean
tableLen_le_treeMCSPPrefixAmbientLength
```

This discharges the local fact that truth-table length is bounded by the staged
ambient input length.

## Runtime-aware codec status

The module defines:

```lean
RuntimeAwareTreeCircuitCodec
```

wrapping `TreeCircuitWitnessCodec threshold`.  It has concrete arithmetic fields
for:

- `witnessBits_poly_in_M`;
- `threshold_poly_in_M`.

It also has named runtime obligations for:

- `decode_polynomial_time_in_M`;
- `circuit_eval_polynomial_time_in_size`;
- `truth_table_lookup_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`.

These runtime fields are staged as `Prop` obligations because the current repo
still lacks a uniform polynomial-time machine-cost formalism for codec decode,
circuit evaluation, and truth-table lookup.  They are not filled with `True`.

## Parser runtime status

The module defines:

```lean
RuntimeAwarePrefixParser
```

with:

- a concrete `PrefixParser problem` field;
- a staged `parser_polynomial_time_in_M` obligation;
- a precise malformed-input rejection obligation;
- a precise length-convention soundness obligation requiring accepted strings of
  length `m` to satisfy `m = M input.n`.

## Budget object status

The module defines:

```lean
TreeMCSPPrefixRuntimeBudget
```

This object is only a runtime-budget interface, not an NP theorem.  It collects:

- `tableLen_le_M`;
- `threshold_poly_in_M`;
- `witnessBits_poly_in_M`;
- staged decode/parser/evaluation/lookup/relation runtime obligations;
- parser malformed-input and length-convention obligations.

## Polynomial-time formalism status

The local arithmetic obligations are now explicit in Lean.  The global runtime
formalism remains the blocker: the repository still needs an audited connection
from these staged parser/codec/runtime facts to the canonical TM-based NP
interface before any honest `PrefixExtensionLanguage_in_NP` theorem can be
proved.

## R1-C status

R1-C remains gated.  This report does not introduce extraction, bounded-search
solvers, `VerifiedNPDAGLowerBoundSource`, `ResearchGapWitness`, `SourceTheorem`,
`gap_from`, or any endpoint/P≠NP claim.
