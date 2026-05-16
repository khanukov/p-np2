# R1-B2a Runtime-Aware Codec / Parser Interface Report — GPT-5.5

## Outcome

Outcome: **LEAN_PROGRESS_LANDED**.

The Lean module
`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`
lands the R1-B2a runtime-budget interface.  It does **not** prove
`PrefixExtensionLanguage_in_NP`, does **not** open R1-C, and does **not** claim
an endpoint.

## Ambient length status

The module defines:

```lean
def treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) : Nat :=
  overhead n + Pnp3.Models.Partial.tableLen n + witnessBits n + padBits n
```

The table component is explicit.  The module proves the real arithmetic lemma:

```lean
theorem tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n
```

This is the local fact needed to audit the distinction between runtime in target
parameter `n` and runtime in ambient input length `M(n)`.

## Runtime-aware codec status

The module defines `RuntimeAwareTreeCircuitCodec`, wrapping
`TreeCircuitWitnessCodec threshold`.  The growth fields are not fake `True`
fields: they use the arithmetic predicate
`FunctionPolynomiallyBoundedBy M f := ∃ c, ∀ n, f n ≤ M n ^ c + c`.

The following runtime fields remain explicit `Prop` obligations because the repo
currently lacks a reusable machine-level polynomial-time formalism for them:

- `decode_polynomial_time_in_M`
- `circuit_eval_polynomial_time_in_size`
- `truth_table_lookup_polynomial_time_in_M`
- `relation_polynomial_time_in_M`

This is the main local blocker remaining after R1-B2a.

## Parser runtime status

The module defines `RuntimeAwarePrefixParser` with concrete parser data and
explicit obligations:

- `parser : PrefixParser problem`
- `parser_polynomial_time_in_M`
- `malformed_inputs_rejected`
- `length_convention_matches_M`

No concrete parser serialization is claimed.

## Budget object status

The module defines `TreeMCSPPrefixRuntimeBudget`, collecting:

- the `tableLen_le_M` obligation;
- `threshold_poly_in_M`;
- `witnessBits_poly_in_M`;
- staged decoder/parser/evaluation/lookup/relation runtime obligations;
- malformed-input and length-convention obligations.

This object is a runtime budget interface only.  It is not an NP theorem.

## Polynomial-time formalism status

The repository still needs a bridge from these local runtime obligations to the
TM-based `NP_TM` definition in `pnp3/Complexity/Interfaces.lean`.  Until that
bridge exists, the R1-B2a runtime fields are intentionally staged as named
obligations rather than silently discharged.

## R1-C readiness

R1-C is still gated.  A future R1-C worker must know at least:

1. the concrete parser serialization and its malformed-input behavior;
2. a concrete decoder runtime bound in ambient length `M(n)`;
3. a concrete circuit-evaluation implementation and per-assignment cost model;
4. a truth-table lookup runtime bound in `M(n)`;
5. a formal bridge from the local runtime budget to `NP_TM`.
