# R1-B2a Runtime-Aware Codec / Parser Seed Pack

## Status

**OPEN — R1-B2a only.**

R1-C is gated.
Full contract expansion is **NOT** authorised.

## Classification

Infrastructure / contract-expansion staging.

This seed pack may prepare a sharper runtime-aware interface for the R1-B / R1-B1
prefix-extension language, but it must not be reported as P-vs-NP mainline
progress unless a later, separately authorised task actually reduces
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.

## Why R1-B2a exists

R1-B2 resolved the key runtime distinction:

- truth-table verification is exponential in target parameter `n`;
- but can be polynomial in ambient input length `M(n)` if `M(n)` includes
  `tableLen n`.

However, current repo still lacks:

- concrete `M(n)`;
- concrete parser;
- codec witness-length bound;
- decode runtime bound;
- threshold bound in `M(n)`;
- bridge from local runtime facts to `NP_TM`.

R1-B2a exists to isolate the next honest interface layer before any R1-C
extraction or endpoint work is allowed.

## Central R1-B2a question

Can we define a runtime-aware tree-circuit codec/parser interface with enough
explicit arithmetic/runtime fields to make the eventual
`PrefixExtensionLanguage_in_NP` theorem meaningful, without claiming it yet?

## Authorised deliverables

Workers must produce exactly one of the outcomes in
`WORKER_PROMPT_R1B2a.md`.

### A. Ambient length convention

Define/stage `TreeMCSPPrefixAmbientLength` with fields or parameters for:

- `overhead`;
- `witnessBits`;
- `padBits`;
- `tableLen` component.

Prove/stage:

- `tableLen_le_M`.

### B. Runtime-aware codec refinement

Define/stage `RuntimeAwareTreeCircuitCodec` or a similarly named wrapper around
`TreeCircuitWitnessCodec` with fields:

- `witnessBits_poly_in_M`;
- `decode_polynomial_time_in_M`;
- `threshold_poly_in_M`;
- `circuit_eval_polynomial_time_in_size`;
- `truth_table_lookup_polynomial_time_in_M`.

### C. Parser runtime record

Define/stage `RuntimeAwarePrefixParser` or a similarly named record with:

- concrete parse or parser obligations;
- `parser_polynomial_time_in_M`;
- malformed-input soundness;
- length convention soundness.

### D. Boundary

Do **NOT** prove `PrefixExtensionLanguage_in_NP`.
Do **NOT** open R1-C.

## Explicit non-goals

- No extraction theorem.
- No `PpolyDAG L → BoundedSearchSolver`.
- No `target.noBoundedSolver`.
- No `VerifiedNPDAGLowerBoundSource`.
- No `ResearchGapWitness`.
- No endpoint.
- No R1-C.
- No `SourceTheorem` / `gap_from`.
- No P≠NP claim.

## Success criteria

### Outcome A

Lean module or markdown+Lean report lands with runtime-aware codec/parser
interface and at least one real arithmetic lemma such as `tableLen_le_M`.

The preferred Lean path, if formalization is genuinely ready and all repository
requirements are satisfied, is:

- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`

### Outcome B

Structured failure identifies the exact blocker, choosing one or more of:

- no polynomial-time formalism;
- codec too abstract;
- parser serialization cannot be fixed locally;
- witnessBits bound unavailable.

## Scope guardrails

Allowed for this seed pack attempt:

- the R1-B2a seed-pack report or failure paths;
- the preferred R1-B2a Lean module path only for Outcome A;
- minimal test/audit registrations only if a Lean module is actually added and
  the repository requires them.

Forbidden:

- R1-C work;
- endpoint or final-target claims;
- trust-root edits;
- spec edits;
- JSONL edits;
- lakefile changes unless a Lean module is actually added and registration is
  required by the repository.
