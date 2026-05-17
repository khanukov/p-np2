# Seed pack `polynomial_time_formalism_scoping_D0`

## Status

OPEN — D0 only.

No implementation authorised.
No Lean code authorised.
No R1-C authorised.

## Why this seed pack exists

The FP3b + contract-expansion retrospective stops the R1-cadence dispatches.
R1-A/B/B1/B2/B2a landed useful parser, codec, adapter, arithmetic, and runtime-budget infrastructure, but continuing directly to an R1-C-style implementation would miss the remaining architectural blocker.

That blocker is not parser arithmetic.  The blocker is that the repository does not yet expose a pnp4 polynomial-time formalism that can bridge local parser/codec/runtime facts to the canonical pnp3 `ComplexityInterfaces.NP` / `NP_TM` definition.  Existing contract-expansion modules can name parser obligations, relation decidability, witness-length bounds, ambient-length facts, and staged runtime obligations; they do not yet provide the global machine-cost layer needed to turn those local facts into a faithful NP-membership theorem.

This seed pack is therefore only a scoping decision.  It asks whether the next investment should be a minimal formalism layer, not another local R1 dispatch.

## Central question

Can the repository build a minimal polynomial-time formalism sufficient to prove:

```text
PrefixExtensionLanguage ∈ NP
```

from local runtime facts, without modifying trust roots and without faking runtime proofs?

## D0 deliverable

One markdown report:

```text
seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_<HANDLE>.md
```

The report should classify the work as infrastructure unless it explicitly reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.

## Possible verdicts

- `GREEN-light_formalism_investment`
- `RED-light_too_large_or_wrong_layer`
- `INCONCLUSIVE_needs_external_literature_or_tooling`

## Forbidden scope

- No Lean code.
- No pnp3 trust-root edits.
- No source theorem.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No R1-C.
- No P≠NP claim.

## Allowed scope

Only the four skeleton files in this seed pack are authorised:

- `seed_packs/polynomial_time_formalism_scoping_D0/README.md`
- `seed_packs/polynomial_time_formalism_scoping_D0/WORKER_PROMPT_D0.md`
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/.gitkeep`
- `seed_packs/polynomial_time_formalism_scoping_D0/failures/.gitkeep`

## Required command

```sh
./scripts/check.sh
```
