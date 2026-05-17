# Polynomial-time formalism scoping D0

## Status

OPEN — D0 only.

No implementation authorised.  
No Lean code authorised.  
No R1-C authorised.

## Why this seed pack exists

The FP3b + `contract_expansion` retrospective recommends stopping the R1-cadence dispatch pattern.  R1-A, R1-B, R1-B1, R1-B2, and R1-B2a landed useful interface, language, decidability, and runtime-budget infrastructure, but further R1-style local packs are not expected to close the remaining blocker.

The blocker is architectural rather than parser arithmetic.  The repository has local pnp4 facts about `PrefixExtensionLanguage`, parser rejection, length conventions, codec decidability, ambient-length arithmetic, and named runtime obligations.  What it does not yet have is a pnp4 polynomial-time formalism capable of turning those local parser/codec/runtime facts into the canonical pnp3 `ComplexityInterfaces.NP` / `NP_TM` membership statement.

This seed pack is therefore only a scoping decision: determine whether investing in a minimal polynomial-time layer is justified, where it should live, and what exact bridge obligations would be needed.  It is infrastructure scoping, not P-vs-NP mainline progress and not a lower-bound source.

## Central question

Can the repository build a minimal polynomial-time formalism sufficient to prove:

```text
PrefixExtensionLanguage ∈ NP
```

from local runtime facts, without modifying trust roots and without faking runtime proofs?

A useful D0 answer should distinguish a real bridge to pnp3 `ComplexityInterfaces.NP` / `NP_TM` from merely adding more named `Prop` obligations in pnp4.

## D0 deliverable

Produce one markdown report:

```text
seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_<HANDLE>.md
```

The report should give a scoping verdict, a minimal proposed interface shape if the verdict is green or inconclusive, and a concrete reason if the verdict is red.

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

Only this seed-pack skeleton is in scope:

- `seed_packs/polynomial_time_formalism_scoping_D0/README.md`
- `seed_packs/polynomial_time_formalism_scoping_D0/WORKER_PROMPT_D0.md`
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/.gitkeep`
- `seed_packs/polynomial_time_formalism_scoping_D0/failures/.gitkeep`

An optional one-line registration in `seed_packs/README.md` is allowed, but not required for D0.
