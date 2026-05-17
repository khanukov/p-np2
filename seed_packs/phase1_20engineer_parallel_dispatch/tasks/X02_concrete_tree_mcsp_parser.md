# X02: Concrete tree-MCSP parser implementation + runtime proofs

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reasons:
> 1. Spec uses `M := fun n => n` in `length_convention` / `malformed_rejected`,
>    but the live runtime in
>    `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`
>    fixes the ambient-length convention as
>    `treeMCSPPrefixAmbientLength overhead witnessBits padBits n
>     = tableLen n + overhead n + witnessBits n + padBits n`.
>    The theorem signatures as written do not align with that convention and
>    cannot be proved against the current runtime layer.
> 2. X02 is gated on X01 landing; even with a corrected spec it must not run
>    in parallel with X01.
> Before reactivation: rewrite signatures to consume `treeMCSPPrefixAmbientLength`
> (or some explicitly stated ambient-length convention from R1-B2a) and gate
> dispatch on X01 merged + reviewed.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** X02 | **Phase:** 5 — Contract expansion | **Estimated:** 4 weeks | **Difficulty:** medium-high | **Benefits from:** X01 landing

## Goal

Provide a **concrete byte-level parser implementation** for the tree-MCSP prefix-extension language plus the parser runtime / soundness / length-convention proofs that R1-B2a staged as `Prop` fields. This makes the contract_expansion track's parser layer non-staged.

## Source material

* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` (R1-B; read).
* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` (R1-B1; read).
* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean` (R1-B2a; the structure to instantiate).
* `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` (tree-MCSP target).

## Deliverable

```
pnp4/Pnp4/Frontier/ContractExpansion/TreeMCSPParserImpl.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Frontier
namespace ContractExpansion

def encodeTreeMCSPPrefixInput {threshold} {encoding} {m} 
    (input : PrefixInput (treeMCSPSearchProblem threshold encoding) m) :
    AlgorithmsToLowerBounds.BitVec m := ...

def parseTreeMCSPPrefixInput {threshold} {encoding} {m} 
    (y : AlgorithmsToLowerBounds.BitVec m) :
    Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m) := ...

def treeMCSPPrefixParserConcrete {threshold} (encoding) (tag M) :
    PrefixParser (treeMCSPSearchProblem threshold encoding) :=
  treeMCSPPrefixParser threshold encoding tag M parseTreeMCSPPrefixInput

theorem parseTreeMCSPPrefixInput_length_convention {...} 
    (h : parseTreeMCSPPrefixInput y = some input) :
    m = (treeMCSPPrefixParserConcrete encoding 0 (fun n => n)).M input.n := ...

theorem parseTreeMCSPPrefixInput_malformed_rejected {...} 
    (h : parseTreeMCSPPrefixInput y = none) :
    PrefixExtensionLanguage (treeMCSPPrefixParserConcrete encoding 0 (fun n => n)) m y = false := ...

theorem parseTreeMCSPPrefixInput_round_trip {...} (input : PrefixInput ...) :
    parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput input) = some input := ...
```

### Optional: budget instance

Instantiate `TreeMCSPPrefixRuntimeBudget` with as many real fields as possible.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `encodeTreeMCSPPrefixInput`, `parseTreeMCSPPrefixInput` defined as **computable** functions (no `noncomputable`).
- [ ] Round-trip property `parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput input) = some input` proven kernel-clean.
- [ ] `parseTreeMCSPPrefixInput_length_convention` proven.
- [ ] `parseTreeMCSPPrefixInput_malformed_rejected` proven.
- [ ] Optionally: `TreeMCSPPrefixRuntimeBudget` instance with at least 4 real (non-`True`) fields.
- [ ] **No `Classical.choose`** in parser definitions.
- [ ] Doc-comment: runtime captured at type-decidability level, not TM-step level (honest caveat).

### Honest caveats
- Runtime claims (e.g., `parser_polynomial_time_in_M`) at structural Prop level only. TM-step level requires X01 + further work.
- If you cannot prove a clean round-trip, state explicitly which encoding choice was made and what's needed for full round-trip.

## Scope

### Allowed
- New module at `pnp4/Pnp4/Frontier/ContractExpansion/TreeMCSPParserImpl.lean`.
- May import from X01 if landed.

### Forbidden
- Universal.
- ❌ Editing `pnp3/Complexity/Interfaces.lean`.
- ❌ Editing R1-B / R1-B1 / R1-B2a (`PrefixExtensionLanguage*.lean`) — frozen.
- ❌ `PrefixExtensionLanguage_in_NP` claim.
- ❌ R1-C work.

## Output
Universal template with detailed honest caveats.
