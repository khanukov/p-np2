# K01: Cross-route NoGo applicability checker library

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: NoGo applicability is reduced to a hand-coded `List (String × NoGoApplicability)`
> over a `ProofSafetyCertificate` whose fields are bare `Prop`s. Typed rubric,
> not a theorem-producing engine. Useful as documentation/program-management
> after routes are settled; not on shortest path now.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** K01 | **Phase:** 4 — Kill-machine | **Estimated:** 2 weeks | **Difficulty:** medium

## Goal

Build a Lean library that, given a candidate route's safety properties (a `ProofSafetyCertificate`), automatically checks applicability of each existing NoGo entry (NOGO-000005..000009) and outputs a list of applicability verdicts per NoGo.

## Source material

* `outputs/nogolog.jsonl` entries (read-only).
* Existing `formal_witness` Lean theorems referenced by each NoGo.
* A09 audit output (if landed) — confirms which `formal_witness` fields are valid.

## Deliverable

```
pnp4/Pnp4/KillMachine/CrossRouteChecker.lean
pnp4/Pnp4/KillMachine/NoGoApplicability.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace KillMachine

structure ProofSafetyCertificate where
  route_name : String
  excludes_support_cardinality_only : Prop
  excludes_displayed_syntax_only : Prop
  excludes_normalise_then_filter : Prop
  excludes_arbitrary_logwidth_tt : Prop
  excludes_prefix_and_hardwiring : Prop

inductive NoGoApplicability where
  | applicable
  | not_applicable
  | safety_unclear
  deriving Repr, DecidableEq

def crossRouteCheck (cert : ProofSafetyCertificate) : List (String × NoGoApplicability) := [
  ("NOGO-000005", ...),
  ("NOGO-000006", ...),
  ("NOGO-000007", ...),
  ("NOGO-000008", ...),
  ("NOGO-000009", ...),
]
```

### Lemmas / sanity

```lean
theorem crossRouteCheck.completeness (cert : ProofSafetyCertificate) :
    (crossRouteCheck cert).length = 5 := by decide

theorem crossRouteCheck.empty_safety :
    ∀ p ∈ crossRouteCheck { route_name := "test", excludes_support_cardinality_only := False, ... },
      p.2 = NoGoApplicability.applicable ∨ p.2 = NoGoApplicability.safety_unclear
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Two modules at exact paths.
- [ ] `ProofSafetyCertificate`, `NoGoApplicability`, `crossRouteCheck` defined.
- [ ] `completeness`, `empty_safety` proven kernel-clean.
- [ ] At least one example `ProofSafetyCertificate` for an existing route (e.g., R1-B2a `andPayload` geometry from fp3b6).
- [ ] Doc-comment cites all 5 NoGo entries.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/KillMachine/`.

### Forbidden
- Universal.
- ❌ Editing `outputs/nogolog.jsonl`.
- ❌ Promoting any guard to `accepted`.

## Output
Universal template.
