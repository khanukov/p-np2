# K02: Pre-dispatch barrier classification tool

**Engineer:** K02 | **Phase:** 4 — Kill-machine | **Estimated:** 2 weeks | **Difficulty:** medium

## Goal

Build a Lean + markdown framework that, given a proposed route's description, produces a structured classification of which classical barriers (Razborov-Rudich / Relativization / Algebrization / Locality / Feasible unprovability) the route likely triggers.

## Source material

* B01, B02, B03 outputs (if landed) — pnp4 barrier formalizations.
* `pnp3/Barrier/*` minimal interfaces.

## Deliverable

```
pnp4/Pnp4/KillMachine/BarrierClassifier.lean
seed_packs/phase1_20engineer_parallel_dispatch/templates/BARRIER_CLASSIFICATION_TEMPLATE.md
```

### Expected signatures (BarrierClassifier.lean)

```lean
namespace Pnp4
namespace KillMachine

inductive Barrier where
  | RazborovRudich
  | Relativization
  | Algebrization
  | Locality
  | FeasibleUnprovability
  deriving Repr, DecidableEq

inductive BarrierTrigger where
  | clearly_triggered
  | possibly_triggered
  | clearly_avoided
  | uncertain
  deriving Repr

structure RouteBarrierClassification (route_name : String) where
  classifications : Barrier → BarrierTrigger
  evidence : Barrier → String

theorem BarrierClassification.completeness (route_name : String) 
    (cls : RouteBarrierClassification route_name) :
    ∀ b : Barrier, ∃ status : BarrierTrigger, cls.classifications b = status :=
  fun b => ⟨cls.classifications b, rfl⟩
```

### Markdown template

```markdown
# Barrier classification for <ROUTE_NAME>

## Route summary
<1-paragraph route description>

## Classification per barrier

| Barrier | Trigger status | Evidence |
| --- | --- | --- |
| Razborov-Rudich | clearly_triggered / possibly / avoided / uncertain | <ref> |
| Relativization | ... | ... |
| Algebrization | ... | ... |
| Locality (CHOPRS) | ... | ... |
| Feasible unprovability (Pich-Santhanam) | ... | ... |

## Conclusion
<Recommend: open / RED-light / needs more design pass>
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `Barrier`, `BarrierTrigger`, `RouteBarrierClassification` defined.
- [ ] `Decidable` instances for `Barrier` and `BarrierTrigger`.
- [ ] Markdown template at exact path.
- [ ] At least one example classification (e.g., for fp3b6 retrospectively — would trigger Locality + possibly Razborov-Rudich).
- [ ] Doc-comment links to B01/B02/B03 outputs (if landed).

## Scope

### Allowed
- New module + new template at exact paths.

### Forbidden
- Universal.
- ❌ No automatic "RED-light" production — classification is operator-decision support, not auto-action.

## Output
Universal template.
