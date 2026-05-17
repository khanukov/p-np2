# E18: Pre-dispatch barrier-classification tool

**Engineer:** E18 | **Phase:** C — Kill-machine infrastructure | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** benefits from E14-E16 landing

## Goal

Build a **pre-dispatch barrier classification framework**: given a proposed route's description (markdown), produce a structured analysis identifying whether the route triggers Razborov-Rudich / relativization / algebrization / locality / unprovability barriers. Combines markdown audit framework with Lean `Decidable` infrastructure where possible.

## Source material

* All existing pnp3/Barrier/* files (read-only).
* E14, E15, E16 outputs (if landed).
* Existing kill-machine practice from FP3b epoch (V2 closure, fp3b6/7/8 analyses).

## Deliverable

```
pnp4/Pnp4/KillMachine/BarrierClassifier.lean
seed_packs/phase1_20engineer_parallel_dispatch/templates/BARRIER_CLASSIFICATION_TEMPLATE.md
```

### Expected signatures (BarrierClassifier.lean)

```lean
namespace Pnp4
namespace KillMachine

/-- The five major barriers a candidate route might trigger. -/
inductive Barrier where
  | RazborovRudich      -- natural proofs
  | Relativization      -- BGS
  | Algebrization       -- AW
  | Locality            -- CHOPRS
  | FeasibleUnprovability  -- Pich-Santhanam
  deriving Repr, DecidableEq

/-- A barrier classification per candidate route. -/
inductive BarrierTrigger where
  | clearly_triggered      -- the route's design clearly falls under this barrier
  | possibly_triggered     -- design pattern suggests risk; needs human review
  | clearly_avoided        -- specific structural argument shows avoidance
  | uncertain              -- not enough information
  deriving Repr

/-- Classification per candidate route. -/
structure RouteBarrierClassification (route_name : String) where
  classifications : Barrier → BarrierTrigger
  evidence : Barrier → String  -- reference to specific theorem / argument
```

### Markdown template (BARRIER_CLASSIFICATION_TEMPLATE.md)

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

### Lemmas

```lean
theorem BarrierClassification.completeness 
    (route_name : String) (cls : RouteBarrierClassification route_name) :
    ∀ b : Barrier, ∃ status : BarrierTrigger, cls.classifications b = status := 
  fun b => ⟨cls.classifications b, rfl⟩
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `Barrier`, `BarrierTrigger`, `RouteBarrierClassification` defined as inductives + structures.
- [ ] `Decidable` instances for `Barrier` and `BarrierTrigger`.
- [ ] Markdown template file at exact path.
- [ ] One sanity theorem proven.
- [ ] At least one example classification (e.g., for fp3b6 Family A reanalyzed through this framework — would clearly trigger Locality and possibly Razborov-Rudich).
- [ ] Module doc-comment explains the relationship to E14-E16 (if landed) or how to upgrade once they do.

## Scope

### Allowed
- New module at `pnp4/Pnp4/KillMachine/BarrierClassifier.lean`.
- New template at `seed_packs/phase1_20engineer_parallel_dispatch/templates/BARRIER_CLASSIFICATION_TEMPLATE.md`.

### Forbidden
- Universal.
- ❌ No automatic "RED-light" production — classification is operator-decision support, not auto-action.

## Output
Universal template.
