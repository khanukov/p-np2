# E17: Cross-route NoGo applicability checker library

**Engineer:** E17 | **Phase:** C — Kill-machine infrastructure | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** benefits from E14-E16 landing but does not block on them

## Goal

Build a **Lean library** that, given a candidate route's claimed safety properties (`ProofSafetyCertificate`), automatically checks applicability of each existing NoGo entry (NOGO-000005 through NOGO-000009) to the candidate. Outputs a list of "applicable" / "not applicable" / "incompatible safety claim" verdicts per NoGo.

## Source material

* Existing NoGo entries: `outputs/nogolog.jsonl` entries NOGO-000005 through NOGO-000009.
* Each NoGo has `formal_witness` field pointing to a kernel-checked Lean theorem.
* The library's job: structure these as Lean predicates and compose them into a single checker.

## Deliverable

```
pnp4/Pnp4/KillMachine/CrossRouteChecker.lean
pnp4/Pnp4/KillMachine/NoGoApplicability.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace KillMachine

/-- A route's safety certificate: claims about which barrier classes it avoids. -/
structure ProofSafetyCertificate where
  route_name : String
  excludes_support_cardinality_only : Prop  -- NOGO-000007 avoidance
  excludes_displayed_syntax_only : Prop      -- NOGO-000008 avoidance
  excludes_normalise_then_filter : Prop      -- NOGO-000009 avoidance
  excludes_arbitrary_logwidth_tt : Prop      -- NOGO-000006 avoidance
  -- ... etc per NoGo entry

/-- A single NoGo's applicability check. -/
inductive NoGoApplicability where
  | applicable      -- The NoGo applies; the route is dead.
  | not_applicable  -- The NoGo's pattern does not apply.
  | safety_unclear  -- Cannot determine; needs explicit operator review.
  deriving Repr, DecidableEq

/-- The cross-route checker: composes all known NoGos. -/
def crossRouteCheck (cert : ProofSafetyCertificate) : 
    List (String × NoGoApplicability) := [
  ("NOGO-000005", ...),
  ("NOGO-000006", ...),
  ("NOGO-000007", ...),
  ("NOGO-000008", ...),
  ("NOGO-000009", ...),
]
```

### Lemmas / sanity checks

```lean
/-- All known NoGos are listed in the checker. -/
theorem crossRouteCheck.completeness (cert : ProofSafetyCertificate) :
    (crossRouteCheck cert).length = 5 := by decide

/-- Empty safety claim returns "safety_unclear" for all NoGos. -/
theorem crossRouteCheck.empty_safety :
    ∀ p ∈ crossRouteCheck { 
      route_name := "test",
      excludes_support_cardinality_only := False,
      excludes_displayed_syntax_only := False,
      excludes_normalise_then_filter := False,
      excludes_arbitrary_logwidth_tt := False
    }, p.2 = NoGoApplicability.applicable ∨ p.2 = NoGoApplicability.safety_unclear
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `ProofSafetyCertificate`, `NoGoApplicability`, `crossRouteCheck` defined.
- [ ] `completeness` theorem proven kernel-clean (by `decide`).
- [ ] `empty_safety` theorem proven kernel-clean.
- [ ] Module doc-comment cites all five NoGo entries by ID.
- [ ] Smoke test demonstrates: for a route claiming `excludes_X := True` for all X, the checker returns `not_applicable` for all NoGos.
- [ ] At least one concrete `ProofSafetyCertificate` example (e.g., for the V_codexd3a D3'-A geometry).

## Scope

### Allowed
- New modules under `pnp4/Pnp4/KillMachine/`.

### Forbidden
- Universal.
- ❌ **No edits to `outputs/nogolog.jsonl`.**
- ❌ No promotion to `accepted` status of any guard.
- ❌ No "automatic NoGo filing" mechanism — that's operator-only.

## Output
Universal template.
