# SmokeProbe plan — rejection-path tests for the verifier

This file is the plan for `bench/SmokeProbe/`.

**PR 5 status: 5 rejected probes + 1 accepted_shape_only probe shipped**
(per Engineering Execution Plan v0.2.1 fallback "ship 5/8 if Lean-level
rejection is ambiguous"). The driver
`scripts/run_smoke_probes.sh` and the verifier-shell MVP
`scripts/verify_candidate.sh` are also live. The smoke driver is wired
into `scripts/check.sh` as a new step.

The probes serve a single purpose: to demonstrate that the
currently-shipped guards reject every kind of move that the Research
Constitution forbids. This is not a benchmark of *successful*
candidates. The verifier never "accepts" a Lean file as a proof of
P ≠ NP at the smoke-probe stage; it only confirms that the Lean
file's *shape* is well-formed.

This is not a benchmark of *successful* candidates. The verifier never
"accepts" a Lean file as a proof of P ≠ NP at the smoke-probe stage; it
only confirms that the Lean file's *shape* is well-formed.

---

## 1. Files

### Shipped in PR 5

```
bench/SmokeProbe/
  rejected_imports_refuted.lean              -> PR 4a guard
  rejected_phantom_axiom.lean                -> PR 1 guard (Part A)
  rejected_typeclass_payload_channel.lean    -> PR 2 guard
  rejected_unmarked_refuted_route.lean       -> PR 3 guard
  rejected_bare_package_final.lean           -> PR 3b extension of PR 3 guard
  accepted_noop_candidate_shape.lean         -> PASS_SHAPE_ONLY
  expected_results.json                      -> driver source-of-truth
```

The five rejected probes are staged into forbidden zones (per the
`staging_path` field of `expected_results.json`), the named guard is
run, the guard must exit non-zero AND its log must contain the
`expected_log_marker`, and the staged file is removed. The accepted
probe lives permanently in `bench/SmokeProbe/`; all four currently-
shipped guards run against the tree containing it and must each
return 0.

### Deferred (per Engineering Execution Plan v0.2.1 fallback)

The following probes ship in later PRs because their corresponding
guards do not exist yet:

```
bench/SmokeProbe/
  rejected_arbitrary_witness.lean              -> PR 6 / PR 8 (Rule 5)
  rejected_goal_drift.lean                     -> PR 11 (TargetLock)
  rejected_hidden_source_theorem_payload.lean  -> PR 6 / PR 8 (Rule 16 hidden payload at SourceTheorem level)
```

These three are recorded under `deferred_probes` in
`bench/SmokeProbe/expected_results.json` with their target PR.

### Original v0.1 plan placeholders (preserved for reference)

```
  rejected_size_policy_violation.lean
  rejected_collapse_not_contradiction.lean
  accepted_noop_candidate_shape.lean
  expected_results.json
```

`expected_results.json` is the source of truth: each `rejected_*.lean`
must produce `verifier_status = "FAIL"` with a specific
`failure_class`, and `accepted_noop_candidate_shape.lean` must produce a
specific `PASS_SHAPE_ONLY` value.

`accepted_noop_candidate_shape.lean` is **not** an "accepted candidate"
— it is a positive control that proves a benign tautology and only
verifies that the verifier's shape checks pass. Its `final_status` is
`PASS_SHAPE_ONLY`, **never** `accepted`. See Rule 1: a real
`accepted` status requires a closed `P_ne_NP_unconditional`.

---

## 2. Per-probe specification

### 2.1 `rejected_imports_refuted.lean`

A toy candidate that imports a refuted predicate from
`pnp3/RefutedPredicates/` (or from
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`, which
re-exports refuted predicates). Expected verifier output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "refuted_route",
  "rule":            "Rule 6"
}
```

### 2.2 `rejected_arbitrary_witness.lean`

A toy `SourceTheorem_*` whose statement universally quantifies over
`PpolyFormula L` without the
`Π_excludes_hardwiring` lemma (Rule 5). Expected output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "vacuity",
  "rule":            "Rule 5"
}
```

(`failure_class = "vacuity"` is used because the missing exclusion
lemma is what makes the universal quantifier vacuously satisfied by
truth-table hardwiring.)

### 2.3 `rejected_phantom_axiom.lean`

A toy candidate that adds `axiom phantom : ComplexityInterfaces.P_ne_NP`
and uses it. Expected output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "vacuity",
  "rule":            "Rule 1"
}
```

The verifier must reject **before** it even gets to Rule 16; an
introduced axiom in the dependency closure of the final theorem fails
`spec/target.toml::[axioms].allowed`.

### 2.4 `rejected_goal_drift.lean`

A toy candidate that proves `ComplexityInterfaces.P_ne_NP'` for some
locally-redefined `P_ne_NP'` and tries to claim it as the target.
Expected output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "goal_drift",
  "rule":            "Rule 0 / Rule 2"
}
```

### 2.5 `rejected_typeclass_payload_channel.lean`

A toy candidate that introduces

```
class HiddenPayload : Type where
  miracle : ComplexityInterfaces.P_ne_NP

theorem candidate_final [HiddenPayload] : ComplexityInterfaces.P_ne_NP :=
  HiddenPayload.miracle
```

Expected output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "typeclass_payload",
  "rule":            "Rule 16"
}
```

This is the most important probe: it directly demonstrates that the
typeclass-payload channel is closed.

### 2.6 `rejected_size_policy_violation.lean`

A toy candidate whose `SourceTheorem_*` is genuinely small but whose
dependency closure under the algorithm in
`spec/source_theorem_size_policy.md` exceeds `K_exp = 200`. Expected
output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "size_policy_violation",
  "rule":            "Rule 4",
  "size_status":     "human-review-required"
}
```

`verifier_status = "FAIL"` here means the *automated* gate fails; the
`size_status` field signals that the candidate may still be promoted to
human review per Rule 4. The smoke probe asserts only the automated
gate.

### 2.7 `rejected_collapse_not_contradiction.lean`

A toy candidate whose `SourceTheorem_*` is a collapse-style consequence
("if NP ⊆ P/poly then PH collapses") with a bridge that pretends this is
a contradiction. Expected output:

```json
{
  "verifier_status": "FAIL",
  "failure_class":   "collapse_not_contradiction",
  "rule":            "Rule 8"
}
```

### 2.8 `accepted_noop_candidate_shape.lean`

A trivial candidate package whose `SourceTheorem_*` is something like
`True` and whose `gap_from_*` is the absurd

```
gap_from_noop : True → ResearchGapWitness :=
  fun _ => ⟨/- placeholder requiring NP_not_subset_PpolyDAG -/⟩
```

Crucially this candidate **must not** typecheck end-to-end as a proof
of `ResearchGapWitness`. Instead, the smoke probe is run with the
verifier in `--shape-only` mode, which checks only:

- file layout (Rule 3),
- typeclass channels (Rule 16),
- size policy (Rule 4),
- import whitelist (Rule 6),
- forbidden identifiers (`spec/implicit_assumption_channels.md` §4),

without running `lake build`. Expected output:

```json
{
  "verifier_status": "PASS_SHAPE_ONLY",
  "final_status":    "PASS_SHAPE_ONLY"
}
```

`PASS_SHAPE_ONLY` is **not** `accepted` and never appears in
`outputs/survivor_history.jsonl` with `final_status = "accepted"`.

---

## 3. `expected_results.json` schema

```json
[
  {
    "file":            "rejected_imports_refuted.lean",
    "verifier_status": "FAIL",
    "failure_class":   "refuted_route",
    "rule":            "Rule 6"
  },
  {
    "file":            "rejected_arbitrary_witness.lean",
    "verifier_status": "FAIL",
    "failure_class":   "vacuity",
    "rule":            "Rule 5"
  }
  // ...
]
```

The verifier runs each probe and matches actual output to expected. Any
mismatch fails CI.

---

## 4. CI integration

The verifier shell from PR 5 must run `bench/SmokeProbe/` on every PR,
not only on candidate PRs. The reason: a governance or cleanup PR that
inadvertently breaks the verifier is itself a regression we want to
catch immediately.

---

## 5. Out of scope

- No "successful candidate" probes.
- No probes against the actual final target.
- No probes that depend on `FrozenSpec.lean` (yet); those will be added
  after PR 7.
- No probes that depend on `pnp3/Candidates/` infrastructure beyond the
  Rule-3 layout.
