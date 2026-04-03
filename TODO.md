# TODO / Roadmap (current)

Updated: 2026-04-03

Canonical checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release wording guardrail:
`RELEASE_RC.md`.
Current DAG plan:
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Snapshot

- Active `axiom` in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes.
- Inclusion is already internalized.
- The remaining work is theorem-level, not endpoint plumbing.

## The Two Remaining Closure Targets

### Target 1. Remove external `hNPDag`

Current public default theorem still requires:

```text
hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

The fastest honest route is now fixed-slice:

1. choose
   `p* := hMag.antiChecker.asymptotic.pAt n hn`;
2. prove one source theorem on `p*`, ideally
   `gapPartialMCSP_supportHalfObligation p*`;
3. feed it through the already compiled asymptotic fixed-slice wrappers.

### Target 2. Remove remaining public `hMag`

Even after `hNPDag` is internalized, the public theorem is not yet zero-arg.
The current default wrapper still takes `hMag` for compatibility.

To reach a genuinely unconditional top-level theorem, we still need either:

1. a concrete fixed-slice `GapPartialMCSP_TMWitness p*` plus a fixed-slice DAG
   blocker, routed through `_TM` wrappers; or
2. an internal proof of the current magnification-assumption package.

## Execution Order

### Task 1. Keep docs and audit wording honest

Status: done for the current snapshot.

Rule:

- do not say the repository proves unconditional `P ≠ NP`;
- distinguish clearly between
  `remove hNPDag from the current route`
  and
  `produce a zero-argument final theorem`.

### Task 2. Close one fixed-slice DAG source theorem

Status: active blocker.

Preferred theorem targets:

1. `gapPartialMCSP_supportHalfObligation p*`
2. `dagRouteBSourceBlocker p*`
3. `dag_stableRestriction_producer p*`

Acceptance condition:

- one of the asymptotic fixed-slice wrappers becomes internally callable with
  no external DAG hypothesis.

### Task 3. Internalize `NP_not_subset_PpolyDAG`

Status: pending on Task 2.

Possible routes:

1. fixed-slice blocker + asymptotic collapse, if the goal is to clean up the
   existing `hMag`-based public surface;
2. concrete fixed slice + `_TM` wrapper, if the goal is a standalone theorem
   with no magnification package;
3. canonical all-slices witness-transfer route, if the goal is a stronger
   theorem program not tied to the current fixed-slice integration path.

### Task 4. Replace the current compatibility final theorem

Status: pending on Task 3.

Current theorem:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

Required end state:

- a zero-argument public theorem, or at minimum
- a theorem with no external DAG separation input.

### Task 5. Preserve the all-slices research track without mistaking it for the immediate blocker

Status: active as parallel theorem program, not as the shortest integration
task.

Existing infrastructure already covers:

- witness easy density,
- witness uniform lower,
- witness transfer quarter,
- compilers from extraction/support budgets,
- support-half family fallback builders.

The remaining debt there is source mathematics, not glue.

### Task 6. Final consistency pass after theorem closure

Status: pending.

Do after the theorem work, not before:

1. switch `README.md`, `STATUS.md`, `TODO.md`, `CHECKLIST_*`, and publication
   docs to unconditional wording only after the public theorem is actually
   unconditional;
2. rerun:

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean; do
  lake env lean "$f"
done
```

## Non-Goals Right Now

- Do not add new endpoint wrappers just to create apparent progress.
- Do not relabel the canonical all-slices route as “done” while it still lacks
  the source theorem.
- Do not claim that removing `hNPDag` automatically yields full
  unconditionality while `hMag` still appears in the public theorem surface.
