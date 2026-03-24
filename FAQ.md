# Frequently Asked Questions

Updated: 2026-03-24

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current milestone release checklist:
`RELEASE_RC.md`.

## What is currently proved in code?

Active final surface is in `pnp3/Magnification/FinalResult.lean`:

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`
- `P_ne_NP_final*`

These compile on the current tree.

## Is unconditional `P ≠ NP` proved here?

No. Current `P_ne_NP_final` is conditional.

## Is the active tree axiom-free in the strictest sense?

No. Active `pnp3/` has no project-local `axiom` and no `sorry/admit`, but the
audited theorem surface still uses standard Lean assumptions:
`propext`, `Classical.choice`, `Quot.sound`.

## Можно ли релизить сейчас, а полный путь закрыть потом?

Да, как промежуточный `RC/milestone` релиз.
Правила формулировок и checklist зафиксированы в `RELEASE_RC.md`.

## Conditional on what exactly?

Current default final DAG endpoint requires:

1. `NP_not_subset_PpolyDAG`

## What is the current inclusion-side blocker?

For inclusion itself, no-arg closure is present and already wired into default
final wrappers:
`proved_P_subset_PpolyDAG_internal`.
Remaining work is DAG-separation internalization (`NP_not_subset_PpolyDAG`).

## Is axiom/sorry hygiene clean?

Yes for active `pnp3/`:

- active global `axiom`: 0
- active `sorry/admit`: 0

Use:

```bash
./scripts/check.sh
```

## How to quickly verify current audit surface?

```bash
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean; do
  lake env lean "$f"
done
```

## Where is the longer route map?

See `PROOF_OVERVIEW.md`.
