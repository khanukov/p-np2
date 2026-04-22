# Provenance: FormulaSupportRestrictionBoundsPartial Falsifiability Audit

Audited branch:

```text
origin/claude/check-unconditional-requirements-Dg8ZQ
```

Audited commit:

```text
23cd321845b956e2fd4b11b064a810c225a79436
```

Commands run:

```bash
git fetch origin
git rev-parse origin/claude/check-unconditional-requirements-Dg8ZQ
git switch --detach origin/claude/check-unconditional-requirements-Dg8ZQ
lake env lean /tmp/pnp3_formula_support_falsifiability_probe.lean
```

Key source files read:

```text
pnp3/Magnification/LocalityProvider_Partial.lean
pnp3/LowerBounds/SingletonDensityContradiction.lean
pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean
pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean
pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean
pnp3/Complexity/Interfaces.lean
pnp3/Models/Model_PartialMCSP.lean
```

Temporary Lean probe:

```text
/tmp/pnp3_formula_support_falsifiability_probe.lean
```

The probe was not added to the Lean project. It was used only to type-check the
audit claims against the current branch.
