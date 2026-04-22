# FormulaSupportRestrictionBoundsPartial Falsifiability Audit

Branch audited: `origin/claude/check-unconditional-requirements-Dg8ZQ`

Tip audited: `23cd321845b956e2fd4b11b064a810c225a79436`

Date: 2026-04-22

## Target

The audited assumption is:

- `Magnification.FormulaSupportRestrictionBoundsPartial`
- Defined in `pnp3/Magnification/LocalityProvider_Partial.lean`

It states that for every strict formula witness
`PpolyFormula (gapPartialMCSP_Language p)`, the selected formula's syntactic
support satisfies the polylog/local-circuit/quarter-support bounds consumed by
the locality route.

## Formal Probes

I checked two Lean probes in `/tmp/pnp3_formula_support_falsifiability_probe.lean`.
The probe compiled with:

```bash
lake env lean /tmp/pnp3_formula_support_falsifiability_probe.lean
```

### Probe 1: incompatibility with fixed-slice PpolyDAG

Lean proves:

```lean
theorem formulaSupportBounds_imply_fixedSlice_not_ppolyDAG
    {p : GapPartialMCSPParams}
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    ¬ ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)
```

Reason:

1. `hBounds` plus the fixed-slice DAG-to-formula bridge
   `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice p`
   yields `LowerBounds.dag_stableRestriction_producer p`.
2. `LowerBounds.no_fixedSlice_stableRestriction_of_inPpolyDAG` says that this
   producer is incompatible with any fixed-slice `PpolyDAG` witness.

This already shows that `FormulaSupportRestrictionBoundsPartial` is not merely
a harmless packaging assumption: it rules out fixed-slice `PpolyDAG`.

### Probe 2: direct contradiction from trivial fixed-slice formula hardwiring

I then added a local truth-table DNF construction for arbitrary Boolean
functions over `Bitstring n` and proved:

```lean
theorem fixedSlice_gapPartialMCSP_in_PpolyFormula
    (p : GapPartialMCSPParams) :
    PpolyFormula (gapPartialMCSP_Language p)
```

The construction is standard non-uniform hardwiring:

1. At the single active input length `partialInputLen p`, use a full truth-table
   formula for `gapPartialMCSP_Language p`.
2. At every other input length, use `FormulaCircuit.const false`.
3. The polynomial bound is allowed to choose a fixed exponent/constant large
   enough for this one hardwired slice.

Combining this fixed-slice formula witness with the existing internal-provider
payload theorem:

```lean
LowerBounds.abstractGapTargetedSingletonDensityPayload_of_internal_provider
```

and the existing support-bounds contradiction consumer:

```lean
LowerBounds.false_of_abstractGapTargetedPayload_of_supportBounds
```

Lean proves:

```lean
theorem formulaSupportBounds_false_for_fixedSlice
    {p : GapPartialMCSPParams}
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    False
```

So, for every available `GapPartialMCSPParams p`, the current
`FormulaSupportRestrictionBoundsPartial` assumption is formally inconsistent.

## Conclusion

`FormulaSupportRestrictionBoundsPartial` is falsified by the current formal
environment.

It is not just a strong residual mathematical hypothesis. In combination with
already-present fixed-slice hardwiring and support-bounds consumers, it implies
`False`.

The source of the problem is that the assumption quantifies over every
`PpolyFormula (gapPartialMCSP_Language p)`. But a fixed-slice language is
trivially in `PpolyFormula` by non-uniform truth-table hardwiring, and that
trivial formula is then fed into a pipeline that treats support bounds as if
they were meaningful lower-bound structure.

## Required Fix Direction

`FormulaSupportRestrictionBoundsPartial` should not quantify over arbitrary
fixed-slice `PpolyFormula` witnesses.

Possible repairs:

1. Restrict it to a nontrivial asymptotic/global formula family, not a
   one-slice hardwired witness.
2. Add provenance excluding truth-table/hardwired fixed-slice formulas.
3. Replace the support assumption with a statement about formulas produced by
   a specific AC0/multi-switching extraction pipeline.
4. Keep it only as a deliberately inconsistent no-go probe, not as an active
   final-route assumption.

Until this is repaired, any theorem depending on
`FormulaSupportRestrictionBoundsPartial` cannot be interpreted as progress
toward an unconditional proof.
