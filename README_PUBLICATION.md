# PNP3: Formal Complexity Pipeline in Lean 4

> **Public-facing status (2026-02-20):** this repository contains a machine-checked,
> but conditional, partial-track pipeline. The active output is
> `NP_not_subset_PpolyFormula` under explicit hypotheses.

## What is verified

- SAL/atlas/capacity infrastructure in Lean.
- Anti-checker and magnification glue in Lean.
- Partial locality-lift bridge plumbing in Lean, including a certificate-driven
  wrapper (`stableRestriction_of_certificate`, `locality_lift_partial_of_certificate`).

## What is still external

1. Localized bridge goals in `pnp3/ThirdPartyFacts/PpolyFormula.lean`
   (`GapPartialMCSPPpolyRealToPpolyFormulaGoal p`).
2. Witness-backed shrinkage inputs in `pnp3/ThirdPartyFacts/Facts_Switching.lean`.
3. Certificate cardinality obligations (`hCardHalf`-style) in
   `pnp3/ThirdPartyFacts/PartialLocalityLift.lean` for the constructive provider path.

## Axiom status

- Active `axiom` declarations in `pnp3/`: **0**.
- Remaining dependencies are explicit hypotheses/goals, not global axioms.

## Source-of-truth documents

- `STATUS.md`
- `TODO.md`
- `AXIOMS_FINAL_LIST.md`
- `AXIOM_ANALYSIS_FINAL.md`

## Reproducibility

```bash
lake build
```

The project currently builds successfully with the status above.
