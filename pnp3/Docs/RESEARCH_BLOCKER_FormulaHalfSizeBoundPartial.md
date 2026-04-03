# Research Note: `FormulaHalfSizeBoundPartial`

Global blocker checklist:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

Date: 2026-02-22
Status: Open research note (optional route)

Current-scope note (2026-04-03):
this is a local formula-side research note. It is not the current repository-
wide blocker summary and should not be read as the active execution plan for
the DAG/final-theorem layers.

## Scope clarification

`FormulaHalfSizeBoundPartial` is still an available interface in
`pnp3/Magnification/LocalityProvider_Partial.lean`, but it is **not** the only
active constructive route anymore.

The certificate-first path now exists and is wired through:

- `FormulaCertificateProviderPartial`
- `constructiveLocalityEnginePartial_of_formulaCertificate`
- `HalfTableCertificateBound` auto export

So this note tracks an **alternative half-size route**, not the mandatory
critical path.

## Why it may still matter

If one wants a half-size-only default provider path without certificate
construction, proving `FormulaHalfSizeBoundPartial` would still be useful.

## Not required for current main constructive plumbing

The old milestone labels mentioned in this note are local to the formula-side
subtrack. They are not the current top-level roadmap labels for the repository.
