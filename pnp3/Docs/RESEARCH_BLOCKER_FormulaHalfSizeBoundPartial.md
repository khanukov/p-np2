# Research Note: `FormulaHalfSizeBoundPartial`

Global blocker checklist:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

Date: 2026-02-22
Status: Open research note (optional route)

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

I-4 is now closed for the explicit AC0/CNF path (Path A).  Remaining core
work is provider-default closure (I-2) and the final formula-to-`P/poly`
bridge layer (I-5).
