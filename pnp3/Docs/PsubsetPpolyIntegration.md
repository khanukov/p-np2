# `P ⊆ P/poly` status in `pnp3`

Scope note:
for unconditional `P ≠ NP` blockers see
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

Update note (2026-04-03):
this file is inclusion-only and should not be read as the current global status
of the DAG-separation or final-theorem layers.

## Current state

`pnp3` no longer depends on the external package `Facts/PsubsetPpoly`.
The constructive inclusion `P ⊆ P/poly` used by the main pipeline is now
internalized under:

- `pnp3/Complexity/PsubsetPpolyInternal/Bitstring.lean`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`
- `pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean`

## Build workflow

Use the standard repository build:

```bash
cd /root/p-np2
lake build
```

No separate build of `Facts/PsubsetPpoly` is required.
