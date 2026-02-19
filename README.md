# P vs NP Lean Formalization (pnp3)

This repository contains an active Lean 4 formalization pipeline for a Partial-MCSP-based route to `P ≠ NP`.

## Start here
- `docs/README.md` - documentation index
- `docs/CurrentState.md` - exact current proof status
- `docs/Roadmap.md` - prioritized execution plan
- `docs/Publication.md` - publication-safe claim boundaries
- `docs/AuditHandoff.md` - ready-to-run external audit handoff protocol

## Active code tree
- `pnp3/` - active formalization
- `archive/`, `old_attempts/` - historical material (not active proof cone)

## Build and verification
```bash
lake exe cache get
lake build
bash scripts/check.sh
bash scripts/audit_handoff.sh
```

`check.sh` is the canonical consistency guard:
- checks no `sorry`/`admit` in `pnp3/`
- checks axiom inventory and dependency signatures
- checks anti-checker critical files for `False.elim` absence

## Current proof status (short)
- A->B->C->D pipeline is machine-checked.
- Active final theorem is `P_ne_NP_final_asymptotic`.
- The cone has zero project axioms in `pnp3/`, but remains conditional through explicit witness assumptions.

See `docs/CurrentState.md` for full details.
