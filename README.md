# P vs NP Lean Formalization (pnp3)

This repository contains an active Lean 4 formalization pipeline for a Partial-MCSP-based route to `P ≠ NP`.

## Start here
- `docs/README.md` - documentation index
- `docs/CurrentState.md` - exact current proof status
- `docs/Roadmap.md` - prioritized execution plan
- `docs/Publication.md` - publication-safe claim boundaries

## Active code tree
- `pnp3/` - active formalization
- `archive/`, `old_attempts/` - historical material (not active proof cone)

## Build and verification
```bash
lake exe cache get
lake build
bash scripts/check.sh
```

`check.sh` is the canonical consistency guard:
- checks no `sorry`/`admit` in `pnp3/`
- checks axiom inventory and dependency signatures
- checks anti-checker critical files for `False.elim` absence

## Current proof status (short)
- A->B->C->D pipeline is machine-checked.
- Final theorem cone is currently conditional on one project-specific scaffold:
  - `ThirdPartyFacts.localizedFamilyWitness_partial`

See `docs/CurrentState.md` for full details.
