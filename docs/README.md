# Documentation Index

This directory is the single entry point for project documentation.

## Read first
- `docs/CurrentState.md` - exact current proof status, active axiom/witness dependencies, and dependency cone.
- `docs/Roadmap.md` - prioritized execution plan (what is done, what is next, what blocks unconditionality).
- `docs/Publication.md` - publication-facing claims, guarantees, and limitations.

## Source-of-truth checks
- `scripts/check.sh` is the canonical automated documentation/proof-consistency guard.
- Axiom audits:
  - `pnp3/Tests/AxiomsAudit.lean`
  - `pnp3/Tests/CoreConeAxiomsAudit.lean`
  - `pnp3/Tests/AntiCheckerConeAxiomsAudit.lean`

## Technical deep dives (module-local docs)
- `pnp3/Docs/Parameters.md`
- `pnp3/Docs/SOURCES.md`
- `pnp3/Docs/PsubsetPpolyIntegration.md`
- `pnp3/Docs/MultiSwitching_NextStep.md`
- `pnp3/Docs/MultiSwitching_DepthInduction_TODO.md`
