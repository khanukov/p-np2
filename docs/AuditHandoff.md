# Auditor Handoff

Last updated: 2026-02-19

This document is the operational handoff for third-party audit of the active proof cone.

## Audit scope
- In scope: `pnp3/` (active Lean formalization tree).
- Out of scope: `archive/`, `old_attempts/`, `experiments/` (historical or sandbox material).

## Canonical claim boundary
- Machine-checked: A->B->C->D pipeline in `pnp3/` and the formal implication route to `P ≠ NP`.
- Final theorem in active cone: `P_ne_NP_final_asymptotic`.
- Current status is conditional (theorem-interface assumptions), not unconditional.

Primary references:
- `docs/CurrentState.md`
- `docs/Publication.md`
- `docs/Roadmap.md`

## Reproducibility protocol
Run exactly:

```bash
lake exe cache get
lake build
bash scripts/check.sh
```

What `scripts/check.sh` enforces:
- no `sorry`/`admit` in `pnp3/`
- no project axioms in `pnp3/` (`axiom` count must be `0`)
- fixed axiom-signature checks for:
  - `pnp3/Tests/AxiomsAudit.lean`
  - `pnp3/Tests/CoreConeAxiomsAudit.lean`
  - `pnp3/Tests/AntiCheckerConeAxiomsAudit.lean`
- no `False.elim` in critical anti-checker files
- publication/doc consistency checks

## One-command audit artifact generation
To generate timestamped logs for attachment to an audit report:

```bash
bash scripts/audit_handoff.sh
```

This writes:
- `artifacts/audit/<UTC-timestamp>/env.txt`
- `artifacts/audit/<UTC-timestamp>/git.txt`
- `artifacts/audit/<UTC-timestamp>/build.log`
- `artifacts/audit/<UTC-timestamp>/check.log`
- `artifacts/audit/<UTC-timestamp>/axioms.log`

## Known limitations (must be stated explicitly)
- No project axioms remain in `pnp3/`.
- Final cone remains conditional via explicit witness assumptions in theorem interfaces
  (see `MagnificationAssumptions` in `pnp3/Magnification/FinalResult.lean`).
- Therefore the current repository state does not justify an unconditional in-repo proof claim.

## Reviewer quick checklist
1. Verify commit hash and dirty/clean state from `git.txt`.
2. Verify `build.log` and `check.log` both end successfully.
3. Verify `check.log` reports:
   - `Axiom inventory OK (0 axioms).`
   - all three axiom audits OK.
4. Verify `axioms.log` shows base Lean axioms only for audited theorem set.
5. Confirm public claim text matches `docs/Publication.md`.
