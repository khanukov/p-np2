# L0 iso-strong conclusion probe (handle: codex)

## Scope and outcome

- Staging Lean file added: `pnp3/Tests/IsoStrongConclusionProbe.lean`.
- Report file added: `seed_packs/isoStrong_conclusion_L0/reports/L0_isoStrong_conclusion_codex.md`.
- No other files changed.

## What landed in Lean

I did not force a fake GREEN/RED endpoint. Instead, I landed two kernel-checked
L0 helper theorems that are useful for L1:

1. `isoStrong_canonical_forcing_payload`
   - Exact unpacking of the canonical `IsoStrongFamilyEventually` witness into
     explicit forcing + slack data.
2. `isoStrong_canonical_forcing_at`
   - A fixed-`(n,β)` instantiation corollary that extracts a YES center from
     the forcing branch under admissibility premises.

These theorems are nontrivial infrastructure for the next proof step, because
L1 can now focus only on the combinatorial contradiction/construction core
without re-unpacking outer eventual quantifiers.

## Why full GREEN/RED did not land at L0

Direction N (recommended) needs a complete formal pigeonhole bridge from:

- canonical counting (`sYES = 1` giving small YES classes),
- slack bound `Mof < 2^(tableLen - κ)`,
- agreement-subcube cardinality and valid-encoding closure,

to a concrete `z` that agrees on `D` but is outside YES.

In this repository, the heaviest missing step at L0 is a reusable lemma that
connects `AgreeOnValues`/`ValidEncoding` with explicit finite-cardinality lower
bounds on valid agreement extensions for canonical slices. That bridge appears
L1-sized rather than a safe ≤300-LOC L0 landing.

## Commands executed

- `lake build PnP3 Pnp4`
- `./scripts/check.sh`
- `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4`
- `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/IsoStrongConclusionProbe.lean`

## Verdict

YELLOW_PARTIAL_LANDING
