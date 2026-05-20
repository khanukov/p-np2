# Stage 2 — Barrier / NoGo Audit (Role C)

**Role**: C — Repo Killer.

**Stance**: prosecutor.

## Worker prompt template

```
You are a hostile reviewer for proof attempt <X>.  Your job is to
check the idea against the internal kill-machine:
pnp3/Docs/BARRIER_CATALOGUE.md.

For each entry in the catalogue, answer:
- "Idea matches NoGo <tag> because [mechanism]."
- "Idea does not match NoGo <tag> because [reason]."

For each pattern matcher (support-cardinality, syntax filter,
normalisation filter, universal hWitness, formula certificate
provider, promise-YES / iso-strong forcing), explicitly check.

Verdict: BARRIER_GREEN / BARRIER_YELLOW / BARRIER_RED.

If BARRIER_RED, cite the specific NoGo tag and the matching
mechanism.
```

## Idea under review

(Copy thesis.)

## NoGo catalogue checklist

| NoGo tag | Match? | Mechanism |
|---|---|---|
| NOGO-000004 (prefixAnd) | yes / no | (...) |
| NOGO-000006 (arbitrary ttFormula payload) | yes / no | (...) |
| NOGO-000008 (syntax-rewrite normalisation) | yes / no | (...) |
| NOGO-000009 (normalisation meta-barrier) | yes / no | (...) |
| Probe 13 (FormulaCertificateProviderPartial) | yes / no | (...) |
| isoStrong L1 chain | yes / no | (...) |
| Iso-strong route closures | yes / no | (...) |
| Support-bounds family | yes / no | (...) |

## Pattern matchers

- **Support-cardinality** based proof: yes / no / partial.
- **Syntax filter** on formula shapes: yes / no / partial.
- **Normalisation filter**: yes / no / partial.
- **Universal `hWitness`** over arbitrary witness type: yes / no.
- **Formula certificate provider**: yes / no.
- **Promise-YES / iso-strong forcing**: yes / no.
- **Pigeonhole over candidate trace counting** on Gap-MCSP: yes /
  no.

## Pending external NoGo proposals (from external_barriers_audit_D0)

- NOGO-EXT-NATURAL-PROOFS: applies if support / shrinkage /
  restriction.  yes / no.
- NOGO-EXT-LOCALITY-BARRIER-SEARCH-MCSP: applies if route uses
  Search-MCSP magnification.  yes / no.
- NOGO-EXT-MAGNIFICATION-THRESHOLD-GAP: applies if bound is in
  achievable regime.  yes / no.

## Final verdict

**`BARRIER_GREEN` / `BARRIER_YELLOW` / `BARRIER_RED`**

(If RED, cite specific NoGo tag and matching mechanism.)
