# Final verdict (retroactive)

| Stage | Verdict | Mechanism |
|---|---|---|
| Stage 1 (Idea Card) | n/a | self-assessed novelty: LOW |
| Stage 1 (Literature Kill) | LIT_YELLOW | folklore-adjacent; counting argument is well-known |
| Stage 2 (Barrier / NoGo) | BARRIER_YELLOW | adjacent to locality barrier (Chen et al. JACM 2022); not a direct kill |
| Stage 3 (Repo Surface) | REPO_GREEN | genuine technical content (specific forcing condition) |
| Stage 4 (Self-Attack) | **SELF_RED** | killed at Attack 1 by trace counting |
| Stage 5 (L0 Probe) | n/a — not reached | (would never have been dispatched) |

## Final outcome

**CLOSED_AT_STAGE_4 (retroactive)** — killed by the trace-counting
observation:

```
|Size1Candidate n| = n + 2  <<  2^|free rows|  for any free
                                              row set of size
                                              ≥ log₂(n + 3)
```

The iso-strong forcing condition cannot be satisfied because the
size-1 candidate trace image is strictly smaller than the Boolean
labeling space on the free rows.

## Cited barriers / NoGo entries

- (Inline) folklore trace-counting observation, in the spirit of:
  - Razborov-Rudich JCSS 1997 (natural proofs intuition — selective
    properties on small classes).
  - Chen et al. JACM 2022 (locality barrier — magnification targets
    admit highly-efficient circuits with oracle extensions).
- Neither is a direct citation kill; the immediate kill is a
  Stage 4 self-attack.

## Lessons learned

1. **The trace-counting check should be elevated to a standard
   sanity check in Stage 4** for any idea involving forcing /
   selectivity / structural conditions on YES sets.
2. **`pnp3/Docs/BARRIER_CATALOGUE.md` should include this pattern
   matcher** explicitly: "selective property on canonically-small
   YES set + forcing over canonically-large free space → killed by
   counting".
3. **The audit chain's actual L0 + L1 work, although verbose, did
   correctly arrive at the same kill** — but at ~50× the
   engineering cost.  The pipeline's value is not in changing the
   outcome but in **accelerating it**.

## Cost comparison

| Approach | Cost | Outcome |
|---|---|---|
| Actual (without pipeline) | ~3 weeks formal engineering, 15 PRs, ~700 LOC Lean | Iso-strong route closed |
| Pipeline (retroactive) | ~5 hours Role A–D + ~1 hour operator review | Iso-strong route closed |

**Force multiplier**: ~25–50×.

This is the **strongest argument** for the pipeline as repository
policy.
