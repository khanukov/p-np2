# Stage 5 — Minimal Lean L0 Probe (Role E)

**Role**: E — Lean Probe Engineer.

**Stance**: agnostic — implementer, not advocate.

## Worker prompt template

```
You are a Lean engineer for proof attempt <X>.  The idea has
passed Stages 1–4.  Your job: write a MINIMAL Lean test-local
file that either (a) proves a route-killer in the style of
isoStrong_conclusion_negative_general, or (b) closes ONE concrete
bridge lemma without claiming the full conclusion.

HARD DISCIPLINE:
- ≤ 500 LOC of new Lean.
- Test-local under pnp3/Tests/ or pnp4/Pnp4/Tests/.
- No endpoint, no spec, no JSONL, no NoGoLog, no known_guards,
  no trust-root edits.
- No ResearchGapWitness, no SourceTheorem, no gap_from,
  no endpoint, no P ≠ NP claim.
- No axiom / opaque / sorry / admit / native_decide.

Register the module in lakefile.lean.

Verify locally:
- lake build <module> -> success
- lake build PnP3 Pnp4 -> success
- ./scripts/check.sh -> exit 0
- #print axioms <new theorems> -> standard kernel axioms only

Report: stage5_L0_probe.md with:
- What landed (theorem names + axiom evidence).
- What did NOT land and why.
- Verdict: L0_GREEN_BRIDGE / L0_RED_KILLED / L0_YELLOW_PARTIAL /
  L0_FAILED.
```

## L0 attempt summary

(To be filled by Role E when L0 probe is dispatched.)

## Files in this directory

- `README.md` — this file.
- `stage5_L0_probe.md` — Role E final report.
- The actual Lean file lives in `pnp3/Tests/` or `pnp4/Pnp4/Tests/`,
  not here.
