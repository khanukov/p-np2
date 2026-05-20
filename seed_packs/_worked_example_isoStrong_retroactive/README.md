# Worked example: iso-strong refutation retrofitted through the pipeline

This directory is a **retroactive case study** showing how the
idea-search pipeline (`pnp3/Docs/IDEA_SEARCH_PIPELINE.md`) would
have processed the iso-strong-route proof attempt **before** the
project spent ~3 weeks formalising its refutation.

## What actually happened (without the pipeline)

The project pursued the iso-strong route across:

- L0 D0 audit (`post_pr13_provider_retarget_D0` opus47).
- L0 D0 audit (`asymptotic_isostrong_route_audit_D0` gpt55, PR
  #1378).
- L0 (`hInDag_triviality_probe_L0` gpt55, PR #1388).
- L0 D0 (`global_hInDag_contract_repair_D0` codex53, PR #1396).
- L0 (`global_hInDag_contract_L0` gpt55, PR #1404).
- L0 D0 (`isoStrong_conclusion_audit_D0` codex53, PR #1407).
- L0 (`isoStrong_conclusion_L0` codex, PR #1413).
- L1 sessions 1–4 (`isoStrong_conclusion_L1`, PRs #1416, #1423,
  #1427, #1433).
- L1 chain (`general_isoStrong_no_go` D0 + L0 + L1 sessions 1–4 +
  route closure).

Total formal engineering work: ~3 weeks of operator time +
parallel codex engineers, producing ~15 PRs and ~700 lines of
kernel-checked Lean.

## What the pipeline would have done

This backfill shows the route would have been **killed at Stage
4 (Self-Attack) in ~30 minutes** by a single observation about
trace counting.

The retroactive walkthrough below uses the same six-stage pipeline.

## Files in this directory

- `stage1_idea_card.md` — Role A retroactive write-up.
- `stage1_literature_kill.md` — Role B retroactive write-up
  (verdict: LIT_YELLOW — folklore-adjacent, no direct kill).
- `stage2_barrier_nogo.md` — Role C retroactive write-up
  (verdict: BARRIER_YELLOW — adjacent to locality barrier).
- `stage3_repo_surface.md` — Role C retroactive write-up
  (verdict: REPO_GREEN — genuine technical content).
- `stage4_self_attack.md` — Role D retroactive write-up
  **(verdict: SELF_RED — killed at Attack 1, trace-counting
  observation)**.
- `verdict.md` — final outcome.

## Lesson

The pipeline would have:

- Cost: ~30 min Role D effort + ~30 min operator review.
- Saved: ~3 weeks formal engineering + ~15 PRs of churn.

The pipeline is therefore validated as a force-multiplier for
operator attention.  The cost of running Stages 1–4 on a typical
idea (~5 hours total Role A–D effort) is dramatically less than
the cost of formalising a folklore refutation.

This is the **strongest single argument** for adopting the
pipeline as repository policy.
