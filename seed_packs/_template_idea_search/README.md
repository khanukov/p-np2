# Template seed pack — idea-search pipeline

This is the **template directory** for the idea-search pipeline
defined in `pnp3/Docs/IDEA_SEARCH_PIPELINE.md`.

To start a new idea evaluation:

1. Copy this directory to `seed_packs/<idea_name>/`.
2. Replace `<idea_name>` with a short, descriptive slug.
3. Dispatch Role A to fill `stage1_idea_card.md`.
4. Dispatch Role B to fill `stage1_literature_kill.md`.
5. Operator reviews; if `LIT_GREEN` or `LIT_YELLOW`, proceed.
6. Dispatch Role C to fill `stage2_barrier_nogo.md` and
   `stage3_repo_surface.md`.
7. Operator reviews; if both `BARRIER_GREEN`/`YELLOW` and
   `REPO_GREEN`/`YELLOW`, proceed.
8. Dispatch Role D to fill `stage4_self_attack.md`.
9. Operator reviews; if `SELF_GREEN` or `SELF_YELLOW`, proceed.
10. Dispatch Role E to attempt Stage 5 Lean L0 probe.
11. Only Stage-5-green-bridge ideas proceed to Stage 6
    implementation.

Files in this template:

- `README.md` — this file.
- `stage1_idea_card.md` — Role A output.
- `stage1_literature_kill.md` — Role B output.
- `stage2_barrier_nogo.md` — Role C output (NoGo audit).
- `stage3_repo_surface.md` — Role C output (wrapper audit).
- `stage4_self_attack.md` — Role D output.
- `stage5_L0_probe/` — Role E output (if reached).
- `stage6_implementation/` — full chain (if reached).
- `verdict.md` — final outcome.

Per-stage files include worker prompt templates that can be
dispatched to AI engineers.
