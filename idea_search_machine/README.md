# Idea Search Machine

Production-grade automation of the six-stage idea-search pipeline
specified in `pnp3/Docs/IDEA_SEARCH_PIPELINE.md`.

This tool dispatches an LLM (Anthropic Claude) through the five
prosecutorial roles (A — Idea Generator; B — Literature Killer;
C — Repo Killer; D — Self-Attack Engineer) and registers
survivors as seed packs ready for Stage 5 (Minimal Lean L0 Probe)
by a human engineer.

## Scope

- **In scope**: Stages 1–4 (idea generation + three kill audits +
  self-attack).  All markdown-only.
- **Boundary**: Stage 5 (Lean L0 probe) and Stage 6
  (implementation) are **human work**.  The machine registers
  survivors but does NOT auto-write Lean.

## Quick start

```bash
# 1. Install dependencies
pip install -r idea_search_machine/requirements.txt

# 2. Set Anthropic API key
export ANTHROPIC_API_KEY=sk-ant-...

# 3. Generate one idea card
python -m idea_search_machine.machine generate --count 1

# 4. Run all audit stages on the generated idea (replace ID)
python -m idea_search_machine.machine audit <idea_id> --stage all

# 5. List registry status
python -m idea_search_machine.machine status

# Optional: dry-run with mock LLM (no API key needed)
python -m idea_search_machine.machine generate --count 3 --mock
python -m idea_search_machine.machine audit <idea_id> --stage all --mock
```

## Architecture

```
idea_search_machine/
├── README.md
├── requirements.txt
├── machine.py                       # CLI entrypoint
├── llm.py                           # Anthropic API abstraction + mock mode
├── registry.py                      # idea storage (JSONL index + per-idea dirs)
├── stages/
│   ├── stage0_generate.py           # Role A: idea card generation
│   ├── stage1_literature_kill.py    # Role B: literature kill audit
│   ├── stage2_barrier_nogo.py       # Role C: barrier / NoGo audit
│   ├── stage3_repo_surface.py       # Role C: repo wrapper audit
│   └── stage4_self_attack.py        # Role D: self-attack probe
├── prompts/                         # markdown prompt templates
│   ├── role_a_idea_card.md
│   ├── role_b_literature_kill.md
│   ├── role_c_barrier_audit.md
│   ├── role_c_repo_surface.md
│   └── role_d_self_attack.md
├── tools/
│   ├── extract_routes.py            # scan pnp3/pnp4 for live routes
│   └── run_check.py                 # invoke ./scripts/check.sh wrapper
└── registry/
    ├── index.jsonl                  # one line per idea: id + verdicts
    └── ideas/<idea_id>/             # per-idea seed pack
        ├── idea.json                # structured metadata
        ├── stage1_idea_card.md
        ├── stage1_literature_kill.md
        ├── stage2_barrier_nogo.md
        ├── stage3_repo_surface.md
        ├── stage4_self_attack.md
        └── verdict.md
```

## Per-stage behaviour

Each stage runs an LLM with a **prosecutorial system prompt**
(see `prompts/`).  The output is parsed for the verdict label
(`LIT_GREEN`, `LIT_YELLOW`, `LIT_RED`, `LIT_UNKNOWN`, etc.) and
the full markdown report.  The verdict updates the idea's
metadata; the markdown is saved as a stage report.

If a stage returns a `RED` verdict, the idea is closed and
subsequent stages are skipped.  If a stage returns `UNKNOWN`,
the idea is **parked** — not promoted, not killed.

## Survivor → Seed Pack

After Stage 4, surviving ideas (all stages `GREEN` or `YELLOW`)
are exported as proper seed packs under
`seed_packs/idea_<idea_id>/` following the existing project
convention.  These are the seeds a human engineer picks up for
Stage 5 Lean L0 probe.

## Mock mode

`--mock` flag uses canned LLM responses for development /
testing without an API key.  Useful for:

- Verifying CLI argument handling.
- Smoke-testing the pipeline plumbing end-to-end.
- Reviewing prompt templates without API spend.

Mock responses are deterministic and intentionally biased toward
exercising every verdict path (`GREEN`, `YELLOW`, `RED`,
`UNKNOWN`) over a few sample runs.

## Limits and honest framing

This machine is a **funnel for AI-generated proof-attempt
candidates**.  Its primary value is:

1. **Throughput**: processing many candidate ideas faster than
   any human can.
2. **Discipline**: enforcing the prosecutorial role separation
   from the pipeline spec.
3. **Documentation**: each killed idea contributes to the
   project's barrier catalogue.

It is **not** a research breakthrough generator.  AI-generated
idea cards will mostly be recombinations of training-data folklore
and will be killed at Stages 1–3 in bulk.  Genuinely novel ideas
must come from outside.

## Connection to repository policy

This tool implements the policy defined in:

- `pnp3/Docs/IDEA_SEARCH_PIPELINE.md` — six-stage pipeline.
- `pnp3/Docs/BARRIER_CATALOGUE.md` — barrier / NoGo reference.
- `pnp3/Docs/CLOSURE_ROUTE_POLICY.md` — closure-route framing.

Survivors registered by this machine become seed packs that
follow the existing `seed_packs/` convention.  Lean engineering
on a survivor proceeds via the standard parallel-codex-dispatch
+ verify + merge + close pattern used throughout the audit chain.

## Operator responsibilities (cannot be automated)

- Approve registry entries before they become formal seed packs.
- Review all Stage 4 `SELF_GREEN` verdicts (strongest signal).
- Decide which survivors to dispatch to Lean L0 probe.
- Manage the parallel-dispatch + curation cycle for Stage 5+.

The machine is a **force multiplier for operator attention**,
not a replacement for it.
