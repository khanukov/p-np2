"""CLI entry point for the Idea Search Machine.

See ``idea_search_machine/README.md`` for usage.  This module is
intentionally thin — heavy logic lives in ``stages/`` and ``registry``.
"""

from __future__ import annotations

import json
import sys
from typing import Optional

try:
    import click
except ImportError:  # pragma: no cover
    sys.stderr.write(
        "click package required; pip install -r idea_search_machine/requirements.txt\n"
    )
    raise

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient
from idea_search_machine.stages import (
    stage0_generate,
    stage1_literature_kill,
    stage2_barrier_nogo,
    stage3_repo_surface,
    stage4_self_attack,
)


DEFAULT_MODEL = "claude-sonnet-4-6"


def _llm(model: str, mock: bool) -> LLMClient:
    return LLMClient(model=model, mock=mock)


@click.group()
def cli() -> None:
    """Idea Search Machine — automated funnel for proof-attempt evaluation.

    Implements the six-stage pipeline from
    ``pnp3/Docs/IDEA_SEARCH_PIPELINE.md``.  Stages 1-4 are automated;
    Stage 5 (Lean L0 probe) and Stage 6 (implementation) are human
    work and are registered for follow-up rather than auto-executed.
    """


@cli.command()
@click.option("--count", default=1, type=int, show_default=True,
              help="Number of fresh idea cards to generate.")
@click.option("--mock/--no-mock", default=False, show_default=True,
              help="Use canned LLM responses (no API key required).")
@click.option("--model", default=DEFAULT_MODEL, show_default=True)
def generate(count: int, mock: bool, model: str) -> None:
    """Stage 0: generate fresh idea cards via Role A."""
    llm = _llm(model, mock)
    for _ in range(count):
        idea = stage0_generate.run(llm)
        click.echo(f"Generated {idea.id} (target={idea.target_interface!r}, novelty={idea.novelty_self_assessment!r})")


def _stage_dispatch(stage: str, llm: LLMClient, idea: registry.Idea) -> registry.StageResult:
    if stage == "1":
        return stage1_literature_kill.run(llm, idea)
    if stage == "2":
        return stage2_barrier_nogo.run(llm, idea)
    if stage == "3":
        return stage3_repo_surface.run(llm, idea)
    if stage == "4":
        return stage4_self_attack.run(llm, idea)
    raise ValueError(f"unknown stage {stage}")


@cli.command()
@click.argument("idea_id")
@click.option("--stage", "stage_choice",
              type=click.Choice(["1", "2", "3", "4", "all"]),
              default="all", show_default=True)
@click.option("--mock/--no-mock", default=False, show_default=True)
@click.option("--model", default=DEFAULT_MODEL, show_default=True)
def audit(idea_id: str, stage_choice: str, mock: bool, model: str) -> None:
    """Run audit stages (1-4) on an existing idea.

    If ``--stage all`` is selected, stages run sequentially and stop at
    the first RED / UNKNOWN verdict.
    """
    idea = registry.load_idea(idea_id)
    llm = _llm(model, mock)
    if stage_choice == "all":
        for s in ["1", "2", "3", "4"]:
            sr = _stage_dispatch(s, llm, idea)
            click.echo(f"  stage {s}: {sr.verdict}")
            if "RED" in sr.verdict or "UNKNOWN" in sr.verdict:
                click.echo(f"  -> halted at stage {s} ({sr.verdict})")
                break
    else:
        sr = _stage_dispatch(stage_choice, llm, idea)
        click.echo(f"  stage {stage_choice}: {sr.verdict}")

    click.echo(f"final verdict: {idea.final_verdict}")


@cli.command()
def status() -> None:
    """Show registry statistics."""
    counts = registry.status_summary()
    click.echo(json.dumps(counts, indent=2, sort_keys=True))


@cli.command()
def survivors() -> None:
    """List ideas registered for Stage 5 (Lean L0 probe by a human)."""
    for idea in registry.list_ideas():
        if idea.final_verdict == "REGISTERED_FOR_STAGE_5":
            click.echo(f"{idea.id}\t{idea.target_interface!r}\t{idea.thesis[:80]!r}")


@cli.command()
@click.argument("idea_id")
def show(idea_id: str) -> None:
    """Pretty-print one idea's record."""
    idea = registry.load_idea(idea_id)
    click.echo(json.dumps(idea.to_dict(), indent=2))


if __name__ == "__main__":
    cli()
