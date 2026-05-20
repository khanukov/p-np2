"""Stage 0 — Idea Card generation (Role A).

Dispatches the LLM in neutral-generator mode and parses the output
into an :class:`Idea` record.
"""

from __future__ import annotations

import re
from pathlib import Path

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient, LLMResult


PROMPT_PATH = Path(__file__).resolve().parent.parent / "prompts" / "role_a_idea_card.md"


def _load_prompt() -> str:
    return PROMPT_PATH.read_text()


def _parse_section(markdown: str, heading: str) -> str:
    """Return the body of `## <heading>` up to the next `## ` line."""
    pattern = rf"##\s*{re.escape(heading)}\s*\n(.*?)(?=\n##\s|\nVERDICT:|\Z)"
    m = re.search(pattern, markdown, re.DOTALL | re.IGNORECASE)
    return (m.group(1).strip() if m else "").strip()


def _parse_idea_card(markdown: str) -> dict:
    """Pull thesis / prerequisites / mechanism / target / novelty out."""
    return {
        "thesis": _parse_section(markdown, "1. Thesis"),
        "prerequisites_block": _parse_section(markdown, "2. Prerequisite techniques"),
        "mechanism": _parse_section(markdown, "3. Expected mechanism"),
        "target_interface": _parse_section(markdown, "4. Target pnp3 / pnp4 interface")
        or _parse_section(markdown, "4. Target pnp3 \\/ pnp4 interface"),
        "novelty": _parse_section(markdown, "5. Self-assessment of novelty"),
    }


def _parse_prerequisites(block: str) -> list[str]:
    return [line.lstrip("-* \t") for line in block.splitlines() if line.strip().startswith(("-", "*"))]


def run(llm: LLMClient, *, system_extra: str = "") -> registry.Idea:
    """Generate one idea card and persist it to the registry."""
    prompt = _load_prompt()
    result: LLMResult = llm.query(prompt, temperature=0.7, max_tokens=2000)
    parsed = _parse_idea_card(result.text)
    idea = registry.Idea(
        id=registry.new_idea_id(),
        created_at=registry.now_iso(),
        thesis=parsed["thesis"] or "(empty thesis)",
        prerequisites=_parse_prerequisites(parsed["prerequisites_block"]),
        mechanism=parsed["mechanism"],
        target_interface=parsed["target_interface"],
        novelty_self_assessment=parsed["novelty"],
        final_verdict="OPEN",
    )
    # Save metadata then the idea-card markdown report.
    registry.save_idea(idea)
    report_filename = registry.save_stage_report(idea, "stage1_idea_card", result.text)
    idea.stages["stage0_generate"] = registry.StageResult(
        stage="stage0_generate",
        verdict="GENERATED",
        ran_at=registry.now_iso(),
        report_file=report_filename,
        model=result.model,
        is_mock=result.is_mock,
    )
    registry.save_idea(idea)
    registry.write_verdict_summary(idea)
    return idea
