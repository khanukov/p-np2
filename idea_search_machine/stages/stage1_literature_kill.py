"""Stage 1 — Literature Kill Audit (Role B)."""

from __future__ import annotations

import re
from pathlib import Path

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient, LLMResult


PROMPT_PATH = (
    Path(__file__).resolve().parent.parent / "prompts" / "role_b_literature_kill.md"
)
VALID_VERDICTS = {"LIT_GREEN", "LIT_YELLOW", "LIT_RED", "LIT_UNKNOWN"}
DEFAULT_VERDICT = "LIT_UNKNOWN"  # paranoid default — never green by default


def _build_prompt(idea: registry.Idea) -> str:
    body = (
        f"## Thesis\n\n{idea.thesis}\n\n"
        f"## Prerequisites\n\n" + "\n".join(f"- {p}" for p in idea.prerequisites) + "\n\n"
        f"## Mechanism\n\n{idea.mechanism}\n\n"
        f"## Target interface\n\n{idea.target_interface}\n"
    )
    return PROMPT_PATH.read_text().replace("{IDEA_BODY}", body)


def _parse_verdict(markdown: str) -> str:
    """Extract the structured `VERDICT: LIT_<LABEL>` line.

    Treats anything other than a valid label (including missing line)
    as :data:`DEFAULT_VERDICT` to prevent silent green leaks.
    """
    m = re.search(r"VERDICT:\s*(LIT_[A-Z_]+)", markdown)
    if not m:
        return DEFAULT_VERDICT
    candidate = m.group(1).strip()
    return candidate if candidate in VALID_VERDICTS else DEFAULT_VERDICT


def run(llm: LLMClient, idea: registry.Idea) -> registry.StageResult:
    """Run Stage 1 and persist the report; return the StageResult."""
    prompt = _build_prompt(idea)
    result: LLMResult = llm.query(prompt, temperature=0.2, max_tokens=4000)
    verdict = _parse_verdict(result.text)
    report_filename = registry.save_stage_report(
        idea, "stage1_literature_kill", result.text
    )
    sr = registry.StageResult(
        stage="stage1_literature_kill",
        verdict=verdict,
        ran_at=registry.now_iso(),
        report_file=report_filename,
        model=result.model,
        is_mock=result.is_mock,
    )
    idea.stages["stage1_literature_kill"] = sr
    if verdict == "LIT_RED":
        idea.final_verdict = "CLOSED_AT_STAGE_1"
    elif verdict == "LIT_UNKNOWN":
        idea.final_verdict = "PARKED_AT_STAGE_1"
    registry.save_idea(idea)
    registry.write_verdict_summary(idea)
    return sr
