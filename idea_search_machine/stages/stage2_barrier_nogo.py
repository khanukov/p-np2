"""Stage 2 — Barrier / NoGo Audit (Role C)."""

from __future__ import annotations

import re
from pathlib import Path

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient, LLMResult


PROMPT_PATH = (
    Path(__file__).resolve().parent.parent / "prompts" / "role_c_barrier_audit.md"
)
BARRIER_DOC_PATH = (
    Path(__file__).resolve().parent.parent.parent / "pnp3" / "Docs" / "BARRIER_CATALOGUE.md"
)
VALID_VERDICTS = {"BARRIER_GREEN", "BARRIER_YELLOW", "BARRIER_RED"}
DEFAULT_VERDICT = "BARRIER_YELLOW"  # paranoid default


def _barrier_excerpt(max_chars: int = 6000) -> str:
    """Load a head excerpt of the barrier catalogue for the prompt."""
    if not BARRIER_DOC_PATH.exists():
        return "(BARRIER_CATALOGUE.md not found; using empty excerpt.)"
    txt = BARRIER_DOC_PATH.read_text()
    if len(txt) > max_chars:
        return txt[:max_chars] + "\n\n(... excerpt truncated; see BARRIER_CATALOGUE.md ...)"
    return txt


def _build_prompt(idea: registry.Idea) -> str:
    body = (
        f"## Thesis\n\n{idea.thesis}\n\n"
        f"## Mechanism\n\n{idea.mechanism}\n\n"
        f"## Target interface\n\n{idea.target_interface}\n"
    )
    template = PROMPT_PATH.read_text()
    template = template.replace("{IDEA_BODY}", body)
    template = template.replace("{BARRIER_CATALOGUE_EXCERPT}", _barrier_excerpt())
    return template


def _parse_verdict(markdown: str) -> str:
    m = re.search(r"VERDICT:\s*(BARRIER_[A-Z]+)", markdown)
    if not m:
        return DEFAULT_VERDICT
    cand = m.group(1).strip()
    return cand if cand in VALID_VERDICTS else DEFAULT_VERDICT


def run(llm: LLMClient, idea: registry.Idea) -> registry.StageResult:
    prompt = _build_prompt(idea)
    result: LLMResult = llm.query(prompt, temperature=0.2, max_tokens=4000)
    verdict = _parse_verdict(result.text)
    report_filename = registry.save_stage_report(idea, "stage2_barrier_nogo", result.text)
    sr = registry.StageResult(
        stage="stage2_barrier_nogo",
        verdict=verdict,
        ran_at=registry.now_iso(),
        report_file=report_filename,
        model=result.model,
        is_mock=result.is_mock,
    )
    idea.stages["stage2_barrier_nogo"] = sr
    if verdict == "BARRIER_RED":
        idea.final_verdict = "CLOSED_AT_STAGE_2"
    registry.save_idea(idea)
    registry.write_verdict_summary(idea)
    return sr
