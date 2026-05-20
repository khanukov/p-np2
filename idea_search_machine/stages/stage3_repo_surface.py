"""Stage 3 — Repo Surface Audit (Role C)."""

from __future__ import annotations

import re
from pathlib import Path

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient, LLMResult
from idea_search_machine.tools.extract_routes import live_routes_excerpt


PROMPT_PATH = (
    Path(__file__).resolve().parent.parent / "prompts" / "role_c_repo_surface.md"
)
VALID_VERDICTS = {"REPO_GREEN", "REPO_YELLOW", "REPO_RED"}
DEFAULT_VERDICT = "REPO_YELLOW"  # paranoid default


def _build_prompt(idea: registry.Idea) -> str:
    body = (
        f"## Thesis\n\n{idea.thesis}\n\n"
        f"## Mechanism\n\n{idea.mechanism}\n\n"
        f"## Target interface\n\n{idea.target_interface}\n"
    )
    template = PROMPT_PATH.read_text()
    template = template.replace("{IDEA_BODY}", body)
    template = template.replace("{REPO_ROUTES_EXCERPT}", live_routes_excerpt())
    return template


def _parse_verdict(markdown: str) -> str:
    m = re.search(r"VERDICT:\s*(REPO_[A-Z]+)", markdown)
    if not m:
        return DEFAULT_VERDICT
    cand = m.group(1).strip()
    return cand if cand in VALID_VERDICTS else DEFAULT_VERDICT


def run(llm: LLMClient, idea: registry.Idea) -> registry.StageResult:
    prompt = _build_prompt(idea)
    result: LLMResult = llm.query(prompt, temperature=0.2, max_tokens=4000)
    verdict = _parse_verdict(result.text)
    report_filename = registry.save_stage_report(idea, "stage3_repo_surface", result.text)
    sr = registry.StageResult(
        stage="stage3_repo_surface",
        verdict=verdict,
        ran_at=registry.now_iso(),
        report_file=report_filename,
        model=result.model,
        is_mock=result.is_mock,
    )
    idea.stages["stage3_repo_surface"] = sr
    if verdict == "REPO_RED":
        idea.final_verdict = "CLOSED_AT_STAGE_3"
    registry.save_idea(idea)
    registry.write_verdict_summary(idea)
    return sr
