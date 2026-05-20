"""Stage 4 — Self-Attack Probe (Role D)."""

from __future__ import annotations

import re
from pathlib import Path

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient, LLMResult


PROMPT_PATH = (
    Path(__file__).resolve().parent.parent / "prompts" / "role_d_self_attack.md"
)
VALID_VERDICTS = {"SELF_GREEN", "SELF_YELLOW", "SELF_RED"}
DEFAULT_VERDICT = "SELF_YELLOW"  # paranoid default


def _build_prompt(idea: registry.Idea) -> str:
    body = (
        f"## Thesis\n\n{idea.thesis}\n\n"
        f"## Prerequisites\n\n" + "\n".join(f"- {p}" for p in idea.prerequisites) + "\n\n"
        f"## Mechanism\n\n{idea.mechanism}\n\n"
        f"## Target interface\n\n{idea.target_interface}\n"
    )
    return PROMPT_PATH.read_text().replace("{IDEA_BODY}", body)


def _parse_verdict(markdown: str) -> str:
    m = re.search(r"VERDICT:\s*(SELF_[A-Z]+)", markdown)
    if not m:
        return DEFAULT_VERDICT
    cand = m.group(1).strip()
    return cand if cand in VALID_VERDICTS else DEFAULT_VERDICT


def run(llm: LLMClient, idea: registry.Idea) -> registry.StageResult:
    prompt = _build_prompt(idea)
    result: LLMResult = llm.query(prompt, temperature=0.2, max_tokens=8000)
    verdict = _parse_verdict(result.text)
    report_filename = registry.save_stage_report(idea, "stage4_self_attack", result.text)
    sr = registry.StageResult(
        stage="stage4_self_attack",
        verdict=verdict,
        ran_at=registry.now_iso(),
        report_file=report_filename,
        model=result.model,
        is_mock=result.is_mock,
    )
    idea.stages["stage4_self_attack"] = sr
    if verdict == "SELF_RED":
        idea.final_verdict = "CLOSED_AT_STAGE_4"
    elif _all_prior_passed(idea) and verdict in {"SELF_GREEN", "SELF_YELLOW"}:
        # Survived all four kill audits.  Mark for human Stage 5.
        idea.final_verdict = "REGISTERED_FOR_STAGE_5"
    registry.save_idea(idea)
    registry.write_verdict_summary(idea)
    return sr


def _all_prior_passed(idea: registry.Idea) -> bool:
    needed = [
        ("stage1_literature_kill", {"LIT_GREEN", "LIT_YELLOW"}),
        ("stage2_barrier_nogo", {"BARRIER_GREEN", "BARRIER_YELLOW"}),
        ("stage3_repo_surface", {"REPO_GREEN", "REPO_YELLOW"}),
    ]
    for name, allowed in needed:
        sr = idea.stages.get(name)
        if sr is None or sr.verdict not in allowed:
            return False
    return True
