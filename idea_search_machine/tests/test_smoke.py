"""Smoke tests for the idea-search machine.

Run with::

    python3 -m unittest idea_search_machine.tests.test_smoke

These tests use the LLM mock mode and do not require an API key.
They verify pipeline plumbing end to end: idea generation, verdict
parsing, registry persistence, and stage halting semantics.
"""

from __future__ import annotations

import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

from idea_search_machine import registry
from idea_search_machine.llm import LLMClient
from idea_search_machine.stages import (
    stage0_generate,
    stage1_literature_kill,
    stage2_barrier_nogo,
    stage3_repo_surface,
    stage4_self_attack,
)


class IdeaSearchMachineSmokeTests(unittest.TestCase):

    def setUp(self) -> None:
        self._original_registry_dir = registry.REGISTRY_DIR
        self._original_index = registry.INDEX_FILE
        self._original_ideas = registry.IDEAS_DIR
        # Use a fresh temporary registry directory per test.
        self._tmp = Path(tempfile.mkdtemp(prefix="ism_test_"))
        registry.REGISTRY_DIR = self._tmp
        registry.INDEX_FILE = self._tmp / "index.jsonl"
        registry.IDEAS_DIR = self._tmp / "ideas"
        registry.IDEAS_DIR.mkdir(parents=True, exist_ok=True)

    def tearDown(self) -> None:
        registry.REGISTRY_DIR = self._original_registry_dir
        registry.INDEX_FILE = self._original_index
        registry.IDEAS_DIR = self._original_ideas
        shutil.rmtree(self._tmp, ignore_errors=True)

    def test_idea_generation_writes_record(self) -> None:
        llm = LLMClient(mock=True)
        idea = stage0_generate.run(llm)
        self.assertTrue(idea.id.startswith("idea-"))
        self.assertTrue(len(idea.thesis) > 0)
        # registry should have one idea now.
        self.assertEqual(len(registry.list_ideas()), 1)
        # idea.json should exist.
        idea_json = registry.IDEAS_DIR / idea.id / "idea.json"
        self.assertTrue(idea_json.exists())
        loaded = json.loads(idea_json.read_text())
        self.assertEqual(loaded["id"], idea.id)

    def test_full_pipeline_dispatches_each_stage(self) -> None:
        llm = LLMClient(mock=True)
        idea = stage0_generate.run(llm)
        # Run all four kill stages.  With the cycling mock, stages
        # 1-3 should run and stage 3 should halt due to REPO_RED.
        sr1 = stage1_literature_kill.run(llm, idea)
        self.assertIn(sr1.verdict, {"LIT_GREEN", "LIT_YELLOW", "LIT_RED", "LIT_UNKNOWN"})
        if sr1.verdict in {"LIT_RED", "LIT_UNKNOWN"}:
            return  # halted early — expected behaviour, not a bug
        sr2 = stage2_barrier_nogo.run(llm, idea)
        self.assertIn(sr2.verdict, {"BARRIER_GREEN", "BARRIER_YELLOW", "BARRIER_RED"})
        if sr2.verdict == "BARRIER_RED":
            return
        sr3 = stage3_repo_surface.run(llm, idea)
        self.assertIn(sr3.verdict, {"REPO_GREEN", "REPO_YELLOW", "REPO_RED"})
        if sr3.verdict == "REPO_RED":
            return
        sr4 = stage4_self_attack.run(llm, idea)
        self.assertIn(sr4.verdict, {"SELF_GREEN", "SELF_YELLOW", "SELF_RED"})

    def test_verdict_parser_handles_missing_terminator(self) -> None:
        """Parser must default to safe verdict when no VERDICT: line."""
        from idea_search_machine.stages import stage1_literature_kill as s1
        self.assertEqual(s1._parse_verdict(""), s1.DEFAULT_VERDICT)
        self.assertEqual(s1._parse_verdict("blah blah"), s1.DEFAULT_VERDICT)
        self.assertEqual(s1._parse_verdict("VERDICT: LIT_GREEN"), "LIT_GREEN")
        self.assertEqual(s1._parse_verdict("VERDICT: LIT_NONSENSE"), s1.DEFAULT_VERDICT)

    def test_red_verdict_halts_and_marks_closed(self) -> None:
        """When a stage returns RED, final_verdict must record the halt."""
        gen_llm = LLMClient(mock=True)
        idea = stage0_generate.run(gen_llm)
        # Fresh audit client mirrors CLI behavior (one LLMClient per
        # audit command).  Cycling mock then drives GREEN -> YELLOW -> RED.
        audit_llm = LLMClient(mock=True)
        stage1_literature_kill.run(audit_llm, idea)
        stage2_barrier_nogo.run(audit_llm, idea)
        stage3_repo_surface.run(audit_llm, idea)
        self.assertEqual(idea.final_verdict, "CLOSED_AT_STAGE_3")

    def test_status_summary_aggregates_counts(self) -> None:
        llm = LLMClient(mock=True)
        for _ in range(2):
            stage0_generate.run(llm)
        counts = registry.status_summary()
        self.assertEqual(counts.get("total"), 2)
        self.assertEqual(counts.get("stage0_generate:GENERATED"), 2)


if __name__ == "__main__":
    unittest.main()
