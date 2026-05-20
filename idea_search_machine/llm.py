"""LLM client abstraction.

Wraps the Anthropic Python SDK with a mock mode for development /
testing without an API key.  Mock responses are deterministic and
exercise every verdict path so the pipeline plumbing can be smoke-
tested end-to-end offline.
"""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass
from typing import Optional


@dataclass
class LLMResult:
    text: str
    model: str
    is_mock: bool


class LLMClient:
    """Thin wrapper over Anthropic SDK with mock mode.

    Parameters
    ----------
    model
        Anthropic model identifier (e.g. ``claude-sonnet-4-6``).
    mock
        If True, do not call the API; return canned deterministic
        responses keyed by prompt hash.
    api_key
        Override the ``ANTHROPIC_API_KEY`` env var.
    """

    def __init__(
        self,
        model: str = "claude-sonnet-4-6",
        mock: bool = False,
        api_key: Optional[str] = None,
    ) -> None:
        self.model = model
        self.mock = mock
        self._client = None
        self._call_count = 0
        if not mock:
            try:
                from anthropic import Anthropic
            except ImportError as exc:
                raise RuntimeError(
                    "anthropic package required for non-mock mode; "
                    "pip install -r idea_search_machine/requirements.txt"
                ) from exc
            self._client = Anthropic(api_key=api_key or os.environ.get("ANTHROPIC_API_KEY"))

    def query(
        self,
        prompt: str,
        system: Optional[str] = None,
        temperature: float = 0.3,
        max_tokens: int = 4000,
    ) -> LLMResult:
        if self.mock:
            self._call_count += 1
            return LLMResult(text=self._mock_response(prompt), model=self.model, is_mock=True)
        assert self._client is not None
        messages = [{"role": "user", "content": prompt}]
        kwargs = {
            "model": self.model,
            "max_tokens": max_tokens,
            "messages": messages,
        }
        # opus-4-7 and newer drop the temperature parameter; pass it
        # only for older models that still accept it.
        if not self.model.startswith("claude-opus-4-7"):
            kwargs["temperature"] = temperature
        if system:
            kwargs["system"] = system
        resp = self._client.messages.create(**kwargs)
        # The Anthropic SDK returns a Message with a list of content blocks.
        text_blocks = [b.text for b in resp.content if hasattr(b, "text")]
        text = "".join(text_blocks)
        return LLMResult(text=text, model=self.model, is_mock=False)

    # ------------------------------------------------------------------
    # Mock responses
    # ------------------------------------------------------------------

    def _mock_response(self, prompt: str) -> str:
        """Return a canned response keyed by prompt content.

        Exercises every verdict path across multiple invocations.  The
        invocation counter combined with the prompt hash cycles
        ideas through different mock outcomes deterministically.
        """
        # Cycle deterministically through GREEN/YELLOW/RED/UNKNOWN
        # via the call counter so the smoke test exercises every
        # pipeline path within a single run.
        salted = (self._call_count - 1) % 4
        verdict_bucket = ["GREEN", "YELLOW", "RED", "UNKNOWN"][salted]
        _ = hashlib.sha256(prompt.encode()).hexdigest()  # kept for stability
        if "Role A" in prompt or "Idea Generator" in prompt:
            return self._mock_idea_card(self._call_count)
        if "Role B" in prompt or "Literature Killer" in prompt or "literature kill" in prompt.lower():
            return self._mock_literature_kill(verdict_bucket)
        if "Role C" in prompt or "Repo Killer" in prompt:
            if "wrapper" in prompt.lower() or "repo surface" in prompt.lower():
                return self._mock_repo_surface(verdict_bucket)
            return self._mock_barrier_nogo(verdict_bucket)
        if "Role D" in prompt or "Self-Attack" in prompt:
            return self._mock_self_attack(verdict_bucket)
        return f"[mock fallback response for prompt with digest {digest[:8]}]"

    @staticmethod
    def _mock_idea_card(call_count: int = 0) -> str:
        # Three rotating mock idea variants so successive generations
        # produce distinguishable ideas under the mock LLM.
        variants = [
            (
                "random-projection shrinkage to bounded-fanin DAG",
                "Frobenius norm of the restriction operator",
                "FixedSliceDAGStableRestrictionSlackRoute",
            ),
            (
                "polynomial method over GF(2) on partial truth tables",
                "low-degree extension of size-1 candidate traces",
                "FixedSlicePromiseValueLocalityRoute",
            ),
            (
                "topological / homotopy-theoretic separation via the",
                "fundamental group of the YES-set complement",
                "ResearchGapWitness",
            ),
        ]
        variant = variants[call_count % len(variants)]
        return f"""# Idea Card

## 1. Thesis

(Mock idea #{call_count}) Apply {variant[0]}
families decoding canonical Gap-Partial-MCSP, treating each fixed
slice as a small composition of low-rank matrices and bounding the
spectral gap via the {variant[1]}.

## 2. Prerequisite techniques

- Random restriction / shrinkage of de Morgan formulae.
- Spectral norm bounds on Boolean operators.
- Standard `InPpolyDAG` interface in pnp3.

## 3. Expected mechanism

Show that any polynomial-size DAG family decoding the Gap-Partial-
MCSP language at canonical parameters must have a low-rank
restriction at every fixed slice, contradicting a counting
argument over Boolean operators of bounded spectral norm.

## 4. Target pnp3 / pnp4 interface

`{variant[2]}`.

## 5. Self-assessment of novelty

MEDIUM.  Restriction-shrinkage is folklore; the specific
spectral-norm angle on Boolean operators may be new in this
combination.

VERDICT: idea_card_generated
"""

    @staticmethod
    def _mock_literature_kill(bucket: str) -> str:
        return f"""# Literature Kill Audit (mock)

## Q1 — Relativizing?
Not killed by relativization (the technique uses structural
properties of canonical Gap-MCSP that do not relativize uniformly).

## Q2 — Natural?
Conditional kill: Razborov-Rudich JCSS 1997 may apply.  The
"low-rank restriction" property is constructive in poly time on
truth tables and the fraction of low-rank Boolean operators is a
classical natural property.

## Q3 — Algebrizing?
Not investigated in depth.

## Q4 — Known magnification dead end?
Possible match against Chen et al. JACM 2022 locality barrier
since the route routes through canonical Gap-Partial-MCSP.

## Q5 — Equivalent to a known open lower bound?
Restriction-shrinkage lower bounds on de Morgan formulae are
well-studied; the specific MCSP angle has been explored by
Cheraghchi-Kabanets-Lu-Myrisiotis ICALP 2019.

## Q6 — Already proved impossible?
Not directly.

## Q7 — Already known to be too weak?
The achievable shrinkage bound for de Morgan formulae is below the
magnification threshold per OPS19 CCC 2019.

## Q8 — Direct paper saying "this does not work"?
Not found after search.

## Final verdict

**LIT_{bucket}**

(mock response; in real usage Role B would produce a substantively
researched audit.)

VERDICT: LIT_{bucket}
"""

    @staticmethod
    def _mock_barrier_nogo(bucket: str) -> str:
        return f"""# Barrier / NoGo Audit (mock)

## NoGo catalogue checklist

| Tag | Match |
|---|---|
| NOGO-000004 (prefixAnd) | no |
| NOGO-000006 (ttFormula payload) | no |
| NOGO-000008 (syntax rewrite) | no |
| Probe 13 (FormulaCertificateProviderPartial) | no |
| isoStrong L1 chain | no |
| Support-bounds family | partial — restriction-shrinkage proximity |

## Pattern matchers

- Support-cardinality: no
- Syntax filter: no
- Universal hWitness: no
- Promise-YES / iso-strong forcing: no
- Pigeonhole on Gap-MCSP candidate trace counting: no

## Final verdict

**BARRIER_{bucket}**

(mock response.)

VERDICT: BARRIER_{bucket}
"""

    @staticmethod
    def _mock_repo_surface(bucket: str) -> str:
        return f"""# Repo Surface Audit (mock)

## Wrapper smell checks

### A. Inlines hard theorem as field?
No.  The idea proposes a specific structural restriction operator,
not a renaming of `ResearchGapWitness`.

### B. Postulates magnification as unverified interface?
No.

### C. Hidden assumption of P ≠ NP?
No.

### D. New abstract surface as plug-in target?
No.

## Final verdict

**REPO_{bucket}**

(mock response.)

VERDICT: REPO_{bucket}
"""

    @staticmethod
    def _mock_self_attack(bucket: str) -> str:
        return f"""# Self-Attack Probe (mock)

## Six-point attack checklist

### Attack 1 — Hardwiring witness
The standard truth-table hardwiring at canonical input length
satisfies the polynomial-size DAG hypothesis trivially.  Whether it
also satisfies the proposed "low-rank restriction" property
depends on the specific operator the route considers.

### Attack 2 — Trivial solver
Gap-Partial-MCSP at canonical parameters is in P/poly trivially
(known from L0 #1388).

### Attack 3 — Non-uniform bypass
Not investigated in depth in this mock.

### Attack 4 — Syntactic rewrite
Plausible: any "low-rank restriction" condition can be rewritten by
a syntactic transformation of the DAG, potentially producing a
violating instance.

### Attack 5 — Collapse into refuted route
Possible collapse into support-bounds family if the spectral norm
bound is structurally equivalent to support cardinality bound.

### Attack 6 — Hidden assumption of main theorem
Not investigated.

## Counting sanity check

For canonical Gap-Partial-MCSP at sYES=1, sNO=2:
- |YES set| ≈ n + 2 per slice (size-1 candidates)
- |Boolean labelings on free rows| = 2^(2^m - |D|)
- For sufficiently large m, the YES set is exponentially smaller.

Therefore any selective spectral property must be compatible with
this tight counting gap.

## Final verdict

**SELF_{bucket}**

(mock response.)

VERDICT: SELF_{bucket}
"""
