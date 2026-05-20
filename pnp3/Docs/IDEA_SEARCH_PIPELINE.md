# Idea Search Pipeline

Updated: 2026-05-20.

This document is the **operating manual** for proof-attempt evaluation
in pnp3 / pnp4.  It defines a six-stage funnel from raw idea seed to
implementation, with explicit role separation, abort criteria, and
worker-prompt templates.

The pipeline exists because the project's history (15+ internal
audit stages, all kernel-checked, all closing the same family of
proof templates) has shown that **most proof attempts can be killed
cheaply before any Lean code is written**, provided that scrutiny
is applied in the right order.

## 1. Pipeline overview

```
                              1000 idea seeds
                                    │
                          Stage 1 — Literature Kill Audit
                                    │ (~80% killed)
                              200 survive
                                    │
                          Stage 2 — Barrier / NoGo Audit
                                    │ (~75% killed)
                              50 survive
                                    │
                          Stage 3 — Repo Surface Audit
                                    │ (~80% killed)
                              10 survive
                                    │
                          Stage 4 — Self-Attack Probe
                                    │ (~70% killed)
                              3 survive
                                    │
                          Stage 5 — Minimal Lean L0 Probe
                                    │ (~50% killed)
                              1–2 survive
                                    │
                          Stage 6 — Implementation
```

The numbers are **target rejection rates**, not contractual
guarantees.  The funnel is the discipline; the rates encode
priors learned from the audit chain so far.

**Key principle**: operator review time is the binding constraint,
not engineer compute.  The funnel exists to make operator review
tractable.

## 2. Role separation

The pipeline is decomposed into **five roles**.  An engineer is
assigned exactly one role per pass.  Mixing roles is forbidden —
each role is structured to filter out a specific failure mode,
and mixing dilutes that filtering.

### Role A — Idea Generator

**Output**: one `stage1_idea_card.md` per idea seed.

**Must**:
- State the idea as a one-paragraph thesis.
- List the prerequisite mathematical techniques.
- Sketch the expected mechanism (≤ 200 words).
- Identify which pnp3 / pnp4 interface the idea would plug into.

**Must NOT**:
- Write Lean code.
- Claim "almost a proof" or "obvious extension".
- Make final claims of any kind.
- Defend the idea against objections.

The Idea Generator is **neutral** — their job is generating, not
defending.

### Role B — Literature Killer

**Output**: one `stage1_literature_kill.md` (auditing one specific
idea card).

**Stance**: **prosecutor, not advocate**.  The Literature Killer's
job is to find published work that closes the idea.  An idea that
"survives" Stage 1 means the Literature Killer **failed** to find a
kill — which is a weaker claim than "the idea works".

**Must answer all eight questions** (see Stage 1 spec below).

**Must NOT**:
- Defend or advocate the idea.
- Mark LIT_UNKNOWN as green by default.
- Skip questions because they "feel" inapplicable.

### Role C — Repo Killer

**Output**: one `stage2_barrier_nogo.md` plus one `stage3_repo_surface.md`.

**Stance**: prosecutor.  The Repo Killer looks for:
- Existing NoGo entries that apply.
- Repository wrappers that hide the hard step inside a structure
  with `hardTheorem : <abstract source>` as a field.
- Already-refuted predicates the idea would re-introduce.

### Role D — Self-Attack Engineer

**Output**: one `stage4_self_attack.md`.

**Stance**: prosecutor with constructive obligation.  The Self-
Attack Engineer must **try to break the idea** by constructing
adversaries / counterexamples / collapses-to-refuted.

**Six-point checklist** (see Stage 4 spec).

**Must NOT** write Lean code — adversaries should be exhibited at
the mathematical level (pseudocode, constructions, parameter
regimes).  Lean comes in Stage 5.

### Role E — Lean Probe Engineer

**Output**: one minimal Lean test-local file + report
(`stage5_L0_probe.md`).

**Stance**: agnostic — implementer, not advocate.

**Must NOT**:
- Touch endpoints, specs, JSONL, NoGoLog, known_guards, trust-root.
- Introduce `axiom` / `opaque` / `sorry` / `admit` / `native_decide`.
- Claim `P ≠ NP` or any unconditional separation in the probe.

**File-size discipline**: ≤ 500 LOC test-local Lean.

### Role F — Operator

The human reviewer.  Receives each stage's report, makes the
**go/no-go decision**, and dispatches to the next role.  Cannot be
parallelised away.

## 3. Stage specs

### Stage 1 — Literature Kill Audit

**Input**: one `stage1_idea_card.md` from Role A.

**Output**: `stage1_literature_kill.md` from Role B.

**Eight questions** — Role B must answer each with citation or
explicit "not found after search":

1. **Is this relativizing?**  Would the proof technique work
   uniformly for arbitrary oracles?  Cite Baker-Gill-Solovay 1975
   if yes.
2. **Is this natural?**  Does the technique exhibit a combinatorial
   property of small circuits that is constructive in polynomial
   time on truth tables and covers a large fraction of functions?
   Cite Razborov-Rudich JCSS 1997 if yes.
3. **Is this algebrizing?**  Does the technique extend to algebraic
   oracles?  Cite Aaronson-Wigderson ACM TOCT 2009 if yes.
4. **Is this a known hardness-magnification dead end?**  Has any
   paper specifically said this style of magnification does not
   work?  Cite Chen et al. JACM 2022 (locality barrier), OPS19 CCC
   2019 (threshold gap), or other specific papers if yes.
5. **Is this equivalent to a known open lower bound?**  Would
   proving the idea imply an already-open conjecture?  If so the
   idea cannot be easier than the original conjecture.
6. **Is this already proved impossible?**  Direct refutation
   citation.
7. **Is this already known to be too weak?**  Does the idea, even
   if successful, fail to produce `NP ⊄ P/poly` because the bound
   is below the magnification threshold?
8. **Is there a paper that directly says "this type of route does
   not work"?**  Search aggressively for negative results.

**Verdict labels** (mandatory):

- **`LIT_GREEN`** — Role B searched and found no published kill.
  No barrier directly applies.  **This does not mean the idea
  works.**  It means literature does not kill it.
- **`LIT_YELLOW`** — One or more questions return partial /
  conditional / weak kills.  Idea survives but with explicit
  caveats; downstream stages should treat the partial kills as
  additional adversaries.
- **`LIT_RED`** — At least one question returns a hard kill.
  Idea closed at Stage 1.
- **`LIT_UNKNOWN`** — Role B could not search effectively (paywall,
  missing prerequisites, etc.).  **Crucially: this is NOT equal
  to green.**  Idea returns to Role B with additional resources,
  or is parked.

**Abort criterion**: `LIT_RED` or `LIT_UNKNOWN` → idea does not
proceed to Stage 2.

**Worker prompt template** (Role B):

```
You are a hostile literature reviewer for proof attempt <X>.

Your goal: kill the idea using published literature.  An idea
that survives your review means you FAILED to kill it.  Bias
towards rejection.

Read the idea card carefully.  Then answer each of the eight
questions with one of:
- "Killed by [paper], because [mechanism]."
- "Conditional kill: [paper], applies under [assumption]."
- "Not killed by [paper], because [reason]."
- "Not found after search."

For each question, run at least 2 targeted searches.  Include
URLs.  Do NOT mark a question as "not killed" without explicit
searches.

Final verdict: LIT_GREEN / LIT_YELLOW / LIT_RED / LIT_UNKNOWN.

LIT_UNKNOWN is NOT a default.  Use it only when search was
genuinely impossible (paywall, missing prerequisites).
```

### Stage 2 — Barrier / NoGo Audit

**Input**: idea card + Stage 1 report (LIT_GREEN or LIT_YELLOW).

**Output**: `stage2_barrier_nogo.md` from Role C.

The Stage 2 audit checks against the **internal kill-machine** —
the catalogue of NoGo entries, refuted predicates, and
already-closed routes in pnp3 / pnp4.  See
`pnp3/Docs/BARRIER_CATALOGUE.md` for the catalogue.

**Standard adversaries to compare against**:

```
NOGO-000004  prefixAnd hardwiring
NOGO-000006  arbitrary ttFormula payload
NOGO-000008  syntax-rewrite normalisation
NOGO-000009  normalisation meta-barrier
Probe 13     FormulaCertificateProviderPartial → False
L1 chain     isoStrong_conclusion_negative_general
Route closure not_AsymptoticIsoStrongRoute_canonical
Route closure not_AsymptoticPromiseYesCertificateRoute_canonical
Route closure not_AsymptoticPromiseYesWeakRouteEventually_canonical
```

**Pattern matchers** — kill if the idea resembles:

- **support-cardinality** based proof → matches refuted
  `FormulaSupportRestrictionBoundsPartial` family.
- **syntax filter** on formula shapes → matches
  ProvenanceFilterV2 / V2-C exclusion suite.
- **normalisation filter** → matches NOGO-000008/9.
- **universal `hWitness`** (universally quantified over arbitrary
  PpolyFormula or DAG witness) → matches Probe 13.
- **formula certificate provider** → matches Probe 13 refutation.
- **promise-YES / iso-strong forcing** → matches L1 chain
  refutation.

**Verdict**: `BARRIER_GREEN` / `BARRIER_YELLOW` / `BARRIER_RED`.

**Abort criterion**: `BARRIER_RED` → idea does not proceed to
Stage 3.

### Stage 3 — Repo Surface Audit

**Input**: idea card + Stages 1–2 reports.

**Output**: `stage3_repo_surface.md` from Role C.

The Stage 3 audit looks for the **wrapper smell**.

**Wrapper smell pattern A**:

```lean
structure X where
  hardTheorem : VerifiedNPDAGLowerBoundSource
```

A structure whose key field is the hard theorem itself.  This is
not progress — the hard theorem is just renamed.

**Wrapper smell pattern B**:

```lean
structure X where
  magnifiesToVerifiedDAGSource :
    weakLowerBound → VerifiedNPDAGLowerBoundSource
```

This **is** a legitimate interface pattern (e.g.,
`SearchMCSPMagnificationContract` in pnp4), but it is **not** a
proof — it postulates the magnification step as an assumption.
Such a structure is acceptable as an interface surface only if
the corresponding magnification theorem is independently proved
or cited as established (e.g., OPS19).

**Verdict**:

- `REPO_GREEN` — not a wrapper; the idea proposes a genuine
  technical step.
- `REPO_YELLOW` — partial wrapper; the idea reduces to a smaller
  hard step that is also unproved but more tractable.
- `REPO_RED` — pure wrapper; the idea just renames the hard
  theorem.

**Abort criterion**: `REPO_RED` → idea closed.

### Stage 4 — Self-Attack Probe

**Input**: idea card + Stages 1–3 reports.

**Output**: `stage4_self_attack.md` from Role D.

The Self-Attack Probe is the **adversarial step before formal
proof**.  Role D must try to break the idea using six standard
attack modes.

**Six-point checklist**:

1. **Construct a hardwiring witness**.  Can a small circuit
   (e.g., truth-table hardwiring at the canonical length) be
   exhibited that satisfies all the idea's hypotheses?  If yes,
   the idea cannot produce a lower bound at that parameter
   regime.
2. **Construct a trivial solver**.  Is the underlying problem
   already in P / NP / P/poly via a trivial reduction?  If yes,
   the idea is targeting a problem in the wrong complexity class.
3. **Find a per-slice non-uniform bypass**.  Does the idea require
   uniformity that the adversary can break with non-uniform
   advice?  If yes, the proof fails non-uniformly.
4. **Replace the witness with a syntactically equivalent rewrite**.
   Can a syntactic transformation reduce a "hard" witness to a
   "trivial" one without changing the semantics?  If yes, the
   idea's syntactic distinction is illusory.
5. **Check for collapse into an already-refuted route**.  Does the
   idea, under any natural specialisation, reduce to a route
   already in the refuted catalogue?  If yes, the idea is a
   re-discovery of an existing refutation.
6. **Check for hidden assumption of the main theorem**.  Does the
   idea require, as a hypothesis somewhere, the very statement it
   purports to prove (or an equivalent)?  If yes, the proof is
   circular.

**Verdict**:

- `SELF_GREEN` — none of the six attacks succeed.  The idea
  passes adversarial scrutiny.
- `SELF_YELLOW` — partial attacks succeed but with documented
  caveats; the idea proceeds with a tightened hypothesis set.
- `SELF_RED` — at least one attack succeeds completely.  Idea
  closed.

**Abort criterion**: `SELF_RED` → idea closed.

**Worker prompt template** (Role D):

```
You are a hostile adversary for proof attempt <X>.

Your goal: break the idea by constructing a counterexample, a
trivial solver, or a collapse into a refuted route.  Bias toward
finding the break.

Apply each of the six attack modes:
1. Hardwiring witness.
2. Trivial solver.
3. Non-uniform bypass.
4. Syntactic rewrite.
5. Collapse into refuted route.
6. Hidden assumption of main theorem.

For each attack, attempt construction in writing
(pseudocode / parameter regime / specific instance).
Do NOT write Lean.

Report format:
- Per-attack result: BROKEN with witness | UNCLEAR | NOT_APPLICABLE.
- Overall verdict: SELF_GREEN / SELF_YELLOW / SELF_RED.

If SELF_RED: provide the breaking witness explicitly.
```

### Stage 5 — Minimal Lean L0 Probe

**Input**: idea card + Stages 1–4 reports, all green or yellow.

**Output**: one Lean test-local file + `stage5_L0_probe.md` from
Role E.

**Hard discipline**:

```
≤ 500 LOC of new Lean
test-local under pnp3/Tests/ or pnp4/Pnp4/Tests/
no endpoint, no spec, no JSONL, no NoGoLog, no known_guards,
no trust-root edits
no `ResearchGapWitness`, no `SourceTheorem`, no `gap_from`,
no endpoint, no `P ≠ NP` claim
no `axiom` / `opaque` / `sorry` / `admit` / `native_decide`
```

**Goal of the L0 probe** — exactly one of:

- **Route-killer**: a small theorem that closes the idea by
  refuting one of its key claims (in the style of our
  `isoStrong_conclusion_negative_general` chain).
- **One bridge lemma**: a single theorem moving the idea forward
  by closing one specific dependency, without claiming the full
  conclusion.

**Verdict**:

- `L0_GREEN_BRIDGE` — bridge lemma landed; idea proceeds to
  Stage 6.
- `L0_RED_KILLED` — route-killer landed; idea closed.
- `L0_YELLOW_PARTIAL` — partial progress, needs another L0
  iteration.
- `L0_FAILED` — could not land any theorem under the discipline.
  Idea returned to Role D for further self-attack.

### Stage 6 — Implementation

**Input**: idea card + Stages 1–5 reports, all green / yellow /
green-bridge.

**Output**: a multi-session implementation chain analogous to the
L1 chain we executed (`isoStrong_no_go_L1 sessions 1–4` +
`general_isoStrong_route_closure`).

**Entry criteria** — ALL must hold:

- Stage 1 verdict ∈ {`LIT_GREEN`, `LIT_YELLOW`}.
- Stage 2 verdict ∈ {`BARRIER_GREEN`, `BARRIER_YELLOW`}.
- Stage 3 verdict ∈ {`REPO_GREEN`, `REPO_YELLOW`}.
- Stage 4 verdict ∈ {`SELF_GREEN`, `SELF_YELLOW`}.
- Stage 5 verdict ∈ {`L0_GREEN_BRIDGE`}.

**No idea reaches Stage 6 without passing all five prior gates**.
The funnel is the discipline; the gates are non-negotiable.

## 4. Funnel arithmetic

Target throughput per cycle:

```
1000 idea cards generated by Role A     (parallelisable)
  ↓ Stage 1: ~80% killed (LIT_RED) or parked (LIT_UNKNOWN)
200 survive
  ↓ Stage 2: ~75% killed (BARRIER_RED)
50 survive
  ↓ Stage 3: ~80% killed (REPO_RED) or marked YELLOW
10 survive
  ↓ Stage 4: ~70% killed (SELF_RED)
3 survive
  ↓ Stage 5: ~50% killed (L0_RED_KILLED or L0_FAILED)
1–2 survive to Stage 6 implementation
```

**Critical observation**: Stages 1–4 are **markdown-only**.
Stages 5–6 are Lean.  The bulk of the funnel (1000 → 3) runs
without any Lean code.  Lean engineering is reserved for the
last 0.3% of ideas.

**Operator review responsibility**:

- Stage 1: spot-check 5–10% of LIT_GREEN verdicts (operator may
  miss something Role B did not).
- Stage 2: spot-check 10–20% — internal NoGo is the project's
  proprietary kill-machine and operator knowledge of edge cases
  is highest leverage here.
- Stage 3: spot-check 20% — wrapper detection is subtle.
- Stage 4: review **all** SELF_GREEN verdicts — Self-Attack
  passing is the strongest signal so far.
- Stage 5: review **all** L0 outputs.
- Stage 6: full operator engagement.

## 5. Anti-patterns and red flags

### Anti-pattern A: "Adversarial role drift"

Role B / C / D drift into advocacy ("the idea seems plausible
because...").  This defeats the prosecutorial stance.  Detection:
the role's report uses positive framing.  Correction: re-prompt
with explicit prosecutorial mandate.

### Anti-pattern B: "LIT_UNKNOWN as green"

Role B reports LIT_UNKNOWN but operator treats it as LIT_GREEN
under time pressure.  Detection: any LIT_UNKNOWN passing to
Stage 2 without an explicit override note.  Correction: hard
abort on LIT_UNKNOWN; require explicit operator override or
return to Role B.

### Anti-pattern C: "Wrapper hidden as theorem"

A Stage 5 L0 probe claims a theorem but the theorem statement
inlines the hard step as a hypothesis (e.g., `theorem main (h :
ResearchGapWitness) : P_ne_NP`).  Detection: any L0 Lean theorem
that takes the abstract source as a hypothesis without
discharging it.  Correction: such theorems are wrappers, not
progress; rebound to Stage 3.

### Anti-pattern D: "Folklore rediscovery"

The L1 implementation chain converges on a counting / pigeonhole
argument that is publicly known folklore (e.g., our iso-strong
chain).  Detection: cross-reference Stage 1 search with the
specific argument being formalised.  Correction: kill the route
retroactively and update the barrier catalogue.

### Anti-pattern E: "Operator review skipped due to PR volume"

Too many parallel ideas → operator skips review → bad ideas leak
through.  Detection: PR throughput exceeds operator review
capacity.  Correction: throttle Stage 5 entries to ≤ 3 active
implementations at any time.

## 6. Connection to existing repository policy

This pipeline does **not** replace existing policies in:

- `pnp3/Docs/CLOSURE_ROUTE_POLICY.md` — closure-route framing.
- `RESEARCH_CONSTITUTION.md` — Rule 0 trust-root, Rule 16
  forbidden-keyword policy.
- `STATUS.md` — audit-chain summary.

It **extends** them with an explicit ideation-to-implementation
funnel that the audit chain has implicitly been running.  The
pipeline is also compatible with the existing seed-pack
convention.

## 7. Worked example: retroactive iso-strong via this pipeline

See `seed_packs/_worked_example_isoStrong_retroactive/` for a
backfill of the iso-strong audit chain through this six-stage
pipeline.  The backfill shows that **Stage 4 (Self-Attack) would
have killed the route in ~30 minutes of mathematical work**, vs
the ~3 weeks of formal-engineering work the project actually
spent.  The backfill is the strongest single case for the
discipline of this pipeline.

## 8. Next deployment

To deploy the pipeline:

1. Operator approves this document as repository policy.
2. Operator (or external researcher) generates the first batch of
   idea cards via Role A.
3. Role B / C / D agents are dispatched per Stages 1–4.
4. Operator reviews survivors and decides Stage 5 entry.
5. Iterate.

The pipeline is **idle-until-fed**.  Without external genuine
novelty, AI-generated idea cards in Role A will likely recombine
training-data folklore and be killed at Stages 1–3 in bulk.  The
pipeline's main value at this point is to **process external idea
contributions efficiently** and to **document the project's
existing kill-machine** for future readers.
