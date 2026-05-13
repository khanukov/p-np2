# Seed pack `first_move_search_2026`

> **Track:** Research-A — adjacent-area first-move scan.
> **Status:** OPEN — runs in parallel with `fp3b3` and `fp3b4`.
> **Method family:** N/A (cross-area research literature scan).
> **Output type:** structured markdown reports, NOT Lean code.
> **Priority:** parallel; low immediate cost, high variance returns.

## 0. TL;DR

Most P-vs-NP-adjacent progress comes from **cross-field insights**,
not within-field iteration.  Razborov-Rudich came from cryptography;
magnification (Oliveira-Pich-Santhanam) came from proof complexity.

This seed pack is a structured **literature scan** for
non-obvious "move-one" ideas from adjacent areas that could
impose new constraints on `ProvenanceFilter_v2` design or open a
new attack surface.

Output: structured markdown reports, **not Lean code**.  Top
survivors become **new audit seed packs** (e.g.,
`fp3b5_<idea>` or `proofcomplexity_independence_track`).

This is a high-variance investment.  ~5% chance of finding a
real new direction; ~95% chance of producing well-archived but
not actionable research.  Cost is low (LLM literature scan with
human verification), so the expected-value math is favorable.

## 1. Why this matters and why it's risky

### Why it matters

50 years of P-vs-NP research mean every "obvious" first-move idea
inside the field has been tried.  But adjacent areas (proof
complexity, fine-grained complexity, descriptive complexity, model
theory, derandomisation, communication complexity, algorithmic
foundations) keep producing ideas that DON'T look like P-vs-NP
attacks but turn out to constrain it.  Examples:

* **Razborov-Rudich (1994)** — natural proofs barrier.  Came from
  cryptography (PRG existence).
* **Oliveira-Pich-Santhanam (2019)** — magnification.  Came from
  proof complexity / circuit complexity bridge.
* **Williams (2014)** — IP = PSPACE-style algorithms force lower
  bounds for ACC.  Came from algorithmic technique.

Each of these reframed the search space.  This seed pack is a
**structured scan for the next such reframing**, scoped to
ideas relevant to FP-N pipeline shape.

### Why it's risky

* LLM literature reviews hallucinate references.
* "Adjacent areas" is vast — without sharp seed questions, output
  is noise.
* Survivors require human verification of cited results AND
  concrete embedding sketch in repo's framework.

The seed pack mitigates these via SHARP seed questions (§3),
mandatory citation verification (§4), and operator-gated
classification (§5).

## 2. What this seed pack does NOT do

* Does NOT produce Lean code.  Output is markdown reports.
* Does NOT promote any idea.  Top survivors become NEW seed
  packs in subsequent operator-approved PRs.
* Does NOT touch the trust root, FP-4, SourceTheorem, gap_from,
  final endpoints, or any guard promotion.
* Does NOT activate Wave 1.

## 3. Sharp seed questions (pick ONE per report)

Each worker picks ONE of these as their report's research
question.  Do NOT generalise to "find anything interesting."  The
sharp question gates the output.

### Q1 — proof-complexity independence

> What proof-complexity / bounded-arithmetic meta-theorems after
> 2010 imply that some classes of formula provenance filters
> cannot be proven valid in subsystems of PA / EF?

Targets: independence-of-arithmetic results restricted to
provenance-filter-class predicates.  Possible value: a fourth
formal barrier in `pnp3/Barrier/` based on proof-system
independence rather than natural properties.

### Q2 — fine-grained complexity barriers

> What fine-grained complexity barriers (SETH, OV, NPSearch,
> 3SUM-hardness, etc.) imply that conditional lower bounds for
> formula classes become unconditional under specific
> reductions?  Are any such reductions formalisable into the
> FP-N pipeline?

Targets: SETH-style / Williams-method work on circuit lower
bounds.  Possible value: a v2-direction informed by
fine-grained-complexity reductions.

### Q3 — descriptive / model-theoretic characterisations

> What descriptive complexity or model-theoretic results
> characterise "natural" filter properties in the Razborov-Rudich
> sense, AND what alternative "non-natural" property classes are
> known to exist?

Targets: Immerman-Vardi / Fagin-style results, plus recent
non-natural-property constructions (e.g., learning-based, or
algorithmic-information based).  Possible value: a v2-direction
that sidesteps the natural-proofs barrier explicitly.

### Q4 — magnification follow-ups

> What magnification results (post-Oliveira-Pich-Santhanam, 2019+)
> extend the AC0 → P/poly bridge to weaker initial circuit
> assumptions?  Are any such extensions compatible with the
> FP-N pipeline's `InPpolyFormula` shape?

Targets: recent magnification literature, including
Chen-Jin-Williams-style or Chen-Hirahara-style results.  Possible
value: opens FP-4 with weaker FP-3 prerequisites.

### Q5 — barrier strengthenings

> What strengthenings of the relativization / natural-proofs /
> algebrization triad have been published since 2015?  Are any
> formalisable as a fourth barrier theorem in
> `pnp3/Barrier/<NewBarrier>.lean`?

Targets: Aaronson-class meta-results, IP-style barriers,
arithmetisation-based barriers.  Possible value: a fourth
classical barrier formalisation, expanding `pnp3/Barrier/`
beyond the current three.

Worker may propose a Q6 if they identify a sharp question
adjacent to but distinct from Q1-Q5.  Q6 must be operator-approved
before worker starts.

## 4. Per-report mandatory structure

Each report lives at:

```
seed_packs/first_move_search_2026/reports/<HANDLE>/Q<N>_<topic-slug>.md
```

It MUST contain these seven sections, in order:

### §1. Question

Quote one of Q1-Q5 verbatim (or the operator-approved Q6).  No
paraphrasing — the search is gated by exact question matching.

### §2. Cited results

A bulleted list of references, each with:

* Author(s), title, year, venue (no fabricated DOIs; if uncertain,
  mark `[unverified]`).
* One-sentence summary of the result.
* Pointer to where the result lives (paper URL if open-access,
  arXiv ID, or "JCSS volume X" — verifiable identifiers).

The reference list is REVIEWABLE: if the operator can't find the
cited paper, the report is rejected.  No hallucinated references
will pass.

### §3. Concrete embedding sketch

How would the cited result import into THIS repo's framework?
Specifically:

* Which existing audit module(s) does it touch?
* What new `def`/`Prop` would it suggest in
  `pnp3/Magnification/AuditRoutes/`?
* Could it be formalised with reasonable effort (months, not
  years)?

### §4. Self-attack against existing NoGos

Mandatory.  For each of `NOGO-000001`, `NOGO-000004`, `NOGO-000005`,
`NOGO-000006`:

* Does the proposed idea fall to this NoGo?
* If yes: WHY (one paragraph).  If no: WHY (one paragraph).

If the idea falls to ALL four NoGos without giving structural
reason, the report classifies as `obviously_dead`.

### §5. Self-attack against classical barriers

Mandatory.  For each of `pnp3/Barrier/Relativization.lean`,
`pnp3/Barrier/NaturalProofs.lean`,
`pnp3/Barrier/Algebrization.lean`:

* Does the proposed idea satisfy the barrier's hypothesis?
* If yes: explain why the idea is consistent with the barrier OR
  why the barrier doesn't apply.

### §6. Verdict

ONE of:

* `survivor` — passes both self-attacks; potentially valuable.
  Recommends a follow-up seed pack.
* `interesting_but_blocked` — passes one self-attack but blocked
  by another.  Archive for future revisit.
* `obviously_dead` — fails one or more self-attacks immediately.
  Archive with one-line reason.

### §7. Follow-up seed pack outline (only if `survivor`)

If §6 verdict is `survivor`, sketch:

* Proposed seed pack id (e.g., `fp3b5_<short-name>`).
* Goal of the new seed pack (one paragraph).
* Suggested slot decomposition (3-6 slots).
* Forbidden scope inheritance from this seed pack's §5.

## 5. Output flow + classification

```text
Worker → reports/<HANDLE>/Q<N>_<topic>.md
            ↓
        Operator review (citation verification + self-attack soundness)
            ↓
   ┌────────┴────────┐
   ↓                 ↓
survivor       interesting_but_blocked / obviously_dead
   ↓                 ↓
PR proposes    archived/<HANDLE>_<topic>.md
new seed pack   (one-line reason header preserved)
(separate PR)
```

Survivors do NOT auto-promote.  Each survivor → operator drafts a
follow-up seed pack PR; that PR is reviewed independently for
viability before any Lean engineer is dispatched.

## 6. Allowed / forbidden scope

### Allowed (per worker)

* New markdown files under
  `seed_packs/first_move_search_2026/reports/<HANDLE>/`.
* Operator may move reports from `reports/` to `archived/` after
  classification.

### Forbidden (HARD)

* Lean code.  This is a literature scan, not a proof-development
  seed pack.
* Editing existing JSONL ledger entries.
* Editing the trust root.
* Hallucinated references (any unverifiable citation in §2 →
  report rejected).
* Promoting any idea to "accepted" via this seed pack.
* Working under any `pnp3/` path.  This seed pack is
  documentation-only.
* `pnp3/Candidates/` creation.
* `gap_from_*`, `SourceTheorem_*`, final endpoint.
* `P_ne_NP_unconditional` claim.
* Wave 1 activation by force.

## 7. Per-report acceptance criteria

A report is **accepted** (regardless of verdict) when:

1. All seven sections (§1-§7 if survivor; §1-§6 if not) are
   present and non-empty.
2. §2 cites references that operator can verify (papers actually
   exist; arXiv IDs / DOIs resolve).
3. §4 and §5 self-attack sections are sincere — not
   "no obvious break" without argument.
4. §6 verdict is one of the three permitted values.
5. Markdown is well-formed.

A report is **rejected** when:

1. Any cited reference is hallucinated.
2. Self-attack sections are vacuous.
3. The report describes Lean code or otherwise violates §6
   forbidden scope.

Rejected reports go to `archived/<HANDLE>_rejected_<topic>.md`
with operator-supplied rejection reason.

## 8. Cross-references

* Existing barriers: `pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`.
* Existing NoGo entries: `outputs/nogolog.jsonl` (NOGO-000001
  through NOGO-000006 at minimum).
* Sibling seed packs: `fp3b3_provenance_filter_v2_design/`,
  `fp3b4_support_cardinality_barrier/`.
* `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.
* `seed_packs/PILOT_WAVE_0_PROTOCOL.md` — worker cycle (this seed
  pack uses a documentation-only variant — no `outputs/attempts.jsonl`
  append per report; only on operator-approved survivor → seed-pack
  promotion).

## 9. Closing note

> "First-move" thinking is high-variance.  Five reports answering
> sharp questions are worth more than fifty reports answering
> "find something interesting."  This seed pack is the structured
> way to scan adjacent areas without producing noise.

Pilot Wave 1 cap is 20 workers; this seed pack's 3-5 reporters
fit comfortably alongside `fp3b4` (6 slots) and `fp3b3` (4
directions × 2 phases).  Expected output cadence: 2-3 reports per
week if dispatched to LLM sessions, 1 report per week if dispatched
to human researchers.  Operator review of each report: 30-90
minutes.

After 4-8 weeks, expected results: 0-2 survivors, 5-15 archived
reports.  Survivors ARE the breakthroughs we're searching for; if
zero, the negative result ("adjacent areas examined under sharp
questions don't yield obvious new directions") is itself a
research-state artifact.
