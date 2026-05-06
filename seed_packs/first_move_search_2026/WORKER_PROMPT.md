# Worker prompt — first_move_search_2026

> Send this entire file as the prompt body.  Workers self-pick
> `<YOUR-HANDLE>` and ONE seed question Q1-Q5.  Output is a
> single markdown report, NOT Lean code.

---

You are conducting a structured literature scan for non-obvious
"move-one" research ideas from areas adjacent to P-vs-NP.  Your
output is a single markdown report.  No Lean code.

## 0. Pick your question

Read `seed_packs/first_move_search_2026/README.md` §3.  Pick ONE
of:

* **Q1** — proof-complexity / bounded-arithmetic independence
  meta-theorems.
* **Q2** — fine-grained complexity barriers and their
  formalisability into FP-N.
* **Q3** — descriptive / model-theoretic characterisations of
  non-natural property classes.
* **Q4** — magnification follow-ups (post-Oliveira-Pich-Santhanam
  2019+).
* **Q5** — strengthenings of relativization / natural-proofs /
  algebrization triad since 2015.

If you propose a Q6 distinct from these, the operator must
approve before you start.

## 1. Required reading

1. `seed_packs/first_move_search_2026/README.md` (this seed pack's
   README) — output format, mandatory structure, classification
   protocol.
2. `outputs/nogolog.jsonl::NOGO-000001`, `NOGO-000004`,
   `NOGO-000005`, `NOGO-000006` — your report's mandatory §4
   self-attack uses these.
3. `pnp3/Barrier/Relativization.lean`,
   `pnp3/Barrier/NaturalProofs.lean`,
   `pnp3/Barrier/Algebrization.lean` — the existing classical
   barriers your report's §5 self-attack uses.  Read at least the
   docstrings to understand what each barrier states.

## 2. Output format

Single markdown file at:

```
seed_packs/first_move_search_2026/reports/<YOUR-HANDLE>/Q<N>_<topic-slug>.md
```

(`<topic-slug>` is a short hyphen-separated phrase describing your
chosen idea.)

The file MUST contain seven sections in order (six if not
`survivor`):

### §1. Question

Quote your chosen Q verbatim.  No paraphrasing.

### §2. Cited results

Bulleted list, each entry:

* Author(s), title, year, venue (NO fabricated DOIs).
* One-sentence summary.
* Verifiable identifier: arXiv ID, paper URL, or
  "JCSS volume X" — operator must be able to find the paper.
* If you're not 100% sure of a reference, mark it
  `[unverified]` rather than fabricating.

**Hallucinated references → automatic report rejection.**  When in
doubt, cite less but more accurately.

### §3. Concrete embedding sketch

How would the cited result import into THIS repo's framework?

* Which existing audit module(s) does it touch?
* What new `def` / `Prop` would it suggest in
  `pnp3/Magnification/AuditRoutes/`?
* Could it be formalised in months (not years)?
* What's the minimal first Lean theorem that would prove the
  embedding viable?

### §4. Self-attack against existing NoGos

Mandatory.  For each of NOGO-000001, NOGO-000004, NOGO-000005,
NOGO-000006:

* Does the proposed idea fall to this NoGo?
* Argue YES or NO in one paragraph each.

If you can't argue either way for a NoGo, mark `[uncertain]` and
explain what would resolve the uncertainty.

### §5. Self-attack against classical barriers

Mandatory.  For each of Relativization, Natural Proofs,
Algebrization:

* Does the proposed idea satisfy the barrier's hypothesis?
* If yes: argue consistency, or argue why the barrier doesn't
  apply.

### §6. Verdict

Pick ONE:

* `survivor` — passes self-attacks; potentially valuable
  follow-up.
* `interesting_but_blocked` — partial pass; archived for future.
* `obviously_dead` — fails self-attacks immediately; archived
  with reason.

Be honest.  Most ideas will be `obviously_dead` or
`interesting_but_blocked` after rigorous self-attack.  That's
expected and useful.

### §7. Follow-up seed pack outline (only if `survivor`)

* Proposed seed pack id.
* Goal (one paragraph).
* Suggested slot decomposition (3-6 slots).
* Inherited forbidden scope from this seed pack.

## 3. Forbidden

* Lean code.  This is documentation-only.
* Hallucinated references.
* Editing existing JSONL ledger entries.
* Touching the trust root.
* Promoting any idea to "accepted".
* Working under any `pnp3/` path.
* `pnp3/Candidates/` creation.
* `gap_from_*`, `SourceTheorem_*`, final endpoint claim.
* P ≠ NP unconditional claim.

## 4. Acceptance + classification

After you submit, the operator reviews.  A report is **accepted**
when:

1. All seven sections (six if not `survivor`) are present.
2. §2 references are verifiable (papers actually exist).
3. §4 and §5 self-attacks are sincere.
4. §6 verdict is one of the three permitted values.

If accepted, your report is classified per its §6 verdict:

* `survivor` → operator may draft a new seed pack PR (separate
  approval) using your §7 outline.
* `interesting_but_blocked` → moved to
  `seed_packs/first_move_search_2026/archived/`.
* `obviously_dead` → moved to
  `seed_packs/first_move_search_2026/archived/` with a one-line
  rejection reason in the file's frontmatter.

## 5. Begin

1. Pick `<YOUR-HANDLE>` and ONE question Q1-Q5.
2. Spend 1-3 days on literature search.
3. Verify cited references (arXiv lookup, Google Scholar, etc.).
4. Run §4 and §5 self-attacks honestly.
5. Reach verdict; if `survivor`, sketch §7.
6. Submit single markdown file.  Stop.

End of prompt.
