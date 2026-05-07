# Phase 2 prompt — fp3b3 V2-`<DIRECTION>` Lean self-attack

> **TEMPLATE — DO NOT DISPATCH AS-IS.**  This file is a skeleton
> for `<DIRECTION>` reviewers to fill in.  Replace every
> `<placeholder>` with concrete values from your review.  After
> filling, save as
> `seed_packs/fp3b3_provenance_filter_v2_design/phase2_prompts/<DIRECTION>_phase2.md`
> and remove this banner.
>
> Preserve `<HANDLE>` as a placeholder so the actual Phase 2
> engineer can pick their own.

---

You are formalising the Phase 2 self-attack of one direction of
`ProvenanceFilter_v2`.  Phase 1 (paper sketch) has been
operator-reviewed and approved per
`seed_packs/fp3b3_provenance_filter_v2_design/reviews/<DIRECTION>_review_<reviewer-handle>.md`.

Your task: produce kernel-checked Lean theorems formalising the
five Phase 2 obligations from the seed pack contract.

Pick `<YOUR-HANDLE>` (your initials, model name, etc.).

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN.

## 1. Required reading (in order)

1. The Phase 1 sketch:
   `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<DIRECTION>/Sketch.lean`.
2. The reviewer's report:
   `seed_packs/fp3b3_provenance_filter_v2_design/reviews/<DIRECTION>_review_<reviewer-handle>.md`.
   **Read the Risks section carefully** — the reviewer flagged
   specific failure modes; your job includes avoiding them.
3. `seed_packs/fp3b3_provenance_filter_v2_design/README.md` and
   `WORKER_PROMPT.md` — the contract.
4. The four obstructions:
   * `outputs/nogolog.jsonl::NOGO-000001` (overbroad uniform
     provenance — `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`
     line 155+),
   * `outputs/nogolog.jsonl::NOGO-000004` and the family at
     `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2`,
   * `outputs/nogolog.jsonl::NOGO-000005` (scope correction),
   * `outputs/nogolog.jsonl::NOGO-000006` and the family at
     `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean::adversaryFamily_v_arbpayload`
     plus witness in `Witness.lean`.
5. The new fp3b4 meta-barrier (you are explicitly NOT
   support-cardinality-only — your review confirmed this):
   * `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/SupportCardinalityOnly.lean`
     (`IsSupportCardinalityOnly` predicate),
   * `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`
     (the meta-barrier theorem your filter dodges).
6. Filter under attack:
   `FP3Attempt.InSupportFunctionalDiversity`.

## 2. Concrete file layout

Create files under
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<DIRECTION>/`:

| File | Goal | Theorem name |
| ---- | ---- | ------------ |
| `Filter.lean` | Re-export / Lean-formalise the candidate filter (mostly imports + one `def` re-name from the sketch if needed) | `<filter-name>` (matches sketch) |
| `NotSupportCardinalityOnly.lean` | Prove the filter dodges fp3b4's barrier | `<filter-name>_not_support_cardinality_only` |
| `ExcludesOverbroad.lean` | Prove the filter rejects NOGO-000001 shape | `excludes_overbroad_<DIR>` |
| `ExcludesPrefixAnd.lean` | Prove the filter rejects NOGO-000004's family | `excludes_prefixAnd_<DIR>` |
| `ExcludesArbitraryPayload.lean` | Prove the filter rejects NOGO-000006's family | `excludes_arbitrary_payload_<DIR>` |
| `NonVacuity.lean` | Prove the filter ADMITS a specific honest family | `<DIR>_admits_<HONEST-FAMILY>` |
| `Survivor.lean` | Compose the four exclusions + non-vacuity | `<filter-name>_survives_known_obstructions` |

`<DIR>` is the short direction tag (`V2_A`, `V2_C`).
`<HONEST-FAMILY>` is the named honest family
(`<honest-family-name>`) approved by the reviewer.

## 3. Mandatory theorems (concrete signatures)

Replace the placeholder names below with the exact Lean
identifiers from your sketch and reviewer report.

### Filter dodges fp3b4's barrier

```lean
theorem <filter-name>_not_support_cardinality_only :
    ¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
        @<filter-name>
```

This is the Phase 2 first-priority theorem.  Without it, fp3b4's
`support_cardinality_barrier` immediately kills your candidate.
The reviewer's §2 already argued the filter inspects information
beyond support cardinality; your job is to make that argument
kernel-checked.  Concrete strategy: exhibit two
`InPpolyFormula L` witnesses with the same support-cardinality
profile but on which the filter disagrees.

### Excludes NOGO-000001

```lean
theorem excludes_overbroad_<DIR>
    (ac0 : <…>) (sb : <…>)
    (hOverbroad : <OverbroadUniformProvenance shape>) :
    ¬ <filter-name> (<the witness implied by the overbroad shape>)
```

Concrete strategy: <reviewer-supplied sketch>.

### Excludes NOGO-000004

```lean
theorem excludes_prefixAnd_<DIR> :
    ¬ <filter-name>
        Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
          .adversaryWitness_v_natlog2
```

Concrete strategy: <reviewer-supplied sketch>.  This is the most
important exclusion: the prefix-AND family is the canonical
hardwiring shape.

### Excludes NOGO-000006

```lean
theorem excludes_arbitrary_payload_<DIR>
    (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
    (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F) :
    ¬ <filter-name>
        (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
          .adversaryWitness_v_arbpayload F hF)
```

Concrete strategy: <reviewer-supplied sketch>.

### Non-vacuity

```lean
def <honest-family-name> : <type — typically PayloadFamily-like>
def <honest-family-name>_witness : InPpolyFormula <honest-family-name>_language
theorem <DIR>_admits_<honest-family-name> :
    <filter-name> <honest-family-name>_witness
```

Concrete honest family: `<honest-family-name>` (reviewer's pick).
For `parity`: family is `fun n => XOR-formula computing parity of
n inputs`, which has full support `Finset.univ`, linear size, and
admits the filter's structural conditions.

### Survivor integration

```lean
theorem <filter-name>_survives_known_obstructions :
    -- conjunction of all five above, packaged for human-Critic review
```

## 4. Allowed scope

* New files under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<DIRECTION>/`
  per §2 layout.
* `lakefile.lean` — append new modules.
* `pnp3/Tests/AuditRoutes_ProvenanceFilterV2_<DIRECTION>_<YOUR-HANDLE>_Smoke.lean`
  (optional regression smoke).
* `outputs/attempts.jsonl` — append ONE entry on Phase 2
  completion.
* `seed_packs/fp3b3_provenance_filter_v2_design/critic_reports/<DIRECTION>_<YOUR-HANDLE>.md`
  — six-attack Critic report per `spec/critic_protocol.md`.

## 5. Forbidden

* Editing the Phase 1 sketch (it stays as historical record).
* Editing the reviewer's review document.
* Editing other directions' files.
* Editing existing JSONL ledger entries (Rule 9).
* Editing trust root, FP3b1/fp3b2/fp3b4 theorem bodies, the FP-3
  candidate filter, CL-0 predicates.
* `axiom`, `opaque`, `Fact`, typeclass-payload (Rule 16).
* `sorry`/`admit` (Rule 1).
* `pnp3/Candidates/`, `gap_from_*`, `SourceTheorem_*`, final
  endpoint, `ProvenanceFilter_v1` promotion.
* Promoting your v2 to "accepted" — survivor candidates ship
  here as audit artifacts; promotion is a separate post-Phase-2
  PR.
* Wave 1 activation by force.

## 6. Direction-specific traps (from reviewer)

<reviewer fills in §6 risks here, copy-pasted from review's §6>.

## 7. Output (exactly ONE of two)

### Outcome A — survivor candidate landed

Submit a unified diff or branch named
`worker/fp3b3/<DIRECTION>_phase2_<YOUR-HANDLE>` with all §2 files
plus lakefile wiring, optional smoke, ledger append, and Critic
report.

**Acceptance checklist:**

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `scripts/check.sh` 17/17 + 12.b/c/d/e/f/g/h/j/k green.
- [ ] `rg "\bsorry\b|\badmit\b" -g"*.lean"
       pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<DIRECTION>/`
      returns nothing.
- [ ] All seven theorems from §3 compile.
- [ ] `validate_jsonl.py` OK on both ledgers.
- [ ] Critic report classified `pass` per
      `spec/critic_protocol.md` §1–3.

### Outcome B — structured failure report

If Phase 2 reveals the candidate is structurally hopeless, ship a
markdown failure report at:

```
seed_packs/fp3b3_provenance_filter_v2_design/failures/<DIRECTION>_phase2_<YOUR-HANDLE>.md
```

Sections: what was attempted, where it broke (Lean errors
verbatim), local vs global obstruction, what the integrator must
know.  A `global` obstruction informs the operator that
`<DIRECTION>` is dead and saturates one of four directions.

## 8. Begin

1. Pick `<YOUR-HANDLE>`.
2. Verify baseline.
3. Read §1 materials, especially the reviewer's Risks.
4. Start with §3's first theorem
   (`<filter-name>_not_support_cardinality_only`) — it's the
   gating result.
5. Iterate through the remaining theorems in §3.
6. Compose Survivor.lean.
7. Write Critic report + ledger append.
8. Submit.

End of prompt template.
