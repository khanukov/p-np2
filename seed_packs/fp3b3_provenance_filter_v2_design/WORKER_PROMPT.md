# Worker prompt — fp3b3_provenance_filter_v2_design

> Send this entire file as the prompt body.  Workers self-pick
> `<HANDLE>` and `<DIRECTION>` ∈ {V2-A, V2-B, V2-C, V2-D}.  At
> most one worker per `(direction, phase)` slot at a time.

---

You are designing one direction of `ProvenanceFilter_v2` —
a structure-sensitive filter on `InPpolyFormula L` records that
must survive all currently-formalised obstructions.

Pick a unique `<YOUR-HANDLE>` (initials, model name, etc.).

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN.  If RED on a fresh checkout, stop.

## 1. Required reading

1. `seed_packs/fp3b3_provenance_filter_v2_design/README.md` —
   the four directions, two-phase shipping contract,
   allowed/forbidden scope.
2. The four formal obstructions any v2 must clear:
   - `outputs/nogolog.jsonl::NOGO-000001`,
   - `outputs/nogolog.jsonl::NOGO-000004`,
   - `outputs/nogolog.jsonl::NOGO-000005`,
   - `outputs/nogolog.jsonl::NOGO-000006`.
3. The candidate filter shape under attack:
   `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3Attempt.InSupportFunctionalDiversity`
   (line 231).  Your v2 candidate is a stronger `Prop` on
   `InPpolyFormula L`.
4. Existing adversary witnesses your filter must EXCLUDE:
   - `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2`
     (NOGO-000004 family),
   - `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean::adversaryWitness_v_arbpayload`
     (NOGO-000006 family).
5. If you pick `V2-B`, also:
   `pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean`
   (CL-0 def-targets — your filter MUST reuse them, not invent
   coherence anew).
6. `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.

## 2. Pick your direction

| Direction | Inspects | Adversary class targeted | Risk |
| --------- | -------- | ------------------------ | ---- |
| V2-A formula-shape | gate types, depth, AND/OR/NOT counts | balanced truth-table-shaped formulas | filter may reject honest deep formulas |
| V2-B cross-length coherence | recipe coherence across lengths (use CL-0) | hardwired families re-picking payload at every length | weak coherence may itself be too admissive |
| V2-C bounded incremental information | δ-extension between consecutive lengths | families injecting new ttFormula payload at every length | hard to formalise in Lean cleanly |
| V2-D rename / provenance signature | non-rename-invariance OR explicit provenance tag | rename σ_n (ttFormula f_n) for arbitrary σ_n | risk of circularity (filter is itself a provenance candidate) |

Pick ONE.  Specialise its idea in your own way.  Document the
choice in your filter's docstring.

## 3. Two-phase shipping contract

### Phase 1 — paper sketch (1-3 days)

Single new file at

```
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<Direction>_<HANDLE>/Sketch.lean
```

Containing:

```lean
namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace <Direction>_<HANDLE>

open Pnp3.ComplexityInterfaces

/-- v2 candidate filter — paper sketch only. -/
def ProvenanceFilter_v2_<Direction>_<HANDLE>
    {L : Language} (w : InPpolyFormula L) : Prop := ...

/-- Phase 1 only — Lean smoke that the predicate elaborates.
    Phase 2 will replace this with real exclusion theorems. -/
theorem v2_<Direction>_<HANDLE>_phase1_loaded : True := trivial

end <Direction>_<HANDLE>
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
```

PLUS a docstring with FIVE paragraphs (paper-mathematical, no
proofs yet):

1. **Excludes NOGO-000001** — one paragraph: how does this filter
   rule out OverbroadUniformProvenance shape?
2. **Excludes NOGO-000004/5** — how does it rule out
   prefixAnd-on-log-width?
3. **Excludes NOGO-000006** — how does it rule out arbitrary
   all-essential ttFormula payload?
4. **Non-vacuity** — name a SPECIFIC honest family the filter
   admits.  Strongly recommended: parity (the formula computing
   XOR of all `n` input bits).  Argue why your filter admits it.
5. **Self-attack** — what's the most dangerous attack you can
   already see on YOUR specific candidate?  If you can already
   exhibit a hardwiring witness inside your filter, file a Phase-1
   failure report instead of shipping the sketch.

Phase 1 is operator-reviewable in 30-60 minutes.  If it doesn't
survive review, you do not start Phase 2.

### Phase 2 — full Lean self-attack (2-6 weeks)

Files under
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<Direction>_<HANDLE>/`:

* `Filter.lean` — the candidate `Prop`, full Lean.
* `ExcludesOverbroad.lean` — kernel-checked theorem.
* `ExcludesPrefixAnd.lean` — kernel-checked theorem against
  `LogWidthAdversary.adversaryWitness_v_natlog2`.
* `ExcludesArbitraryPayload.lean` — kernel-checked theorem against
  `ArbitraryLogWidthTT.adversaryWitness_v_arbpayload`.
* `NonVacuity.lean` — exhibit at least one specific honest family
  AND prove the filter admits it.
* `Survivor.lean` — single integration theorem composing the four
  exclusions + non-vacuity.

Plus:

* Updated `lakefile.lean` wiring.
* Optional smoke test under `pnp3/Tests/`.
* `outputs/attempts.jsonl` append (one entry, `seed_pack_id =
  fp3b3_provenance_filter_v2_design`,
  `verifier_status = PASS_SHAPE_ONLY`, `critic_status = pass`,
  `critic_report_path` pointing at your Phase-2 critic_report.md).
* `seed_packs/fp3b3_provenance_filter_v2_design/critic_reports/<Direction>_<HANDLE>.md`
  — six-attack Critic report per `spec/critic_protocol.md`.

**Phase 2 acceptance checklist:**

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` green (17/17 + 12.b/c/d/e/f/g/h/j/k).
- [ ] `rg "\bsorry\b|\badmit\b" -g"*.lean"
       pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<Direction>_<HANDLE>/`
      returns nothing.
- [ ] All four exclusion theorems compile.
- [ ] Non-vacuity theorem compiles AND admits a named honest
      family (parity or equivalent).
- [ ] Survivor.lean integration theorem compiles.
- [ ] `validate_jsonl.py` green on both ledgers.
- [ ] Critic report classified `pass` per spec/critic_protocol.md
      §1–3.

## 4. Forbidden scope (HARD)

* Trust root.
* Editing `FP3Attempt.InSupportFunctionalDiversity` predicate.
* Editing fp3b1 / fp3b2 / fp3b4 theorem bodies.
* Editing `CrossLengthCoherence_NoGo.lean` predicates (V2-B uses
  them, doesn't change them).
* Editing existing JSONL log entries (Rule 9 — append-only).
* `axiom`, `opaque`, `Fact`, typeclass-payload (Rule 16).
* `sorry` / `admit` in committed Lean (Rule 1).
* `pnp3/Candidates/<id>/` creation.
* `gap_from_*`, `SourceTheorem_*`, final endpoint.
* `ProvenanceFilter_v1` promotion to `accepted`.
* **Promoting your v2 candidate to "accepted" via this seed
  pack.**  Survivors ship as informal proposals; promotion is a
  separate post-fp3b3 PR.
* Working under `SupportCardinalityBarrier/` — that's `fp3b4`.
* Working under `FirstMoveSearch2026/` — that's
  `first_move_search_2026`.
* Editing other workers' `<other-direction>_<other-handle>/`
  directories — independent parallel attempts.

## 5. Output (exactly ONE per phase)

### Outcome A — slot delivers

Submit a unified diff or branch named
`worker/fp3b3/<Direction>_<HANDLE>_phase<N>` containing the
phase-appropriate files.

### Outcome B — structured failure report

```
seed_packs/fp3b3_provenance_filter_v2_design/failures/<Direction>_<HANDLE>_phase<N>.md
```

with the four sections: what was attempted, where it broke (Lean
errors verbatim if Phase 2; mathematical obstacle if Phase 1),
local vs global, what the integrator must know.

A **global** obstruction in any one direction is itself useful;
saturation across all four directions strongly suggests FP-N
pipeline shape is exhausted.

## 6. Common documented traps

* **Vacuity.**  Filter that excludes everything — including
  parity — is a win against hardwiring but useless.  Phase-1
  paragraph 4 is non-negotiable.
* **Circularity (V2-D especially).**  Filter that asks "is this
  family itself a valid provenance" is itself a provenance
  candidate.  Need a non-circular grounding.
* **Hidden classical-barrier compatibility.**  If your filter
  smells like a "natural property" in the Razborov-Rudich sense,
  you must explicitly address it.  See `pnp3/Barrier/NaturalProofs.lean`.
* **Support-cardinality-only.**  Your filter MUST use information
  beyond `n ↦ (support (w.family n)).card`.  After `fp3b4` lands
  its barrier theorem, this is a kernel-checked precondition.

## 7. Begin

1. Pick `<YOUR-HANDLE>` and `<DIRECTION>`.
2. Verify green baseline.
3. Read §1 materials.
4. Ship Phase 1 sketch.
5. Wait for review.
6. If approved, ship Phase 2.  If rejected, ship structured
   failure report and stop.

End of prompt.
