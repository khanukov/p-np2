# Seed pack `fp3b3_provenance_filter_v2_design`

> **Track:** Research-A — positive line of FP-N closure.
> **Prerequisite:** `seed_packs/fp3b4_support_cardinality_barrier/`
> Phase 1 should ideally have shipped its barrier theorem before
> `fp3b3` Phase 2 starts.  Phase 1 of `fp3b3` (paper sketch) can
> run in parallel with `fp3b4`.
> **Status:** OPEN — eligible for Pilot Wave 1 parallel attack.
> **Method family:** `ac0_locality_support`.
> **Priority:** second (after `fp3b4` ships its barrier theorem).

## 0. TL;DR

`fp3b2` shipped `NOGO-000006`: support-cardinality-only filters
admit arbitrary all-essential log-width truth-table payload.
`fp3b4` (in flight) generalises this to a meta-barrier: ANY
support-cardinality-only filter is dead.

The positive line: **design a structure-sensitive
`ProvenanceFilter_v2` that survives the existing obstructions**.

This seed pack runs FOUR parallel filter-design directions —
each independently attempts a candidate v2 satisfying:

1. excludes `NOGO-000001` (overbroad uniform provenance),
2. excludes `NOGO-000004 / NOGO-000005` (prefix-AND specialisation),
3. excludes `NOGO-000006` (arbitrary all-essential `ttFormula` payload),
4. is **non-vacuous** — admits at least one named honest family
   (parity is the canonical example).

A v2 candidate that clears all four is a survivor.  No v2 is
"chosen" at the seed-pack level: each direction independently
ships either a survivor candidate (for human-Critic review) or a
structured failure report.

## 1. Why FOUR directions, not ten

After `NOGO-000006`, search space narrowed: any v2 must use
information **beyond** support cardinality.  Four orthogonal
directions cover the structural information families that FP-N
pipeline shape can plausibly use:

| Direction | What it inspects | Adversary class it might exclude |
| --------- | ---------------- | -------------------------------- |
| **V2-A formula-shape** | Gate types, formula tree depth, AND/OR/NOT counts | Truth-table-shaped formulas (deep, balanced) |
| **V2-B cross-length coherence** | Whether the family has a coherent recipe across lengths | Hardwired families that re-pick payload at every length |
| **V2-C bounded incremental information** | Information added at each length (e.g., bounded edit distance, bounded recipe extension) | Families that inject new arbitrary `ttFormula` payload at each length |
| **V2-D rename / provenance signature** | Whether the family is invariant under input renaming, or carries a provenance signature distinguishing constructions | Families produced by `rename σ_n (ttFormula f_n)` for arbitrary `σ_n` |

Each direction has independent risk of vacuity (filter excludes
EVERYTHING including parity) and of leak (filter still admits
some hardwiring shape).

## 2. Common structure (all four directions)

Each direction's worker ships TWO phases:

### Phase 1 — paper sketch (1-3 days, low cost)

A new file at
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<Direction>_<HANDLE>/Sketch.lean`
containing:

```lean
-- The candidate filter as a Lean Prop, kernel-checked at the type
-- level (no proofs yet).
def ProvenanceFilter_v2_<Direction>_<HANDLE>
    {L : Language} (w : InPpolyFormula L) : Prop := …
```

PLUS a docstring with FIVE explicit paper-mathematical sketches:

1. **Excludes NOGO-000001** sketch (one paragraph: how does this
   filter rule out `OverbroadUniformProvenance`?).
2. **Excludes NOGO-000004/5** sketch (how does it rule out
   `prefixAnd` log-width specialisation?).
3. **Excludes NOGO-000006** sketch (how does it rule out arbitrary
   all-essential `ttFormula` payload?).
4. **Non-vacuity** sketch — name a specific honest family the
   filter MUST admit (e.g., parity / pseudorandom function /
   AC0-computable function), and argue why your filter admits it.
5. **Self-attack** sketch — what's the most dangerous attack on
   YOUR specific candidate?  If you can already see it dies, file
   a failure report instead.

Phase 1 is operator-reviewable in 30-60 minutes.  If the paper
sketches don't survive review, Phase 2 doesn't start.

### Phase 2 — full Lean self-attack (2-6 weeks, high cost)

Gated on Phase 1 review.  Files under
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<Direction>_<HANDLE>/`:

* `Filter.lean` — the candidate `Prop`, Lean-formalized.
* `ExcludesOverbroad.lean` — kernel-checked theorem:
  `∀ ac0 (w : InPpolyFormula …), OverbroadUniformProvenance ac0 ∧ … → ¬ Π_v2 w`.
* `ExcludesPrefixAnd.lean` — kernel-checked theorem against
  `LogWidthAdversary.adversaryWitness_v_natlog2` (fp3b1 family).
* `ExcludesArbitraryPayload.lean` — kernel-checked theorem against
  `ArbitraryLogWidthTT.adversaryWitness_v_arbpayload` (fp3b2
  family).
* `NonVacuity.lean` — exhibit + admit-proof for at least one
  named honest family (parity strongly recommended).
* `Survivor.lean` — single integration theorem composing the four
  exclusions + non-vacuity into a "candidate v2 surviving all
  known obstructions."

Phase 2 is the survivor candidate; if it ships, the candidate goes
to human-Critic review for promotion consideration.  If it
doesn't, ship a structured Phase 2 failure report.

## 3. Per-direction mandatory references

### V2-A formula-shape

Look at `FormulaCircuit` constructor count / depth / gate types.
Recommended structural property to test:

```lean
def hasNoExpDepthSpike (w : InPpolyFormula L) : Prop :=
  ∀ n, FormulaCircuit.depth (w.family n) ≤ Nat.log2 (n + 1) + C
```

(Some constant `C`.) Or other shape-based property.  Worker
discretion; the goal is to FAIL `prefixAnd` (which has linear
depth at log-width) AND `ttFormula` (deep balanced tree).

Risk: filter may also reject linear-depth honest formulas.
Non-vacuity needs a honest family with `O(log n)` depth (parity
fits).

### V2-B cross-length coherence

**MUST reuse** the existing CL-0 audit module:

`pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean`

defines

```lean
namespace Pnp3.Magnification.AuditRoutes.CrossLengthCoherence

def NaiveCrossLengthCoherence {α : Type} (F : ToyFamily α) : Prop := ...
def StrongCrossLengthCoherence {α : Type} (F : ToyFamily α) : Prop := ...
def CL0_Target_naive_coherence_accepts_table_hardwiring : Prop := ...
def CL0_Target_logWidthHardwiring_breaks_strong_coherence : Prop := ...
```

These are research-target Props (not theorems).  V2-B's job is to
either (a) lift `StrongCrossLengthCoherence` into a real predicate
on `InPpolyFormula` and prove it excludes the four obstructions, or
(b) prove `CL0_Target_naive_coherence_accepts_table_hardwiring`
(weak coherence is ALSO dead) — the second outcome is itself a
new NoGo result, not a v2 survivor.

Either output is valuable.  V2-B is the highest-information
direction because the 12-engineer audit already converged here.

### V2-C bounded incremental information

Idea: family must satisfy

```lean
∀ n, family (n+1) is "δ-extension" of family n
```

for some bounded δ.  Hardwired families that re-pick `f_n`
arbitrarily fail this; honest families with a fixed recipe
satisfy it.

Critical: pick a definition of "δ-extension" that's:
* formal (Lean-checkable),
* satisfied by parity or another honest family,
* violated by `rename σ_n (ttFormula f_n)` for arbitrary `f_n`.

This is the hardest direction to formalise; ⅔ probability of
failure expected.

### V2-D rename / provenance signature

Two sub-options:

(i) **Non-rename-invariance.**  Filter looks at *which*
coordinates the family touches, not just how many.  But: any
filter touching specific coordinate identities is fragile under
honest renamings (`x_0 ∧ x_1` and `x_3 ∧ x_5` should be
indistinguishable for honest purposes).

(ii) **Provenance signature.**  Family carries an explicit
"recipe" tag (`Generated`/`Hardwired`/`RenameOf …`) inspected by
the filter.  Risk: signature is itself a candidate provenance,
making the filter circular.

V2-D's success criterion is sharper than the others: must
exhibit non-circularity.

## 4. Allowed / forbidden scope

### Allowed (per direction worker)

* New files under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<Direction>_<HANDLE>/`.
* `lakefile.lean` — append new modules.
* Optional smoke at
  `pnp3/Tests/AuditRoutes_ProvenanceFilterV2_<Direction>_<HANDLE>_Smoke.lean`.
* If V2-B: may use `CrossLengthCoherence_NoGo.lean` types
  (read-only, do not edit them).
* If Phase 2 survivor: append one `outputs/attempts.jsonl` entry,
  ship critic_report.md per `spec/critic_protocol.md`.

### Forbidden (HARD)

* Trust root.
* Editing `FP3Attempt.InSupportFunctionalDiversity` or any
  fp3b1/fp3b2/fp3b4 theorem.
* Editing `CrossLengthCoherence_NoGo.lean` predicates (V2-B uses
  them, doesn't change them).
* Editing existing JSONL entries (Rule 9 — append-only).
* `axiom`, `opaque`, `Fact`, typeclass-payload (Rule 16).
* `sorry` / `admit` in committed Lean (Rule 1).
* `pnp3/Candidates/<id>/` creation.
* `gap_from_*`, `SourceTheorem_*`, final endpoint (FP-4 — gated).
* `ProvenanceFilter_v1` promotion.
* **Promoting any v2 candidate to "accepted" via this seed pack.**
  Survivor candidates ship; promotion is a separate seed pack
  (post-fp3b3).
* **Designing v2 in `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/`** —
  that's `fp3b4`'s zone.

## 5. Acceptance criteria

### Phase 1

- [ ] `lake build PnP3 Pnp4` green (the candidate `Prop` compiles).
- [ ] Five paper-sketch sections present in docstring.
- [ ] Self-attack section is sincere (not "no obvious break" without
      argument).
- [ ] PR description names the candidate filter and its file:line.

### Phase 2 (gated on Phase 1 review)

- [ ] All four exclusion theorems compile, no `sorry` / `admit`.
- [ ] Non-vacuity theorem compiles.
- [ ] `Survivor.lean` integration theorem compiles.
- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` 17/17 + sub-steps green.
- [ ] `rg "\bsorry\b|\badmit\b"` clean on the new files.
- [ ] One `outputs/attempts.jsonl` line referencing a non-template
      Critic report.
- [ ] Critic report follows `spec/critic_protocol.md` §1–3 with
      `critic_status = pass`.

## 6. Per-direction failure criterion

If the direction proves structurally hopeless within the allowed
scope, ship a markdown failure report at

```
seed_packs/fp3b3_provenance_filter_v2_design/failures/<Direction>_<HANDLE>_phase<N>.md
```

with the four sections (what was attempted, where it broke, local
vs global obstruction, what the integrator must know).

A `global` obstruction is itself useful: if all four directions
ship global failures, the FP-N pipeline shape is empirically
saturated, and strategy must shift to (a) different method-family
or (b) `MetaFilterBarrier_NoGo` formalisation at higher level
than `fp3b4`.

## 7. Run protocol — sequencing

```text
Step 0: fp3b4 Phase 1 lands (T1..T5 of the barrier seed pack).
        This gives fp3b3 directions the kernel-checked precondition
        "must NOT be support-cardinality-only".

Step 1: 4 fp3b3 workers each ship Phase 1 (paper sketches).  ~3 days.

Step 2: Operator reviews 4 Phase-1 deliverables.
        - Surviving Phase 1s → Phase 2 dispatch.
        - Failing Phase 1s → archived as failure reports.

Step 3: Phase-2 workers ship Lean exclusion proofs + non-vacuity.
        ~2-6 weeks each.

Step 4: Surviving Phase-2 candidates → human-Critic review for
        promotion to spec/known_guards.toml::ProvenanceFilter_v2 =
        "informal" (or "accepted" only with FP-4 readiness gate
        passed in a future PR — not this seed pack).

Step 5: Failing Phase-2 → NoGo entries (NOGO-000008 onward).
```

## 8. Cross-references

* Predecessors: `outputs/nogolog.jsonl::NOGO-000001`,
  `NOGO-000004`, `NOGO-000005`, `NOGO-000006`.
* `fp3b4_support_cardinality_barrier/` (sibling, prerequisite).
* `pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean`
  (V2-B mandatory input).
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean`
  (NOGO-000004 family).
* `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean`
  (NOGO-000006 family).
* `pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`
  (classical barriers — v2 candidates that smell like a "natural
  property" must explicitly address Razborov-Rudich).
* `spec/critic_protocol.md` — Critic format.
* `seed_packs/PILOT_WAVE_0_PROTOCOL.md` — worker cycle.

## 9. What this seed pack does NOT do

* Does NOT promote `ProvenanceFilter_v2` to `accepted`.
  Survivor candidates ship as informal proposals for human review.
* Does NOT start FP-4 / construct `gap_from_*` / produce a
  `SourceTheorem`.
* Does NOT touch the trust root.
* Does NOT prove or disprove `P ≠ NP`.

## 10. Closing note

> Four orthogonal probes; not a tournament with a winner.
> Each direction independently produces either a survivor
> candidate (for human-Critic review) or a structured failure
> (for NoGo ledger).  Saturation across all four directions
> is itself a research result that forces strategy shift.

Pilot Wave 1 cap is 20 workers; this seed pack's 4 directions ×
2 phases = 8 worker-tasks fit comfortably alongside `fp3b4` (6
slots) and `first_move_search_2026` (3-5 reports).
