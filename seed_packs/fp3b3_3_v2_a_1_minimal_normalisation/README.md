# Seed pack `fp3b3_3_v2_a_1_minimal_normalisation`

> **Track:** Research-A — sub-pack of `fp3b3_provenance_filter_v2_design/`,
> Stream X of the operator review at commit `33c8925`.
> **Method family:** `ac0_locality_support`.
> **Parent:** the `V2-A / gpt55` candidate ProvenanceFilter_v2,
> `informal` registry pin (commit `66a900a`), formally blocked for
> `accepted` promotion by NOGO-000008 (commit `e375dd4`).
> **Status:** **OPEN** — eligible for dispatch.
> **Priority:** **highest** in the V2-* design space — the only route
> back to a viable `accepted`-status candidate after NOGO-000008.

## 0. TL;DR

V2-A is purely syntactic, hence defeatable by tautological-seed
rewriting (NOGO-000008).  Sibling sub-pack `fp3b3_1` already proved
this is the same coin's other face as V2-A's escape from
Razborov-Rudich: non-extensionality on Boolean functions buys both.

This sub-pack defines **V2-A.1**: a successor candidate that composes
V2-A's existing four-conjunct filter with a **canonical syntactic
normalisation pass** on the displayed `FormulaCircuit`.  The
normalisation eliminates a small, fixed set of syntactic redundancies
(double negation, tautological seed gates, identity-of-AND with
`const true`, …) BEFORE the V2-A predicate is applied.

The intent: V2-A.1 should

* still **admit** the honest seeded prefix-AND family
  (`seededPrefixAndFamily`) and its disguised variants (e.g.
  `paddedSeededPrefixAndFamily` — currently REJECTED by V2-A, an
  outcome V2-A.1 is required to FIX);
* still **reject** the four classical adversary witnesses
  (NOGO-000001/4/5/6);
* additionally **reject** the rewrite-attack witness
  (`rewritePrefixAndWitness` from NOGO-000008) — kernel-checked as
  an explicit slot in this seed pack;
* **honestly re-classify** itself against the Razborov-Rudich
  naturality template, expecting **partial extensionality on the
  normalisation axis** — this is the price of escaping NOGO-000008
  and must be documented, not hidden.

If this seed pack lands, V2-A.1 becomes the new
`ProvenanceFilter_v2` successor candidate, eligible for its own
operator review and potentially for `accepted` promotion (gated on
that review).

## 1. Why minimal-formula normalisation (and not semantic quotient)

Two patch routes were enumerated in the operator review §7:

* **V2-A.1 (this seed pack):** minimal *syntactic* normalisation.
* **V2-A.2 (future):** full *semantic* (truth-table) equivalence
  quotient.

V2-A.2 is the stronger fix but at the price of full extensionality —
the Razborov-Rudich naturality barrier re-enters in full force.
V2-A.1 stays partially non-extensional (only the normalised axis
becomes extensional), so a fraction of the V2-A naturality escape is
preserved.

The operator decision (commit-time confirmation): V2-A.1 ships first.
V2-A.2 is deferred to a separate sub-pack `fp3b3_4_*` if and only if
V2-A.1 fails.

## 2. Goal (precise)

Five kernel-checked artifacts, dispatched in two rounds:

### Round 1 (THIS dispatch): T1 + T2

```lean
-- T1
def canonicalNormalise {n : Nat} : FormulaCircuit n → FormulaCircuit n
theorem canonicalNormalise_eval {n : Nat} (c : FormulaCircuit n) (x : Bitstring n) :
    eval (canonicalNormalise c) x = eval c x
theorem canonicalNormalise_size_le {n : Nat} (c : FormulaCircuit n) :
    FormulaCircuit.size (canonicalNormalise c) ≤ FormulaCircuit.size c

-- Plus targeted reduction lemmas (see §3 T1 for exhaustive list):
theorem canonicalNormalise_doubleNotPad_collapses : …
theorem canonicalNormalise_seedGate_collapses_to_true : …
theorem canonicalNormalise_rewritePrefixAnd_collapses_to_adversary : …

-- T2
def ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter
    {L : Language} (w : InPpolyFormula L) : Prop
theorem v2A_1_admits_seededPrefixAndWitness :
    ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter seededPrefixAndWitness
```

### Round 2 (NOT in this dispatch — gated on Round 1 landing): T3, T4, T5

```lean
-- T3 (classical exclusions inherit)
theorem v2A_1_excludes_overbroad : ¬ … (uniform_provenance_overbroad) …
theorem v2A_1_excludes_adversaryWitness_v_natlog2 : …
theorem v2A_1_excludes_adversaryWitness_v_arbpayload : …
theorem v2A_1_not_support_cardinality_only : …

-- T4 (NEW: anti-rewrite + bonus admission of disguised honest)
theorem v2A_1_excludes_rewritePrefixAndWitness :
    ¬ ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter rewritePrefixAndWitness
theorem v2A_1_admits_paddedSeededPrefixAndWitness :
    ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter paddedSeededPrefixAndWitness

-- T5 (Survivor + Critic report + RR re-classification)
theorem V2_A_1_<HANDLE>_survivor : <T2 ∧ T3 ∧ T4>
```

No `sorry`/`admit`, no `axiom`, no spec edits, no candidate package,
no FP-4 territory.

## 3. Slot decomposition (Round 1: T1, T2 — parallel-attackable)

Disjoint file paths under
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_1_<HANDLE>/`.

### T1 — canonical normalisation pass

**File:** `V2_A_1_<HANDLE>/Normalisation.lean`.

**Required reductions (HARD minimum):**

1. **Double-negation elimination:** `canonicalNormalise (not (not c)) = canonicalNormalise c`.
2. **Tautological binary OR with negation:** for any `c`,
   `canonicalNormalise (or c (not c)) = const true` and
   `canonicalNormalise (or (not c) c) = const true`.  This kills the
   `seedGate` shape used by NOGO-000008.
3. **AND identity with `const true`:**
   `canonicalNormalise (and c (const true)) = canonicalNormalise c`,
   `canonicalNormalise (and (const true) c) = canonicalNormalise c`.
4. **OR identity with `const false`:** symmetric.
5. **Structural recursion** on the formula tree.  The pass must be a
   single fixed-point pass: after applying the case rules
   bottom-up once, the formula must be in normal form (no further
   reductions applicable).  Worker discretion: if a worked-out
   fixed-point is structurally awkward, ship a recursive normaliser
   that applies the rules until a structural stop condition is met,
   accompanied by a termination proof.

**Optional reductions** (allowed but not required):

* AND with `const false` → `const false`; OR with `const true` → `const true`.
* Commutativity-driven canonical ordering of AND/OR operands.
* Anything else as long as `canonicalNormalise_eval` survives.

**Required theorems:**

```lean
theorem canonicalNormalise_eval {n : Nat} (c : FormulaCircuit n) (x : Bitstring n) :
    eval (canonicalNormalise c) x = eval c x

theorem canonicalNormalise_size_le {n : Nat} (c : FormulaCircuit n) :
    FormulaCircuit.size (canonicalNormalise c) ≤ FormulaCircuit.size c
```

**Targeted reduction lemmas** (required so T2-T4 can ship cleanly):

```lean
-- Used by T2 for size bound on normalised witnesses
theorem canonicalNormalise_doubleNotPad
    {n : Nat} (k : Nat) (c : FormulaCircuit n) :
    canonicalNormalise (doubleNotPad k c) = canonicalNormalise c

-- Used by T4 for the NOGO-000008 collapse
theorem canonicalNormalise_seedGate
    {n : Nat} (h : 1 ≤ n) :
    canonicalNormalise (seedGate n h) = const true

theorem canonicalNormalise_and_const_true
    {n : Nat} (c : FormulaCircuit n) :
    canonicalNormalise (and c (const true)) = canonicalNormalise c

theorem canonicalNormalise_and_true_const
    {n : Nat} (c : FormulaCircuit n) :
    canonicalNormalise (and (const true) c) = canonicalNormalise c
```

Plus, optionally, an idempotence lemma:

```lean
theorem canonicalNormalise_idempotent {n : Nat} (c : FormulaCircuit n) :
    canonicalNormalise (canonicalNormalise c) = canonicalNormalise c
```

**Expected LOC:** 100–200, depending on how aggressive the optional
reductions are.  The HARD-minimum reductions are sufficient to land T4.

**Critical scope rule:** `canonicalNormalise` MUST be a **structural,
syntactic** function on `FormulaCircuit n` — NO truth-table evaluation,
NO `Decidable`, NO Boolean-function representation as `Bitstring n →
Bool`.  If you find yourself needing to evaluate the formula on inputs
to decide what to do, you've crossed into V2-A.2 territory — STOP and
ship a failure report.

### T2 — V2-A.1 filter definition + non-vacuity

**File:** `V2_A_1_<HANDLE>/Filter.lean` + `V2_A_1_<HANDLE>/NonVacuity.lean`.

**Construction sketch:**

```lean
-- Filter.lean
namespace V2_A_1_<HANDLE>

/-- Apply canonicalNormalise pointwise to the witness's family.
This builds the normalised witness V2-A is applied to. -/
def normalisedWitness {L : Language} (w : InPpolyFormula L) :
    InPpolyFormula L where
  family := fun n => canonicalNormalise (w.family n)
  polyBound := w.polyBound
  polyBound_poly := w.polyBound_poly
  family_size_le := fun n =>
    (canonicalNormalise_size_le _).trans (w.family_size_le n)
  correct := fun n x => by
    rw [canonicalNormalise_eval]; exact w.correct n x

def ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter
    {L : Language} (w : InPpolyFormula L) : Prop :=
  ProvenanceFilter_v2_V2_A_gpt55_Filter (normalisedWitness w)

end V2_A_1_<HANDLE>
```

**Required non-vacuity theorem:**

```lean
-- NonVacuity.lean
theorem v2A_1_admits_seededPrefixAndWitness :
    ProvenanceFilter_v2_V2_A_1_<HANDLE>_Filter seededPrefixAndWitness
```

This should follow from V2-A's existing `seededPrefixAndWitness_admitted`
plus the observation that `canonicalNormalise (seededPrefixAndFamily n)
= seededPrefixAndFamily n` (the honest family is already in normal
form — the worker must prove this as a small targeted lemma if it
isn't trivially `rfl`).

**Expected LOC:** 40–80 across both files.

**Scope rule:** if `canonicalNormalise (seededPrefixAndFamily n)` is
**not** equal (definitionally or propositionally) to
`seededPrefixAndFamily n`, the worker must investigate.  Either:
* the seeded family has a normalisable redundancy (refine the family,
  but that's editing V2-A's NonVacuity — forbidden), or
* T1's normalisation is too aggressive (refine T1).

This is the first stress-test of T1's design.  If T2 reveals that the
honest family does not survive normalisation in admissible form,
T1 has structural issues and T2 should ship a structured failure
report at
`seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T2_<HANDLE>_seed_normalisation_collision.md`.

### Round 2 slots (preview only — do NOT pick in this dispatch)

* **T3** — classical exclusions inherit from V2-A.  Files:
  `ExcludesOverbroad.lean`, `ExcludesPrefixAnd.lean`,
  `ExcludesArbitraryPayload.lean`, `NotSupportCardinalityOnly.lean`.
  Each is a 1–3 line proof of the form "normalise leaves the adversary
  family fixed (or reduces to another excluded family), hence V2-A's
  exclusion transports."
* **T4** — anti-rewrite theorem
  `v2A_1_excludes_rewritePrefixAndWitness` + bonus admission theorem
  `v2A_1_admits_paddedSeededPrefixAndWitness`.  File:
  `AntiRewrite.lean`.  Mandatory accompanying markdown:
  `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/reports/V2_A_1_<HANDLE>_natural_proofs_reclassification.md`
  — honest re-classification of V2-A.1 against Razborov-Rudich (expected
  outcome: **partial re-entry of barrier on normalised axis**).
* **T5** — Survivor packaging + Critic report.  Files:
  `Survivor.lean` + `critic_reports/V2_A_1_<HANDLE>.md`.

Round 2 opens only after T1 + T2 land.  Do not pre-stage Round 2
artifacts in Round 1 commits.

## 4. Allowed / forbidden scope

### Allowed (per slot, Round 1)

* New files under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_1_<HANDLE>/`.
* `lakefile.lean` — append new modules to the existing
  `Glob.one ...` list.
* Optional smoke test at
  `pnp3/Tests/AuditRoutes_V2A1_<HANDLE>_Smoke.lean` wired through
  `lakefile.lean`.

### Forbidden (HARD)

* Trust root: `pnp3/Complexity/Interfaces.lean` (in particular, no
  edits to `FormulaCircuit` / `eval` / `support` / size definitions),
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/{UnconditionalResearchGap,LocalityProvider_Partial,FinalResultMainline,FinalResultAuditRoutes}.lean`.
* Editing **any** V2-A file in
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/` —
  V2-A's predicate, exclusion proofs, NonVacuity, Survivor, the
  natural-proofs self-test, and the rewrite attack are ALL imports,
  not editables.
* Editing fp3b1 / fp3b2 / fp3b4 theorem bodies — generalise/import,
  do not rewrite.
* Editing existing JSONL log entries (Rule 9 — append-only).
* `axiom` / `opaque` / `Fact` / typeclass-payload (Rule 16).
* `sorry` / `admit` (Rule 1).
* `pnp3/Candidates/<id>/` creation (audit-only routing).
* `gap_from_*`, `SourceTheorem_*` (FP-4 territory).
* Promoting `ProvenanceFilter_v2` or `V2_A_1_<HANDLE>` to `accepted` —
  promotion gates on operator review of Round 2's Survivor + Critic.
* Designing V2-A.2 (semantic-equivalence quotient) — separate
  sub-pack `fp3b3_4_*` if needed.
* Adding NOGO entries for V2-A.1 — this is positive territory; if
  the worker thinks an entry is warranted, append a paragraph to
  the Round 2 critic report instead and let operator decide.
* Using truth-table semantics inside `canonicalNormalise` — see T1
  critical scope rule above.

## 5. Slot acceptance criteria

A slot Sₖ is **complete** when:

1. The Lean theorem(s) listed for Sₖ compile in the target file
   path with no `sorry` / `admit`.
2. `lake build PnP3 Pnp4` green.
3. `./scripts/check.sh` 17/17 + sub-steps green.
4. `rg "\bsorry\b|\badmit\b" -g"*.lean"
    pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_1_<HANDLE>/`
   returns nothing.
5. PR description names each new theorem and its file:line.
6. No file outside §4 allowed scope was modified.

## 6. Per-slot failure criterion

If a slot is structurally unreachable, ship a markdown failure report
at

```
seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T<k>_<HANDLE>.md
```

with four sections:

1. **What was attempted.**
2. **Where it broke** (Lean error verbatim).
3. **Local vs global obstruction.**
   * Local: missing helper lemma; recoverable.
   * Global: V2-A.1's normalisation approach is structurally wrong
     (e.g. `canonicalNormalise (seededPrefixAndFamily n)` cannot be
     made equal to `seededPrefixAndFamily n` without truth-table
     evaluation).  This would itself be a research result —
     the operator review's Stream X choice is then refuted, and
     the dispatcher should consider V2-A.2 (semantic quotient,
     `fp3b3_4_*`) instead.
4. **What an integrator must know.**

A T2 failure of the form "normalisation collapses the honest seed
gate into `const true`, but `seededPrefixAndFamily` definition uses
`seedGate` directly, so V2-A.1 admits a DIFFERENT formula than V2-A
admits" is a **local** obstruction — worker can refactor T1 to not
touch the *single* seed gate inside an `and`-chain (subtler design),
OR can ship the failure with a recommendation that V2-A's NonVacuity
construction be re-thought.  The decision is the operator's; do not
edit V2-A from this dispatch.

## 7. Critic angles (six attacks for Round 2's T5 critic_report.md)

Preview for the future T5 worker.  Round 1 workers do not need to
write a critic report.

* **Hidden-payload attack.**  Does V2-A.1 use `class`/`instance`/`Fact`/
  `opaque` to smuggle a Boolean-function check disguised as a
  syntactic check?  Expected: no.  Proof: `canonicalNormalise` is
  structural recursion only.
* **Hardwiring attack.**  Operator's question: does V2-A.1 admit
  ANY hardwiring witness through a normalisation gap?  The NOGO-000008
  rewrite attack is one such; T4 explicitly addresses it.  Critic
  should attempt one more rewrite shape (e.g. seed via
  `and (input 0) (or (input 1) (not (input 1)))` — two-coord
  redundancy) and report whether V2-A.1's normalisation handles it.
  If not, propose either a T1 strengthening or document the residual
  attack surface.
* **KnownGuards-factorization.**  Does V2-A.1 factor through a known
  guard?  Expected: no (audit-only, no `gap_from_*`).
* **Natural-proofs / relativization / algebrization.**  THE central
  caveat.  V2-A.1 is partially extensional on the normalisation axis;
  expected verdicts:
  * Constructivity: still `yes` (predicate is decidable on the
    displayed formula tree).
  * Largeness: borderline — by quotienting through normalisation,
    V2-A.1 is *closer* to a Boolean-function-property than V2-A but
    not all the way there (rewriting outside the normalisation
    targets still bypasses).
  * Usefulness: same scope as V2-A modulo the new admission of
    `paddedSeededPrefixAndWitness`.
  * Extensionality: `partial` — extensional on the normalisation axis,
    non-extensional elsewhere.
  * Razborov-Rudich (audit predicate use): `partial_re_entry`.  The
    barrier applies to the normalised axis; engineer must explicitly
    enumerate which Boolean functions V2-A.1 cannot consistently
    classify due to remaining non-extensionality.
* **Collapse-not-contradiction.**  Verify V2-A.1 isn't trivially
  empty or trivially full.  Non-vacuity (T2) prevents emptiness.
  The classical exclusions (T3) prevent fullness.
* **Vacuity / source-theorem rephrasing.**  Verify V2-A.1 is not
  just a rename of V2-A.  Concrete check: V2-A.1 admits
  `paddedSeededPrefixAndWitness`, V2-A rejects it.  These two
  predicates DIFFER on this witness — V2-A.1 is not a notational
  rephrasing of V2-A.

## 8. What this seed pack does NOT do

* Design V2-A.2 (semantic-equivalence quotient).  That is a separate
  sub-pack `fp3b3_4_*` if V2-A.1 fails or if a parallel candidate
  is desired.
* Promote V2-A.1 to `accepted`.  Promotion is gated on operator
  review of Round 2's Survivor + Critic report.
* Append NOGO entries.  V2-A.1 is intended to be a positive result
  (a successor candidate), not a barrier.
* Construct a fourth or fifth classical barrier theorem at the
  Razborov-Rudich level — this is local to FP-N filter design.
* Activate Pilot Wave 1, edit trust root, edit any V2-A file, edit
  any fp3b1/fp3b2/fp3b4 file.
* Open V2-B / V2-D Phase 2 dispatches (separate Stream Y).

## 9. Cross-references

* Stream X origin: operator review at
  `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/fp3b3_1_and_fp3b3_2_landing_review.md` §7.
* Parent V2-A artifacts (imports, NOT editables):
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/{Sketch,Filter,ExcludesOverbroad,ExcludesPrefixAnd,ExcludesArbitraryPayload,NonVacuity,NotSupportCardinalityOnly,Survivor}.lean`.
* NOGO-000008 (the attack V2-A.1 must resist):
  `outputs/nogolog.jsonl::NOGO-000008` and Lean witness
  `pnp3/.../V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean::v2A_rewrite_attack_prefixAnd`.
* Razborov-Rudich self-test on V2-A (companion to T4 re-classification):
  `pnp3/.../V2_A_gpt55/NaturalProofsSelfTest/RepresentationSensitivity.lean::v2A_same_language_different_representation`.
* Honest seeded family (must remain admitted):
  `pnp3/.../V2_A_gpt55/NonVacuity.lean::seededPrefixAndWitness`.
* Sibling sub-packs:
  `seed_packs/fp3b3_1_v2a_natural_proofs_self_test/`,
  `seed_packs/fp3b3_2_v2a_adversarial_robustness/`.
* `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.
* `spec/critic_protocol.md` — for Round 2's T5 critic format.
* Classical Razborov-Rudich barrier (read-only context for T4's
  re-classification):
  `pnp3/Barrier/NaturalProofs.lean`.

## 10. Closing note

> V2-A.1 is the **first attempted patch** of V2-A under the
> kernel-checked anti-evidence of NOGO-000008.  It targets exactly
> the syntactic redundancies the rewrite attack exploited, no
> wider.  If it lands, the V2-* design space has a successor with
> measured Razborov-Rudich re-entry — a clean intermediate point
> between "fully non-extensional but trivially defeatable" (V2-A)
> and "fully extensional but barrier-bound" (V2-A.2).  If it
> fails on T1's structural impossibility, that is itself a result:
> the audit predicate's escape from the barrier may be inseparable
> from its rewrite vulnerability.

Round 1 cap: T1, T2 only.  Round 2 (T3, T4, T5) opens when T1 + T2
have landed.  Do not stage Round 2 artifacts in a Round 1 commit.
