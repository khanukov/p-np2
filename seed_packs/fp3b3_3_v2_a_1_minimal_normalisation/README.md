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

If T1 globally fails (the structural normalisation impossibility
result), the operator pivots to a meta-barrier seed pack
`fp3b3_4_v2_a_normalise_meta_barrier/` — see §10 for the
negative-pivot protocol.  This dispatch is therefore **positive
with pre-staged negative pivot readiness** — either outcome
produces durable research artifacts.

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

**Required reductions (HARD minimum) — REVISED after g55 audit:**

1. **Double-negation elimination:** `canonicalNormalise (not (not c)) = canonicalNormalise c`.
2. **Constant negation under NOT (NEW after g55 audit):** for the two
   constants, `canonicalNormalise (not (const true)) = const false`
   and `canonicalNormalise (not (const false)) = const true`.
   **Derivation, not extension:** these are forced by the existing
   AND-identity + AND-contradiction lemmas under specialisation at
   `C := const true` / `C := not (const true)` (see audit document
   `audits/T1_g55_operator_audit.md` §1).  Adding them explicitly
   removes the spec inconsistency g55 discovered.
3. **Tautological binary OR with negation:** for any `c`,
   `canonicalNormalise (or c (not c)) = const true` and
   `canonicalNormalise (or (not c) c) = const true`.  This kills the
   `seedGate` shape used by NOGO-000008.
4. **Contradictory binary AND with negation:** symmetric for AND —
   `canonicalNormalise (and c (not c)) = const false` and
   `canonicalNormalise (and (not c) c) = const false`.  Pre-empts a
   trivial NOGO-000008-style dual attack via contradiction-seeded AND.
5. **AND identity with `const true`:**
   `canonicalNormalise (and c (const true)) = canonicalNormalise c`,
   `canonicalNormalise (and (const true) c) = canonicalNormalise c`.
6. **OR identity with `const false`:** symmetric.
7. **Structural recursion** on the formula tree.  The pass must be a
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

**Canonical-output invariant (NEW after g55 audit):**

g55's failure report flagged that the originally-requested
`canonicalNormalise_double_not` is **false** as an unconditional
local involution on raw `FormulaCircuit` syntax — it holds only on
the **image** of `canonicalNormalise`.  Repair: introduce a
syntactic normal-form predicate, prove every output is canonical,
derive the originally-shaped theorem as a wrapper.

```lean
/-- Syntactic normal-form predicate.  Canonical outputs avoid these
shapes at the root (and recursively in sub-formulas, modulo the
inductive clauses for and/or). -/
inductive IsCanonical : {n : Nat} → FormulaCircuit n → Prop
  -- const and variable nodes are always canonical
  -- (not (const _)) at root: FORBIDDEN
  -- (not (not _)) at root:   FORBIDDEN
  -- recursive clauses for and / or with canonical sub-formulas
  | -- ... (worker fills in)

/-- Every output of canonicalNormalise satisfies IsCanonical. -/
theorem canonicalNormalise_isCanonical {n : Nat}
    (C : FormulaCircuit n) :
    IsCanonical (canonicalNormalise C)

/-- Image-invariant double-not: holds on canonical inputs. -/
theorem canonicalNormalise_double_not_canonical {n : Nat}
    (C : FormulaCircuit n) (h : IsCanonical C) :
    canonicalNormalise (not (not C)) = C

/-- Wrapper recovering the originally-requested theorem shape.
Derived via canonicalNormalise_isCanonical + the canonical version. -/
theorem canonicalNormalise_double_not {n : Nat}
    (C : FormulaCircuit n) :
    canonicalNormalise (not (not C)) = canonicalNormalise C
```

The wrapper is what T4 consumes; the invariant is the proof
vehicle.  Workers should NOT attempt the unconditional local
involution shape g55 discovered to be false.

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

-- NEW after g55 audit: constant-negation reductions
theorem canonicalNormalise_not_const_true {n : Nat} :
    canonicalNormalise (not (const true) : FormulaCircuit n) = const false

theorem canonicalNormalise_not_const_false {n : Nat} :
    canonicalNormalise (not (const false) : FormulaCircuit n) = const true
```

Plus, optionally, an idempotence lemma:

```lean
theorem canonicalNormalise_idempotent {n : Nat} (c : FormulaCircuit n) :
    canonicalNormalise (canonicalNormalise c) = canonicalNormalise c
```

**Expected LOC (revised after g55 audit):** 150–280.  The
canonical-output invariant adds ~50 LOC for the `IsCanonical`
predicate definition, its preservation proofs across the structural
recursion, and the image-invariant double-not proof.  The
HARD-minimum reductions, the constant-negation pair, and the
invariant together are sufficient to land T4.

**Proof-strategy hints (synthesised from g55 audit recipe):**

1. Define `canonicalNormalise` structurally with local constructors
   ordered so that constants are normalised under NOT first:
   `not (const true) ↦ const false`, `not (const false) ↦ const true`,
   `not (not C) ↦ C` (after recursive normalisation of `C`).
2. Define `IsCanonical` to exclude `not (const _)` and `not (not _)`
   at the root, plus recursive clauses for `and`/`or`.
3. Prove `canonicalNormalise_isCanonical` by structural induction
   on `FormulaCircuit n`, case-splitting on whether sub-formulas
   match the local-reduction patterns.
4. Derive `canonicalNormalise_double_not_canonical` from the
   invariant directly.
5. Wrap to recover `canonicalNormalise_double_not` via
   `canonicalNormalise_isCanonical (canonicalNormalise C)` and the
   canonical version.
6. Factor `normaliseAnd` and `normaliseOr` into smaller helper
   functions (e.g. `normaliseAndStep`, `normaliseOrStep`) and prove
   their local lemmas by explicit constructor cases, avoiding broad
   `repeat' split` proofs over deeply nested generated matches.

**Critical scope rule:** `canonicalNormalise` MUST be a **structural,
syntactic** function on `FormulaCircuit n` — NO truth-table evaluation,
NO `Decidable`, NO Boolean-function representation as `Bitstring n →
Bool`.  If you find yourself needing to evaluate the formula on inputs
to decide what to do, you've crossed into V2-A.2 territory — STOP and
ship a failure report.

**Explicit forbidden definitions of `canonicalNormalise` (all kick
V2-A.1 over the cliff into V2-A.2 / semantic-quotient territory and
re-instate the natural-proof barrier):**

```lean
-- FORBIDDEN: argmin over equivalent formulas
def canonicalNormalise (C : FormulaCircuit n) : FormulaCircuit n :=
  (Finset.image id ...).argmin (fun D => D.size) ...

-- FORBIDDEN: truth-table reconstruction
def canonicalNormalise (C : FormulaCircuit n) : FormulaCircuit n :=
  ttFormula (FormulaCircuit.eval C)
  -- or any variant that round-trips through a Boolean function

-- FORBIDDEN: choice principle
def canonicalNormalise (C : FormulaCircuit n) : FormulaCircuit n :=
  Classical.choose (existence_of_canonical_form C)
```

These are V2-A.2's territory.  If any of them is your candidate
definition, STOP — that is the global-failure signal for T1, ship
the failure report with `Global` obstruction classification.

**Recommended lemma names** (the audit will check for these or
clearly-equivalent renamings):

```text
canonicalNormalise_eval
canonicalNormalise_size_le
canonicalNormalise_double_not
canonicalNormalise_or_self_not_self
canonicalNormalise_or_not_self_self
canonicalNormalise_and_self_not_self
canonicalNormalise_and_not_self_self
canonicalNormalise_and_const_true
canonicalNormalise_and_true_const
canonicalNormalise_or_const_false       -- OR-identity with const false
canonicalNormalise_or_false_const       -- symmetric
```

The HARD-minimum set is the first nine; the OR-identity pair is
strongly recommended for symmetry but not strictly required for T4.

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

## 10. Negative-pivot protocol (operator-side, NOT worker scope) — STALLED post-M1

**SEED PACK STATUS: STALLED.**  T1 retry track PAUSED.  T2 / Round
2 PAUSED.  Pause decision documented at
`audits/T1_retry_pause_post_M1.md` (commit added with the M1
operator review).

**Why STALLED (one-paragraph summary):** parallel meta-barrier
track fp3b3_4 M1 landed a candidate statement (worker `m1nova`,
PR #1241) showing that any structural normaliser satisfying the
HARD-minimum reductions in §3 T1 forces `canonicalNormalise
(seededPrefixAndFamily n) ≠ seededPrefixAndFamily n` for `n ≥ 1`,
collapsing V2-A's own non-vacuity witness to a formula with zero
OR + zero NOT gates.  This makes V2-A's mixed-gate clause reject
the normalised seeded witness at `n ≥ 2`, so the T2 theorem
`v2A_1_admits_seededPrefixAndWitness` is **structurally false**
under the published T1 spec.  The fp3b3_3 §T2 scope rule (lines
377-388) anticipates this failure mode but lists only two escapes
(refine the family — forbidden; refine T1 — kills V2-A.1's
purpose), both blocked.

Round 1 history below preserves the audit trail.

This seed pack is dispatched under the operator's "**positive with
readiness to pivot negative**" stance.  Workers always pursue the
positive goal (build V2-A.1 survivor) — but the dispatcher pre-stages
a negative-result pivot path so a structured failure becomes a
research artifact, not wasted compute.

**Round 1 attempt #1 (commit `7840ef4` / PR #1239):** worker
g55 attempted T1, surfaced an internal spec inconsistency on the
HARD-minimum lemma surface, shipped a structured failure
report classified as `Local`.  Audit at
`audits/T1_g55_operator_audit.md` countersigned `Local`, spec
patched, parallel fp3b3_4 M1 dispatch approved.

**Round 1 attempt #2 (commit `c6b63d7` / PR #1240):** worker
g55r1 attempted T1 retry with the canonical-output invariant
recipe.  Hit a different proof-engineering wall on local AND/OR
identity lemmas — fixable with the abstract-canonical-term
helper-lemma factoring recipe in `failures/T1_g55r1.md` §4.
Failure classified `Local`.

**Round 1 fp3b3_4 M1 (commit `8c45586` / PR #1241):** worker
m1nova shipped a meta-barrier candidate recommending PROCEED to
M2.  Operator review at
`../fp3b3_4_v2_a_normalise_meta_barrier/audits/M1_m1nova_operator_review.md`
verified m1nova's argument against trust-rooted Lean facts
(`NonVacuity.lean:24-40`, `ExcludesPrefixAnd.lean:29-43`) and
promoted M1.  Operator-level synthesis: the meta-barrier
observation is reachable **directly from the published T1 spec**
without M2 / M3 formalisation, making T1 retry track wasted
compute.  See
`audits/T1_retry_pause_post_M1.md` for the full pause decision.

**Next operator-side action:** dispatch fp3b3_4 M2 (Lean
formalisation of the meta-barrier theorem), see
`../fp3b3_4_v2_a_normalise_meta_barrier/WORKER_PROMPT_M2.md`.
M2 landing triggers: NOGO-000009 addition, fp3b3_3 archival,
V2-A.2 / V2-B / V2-D priority refresh.  M2 failure triggers:
re-audit operator-level argument, decide whether to (a) refine
class formalisation, (b) accept operator-level closure without
Lean theorem, or (c) re-open fp3b3_3 with revised non-vacuity
witness design.

**Pivot trigger (original, still in force for future re-dispatches
if fp3b3_3 ever re-opens under a redesigned T1/T2 spec):** T1
ships a structured failure report (Outcome B, §6 with `Global`
obstruction classification) AND independent review confirms the
obstruction is structural rather than implementation detail.

**Note on early opening of `fp3b3_4_*`:** the operator opened the
meta-barrier track ahead of a `Global` classification because the
first dispatch's spec inconsistency was a weak meta-signal that
made parallel exploration cheaper than a pure retry sequence.  This
**override is recorded** in the audit document, does not modify the
`Global`-trigger protocol for future dispatches, and does not
preempt the fp3b3_3 retry track — both tracks run in parallel.

**Pivot action (operator only):** open a successor seed pack
`fp3b3_4_v2_a_normalise_meta_barrier/` whose target is the Lean
theorem

```lean
theorem v2_a_syntactic_normalise_meta_barrier :
    ∀ (normalise : ∀ {n}, FormulaCircuit n → FormulaCircuit n),
      <some structural class predicate on normalise> →
      (∀ n, eval (normalise (rewritePrefixAndFamily n)) = eval (rewritePrefixAndFamily n))
      → ¬ <V2-A_predicate-style filter composed with normalise admits
           both seededPrefixAndWitness AND rejects rewritePrefixAndWitness>
```

i.e. a meta-theorem stating that any structural syntactic normaliser
in the relevant class CANNOT simultaneously preserve V2-A's
non-vacuity and resist NOGO-000008.  This would be a **fifth structural
barrier theorem**, joining
`pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean` and
`pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`
in the audit-route barrier suite.  The pivot would consume the T1
failure report as its starting point and re-dispatch as a fresh
research direction.

**Worker scope (this seed pack):** ignore the pivot — pursue Outcome A
(positive landing) or Outcome B (structured failure).  The pivot is
an operator decision based on whether the failure is local or global,
informed by independent review.  Workers do NOT pre-stage pivot
artifacts in this seed pack.

**Scientific value of either outcome:**

* Outcome A on T1+T2 (positive) → Round 2 opens.  V2-A.1 has measured
  Razborov-Rudich re-entry; a fresh `informal` candidate enters the
  registry pipeline.
* Outcome B on T1 (global) → operator pivots to `fp3b3_4_*`
  meta-barrier seed pack.  The negative result, if formalised,
  would be a stronger anti-evidence than NOGO-000008: it would close
  the **entire V2-A-with-structural-normalisation design space**, not
  just one candidate.

Either way, no compute is wasted.

**Pivot chain (operator-side, full):**

```
T1 global fail (structured failure report, Global classification)
   ↓
fp3b3_4_v2_a_normalise_meta_barrier seed pack opens
   ↓
meta-barrier theorem landed
   ↓
natural-proof risk review (because V2-A.2 trades non-extensionality
for full extensionality and re-enters Razborov-Rudich territory)
   ↓
fp3b3_5_v2_a_2_semantic_quotient seed pack opens (if and only if
the natural-proof review concludes the semantic quotient has a
defensible re-entry pattern, e.g. via partial-truth-table
restriction, not full extensionality)
```

Note: V2-A.2 (semantic-equivalence quotient) is NOT the automatic
next route after T1 global failure.  The intermediate meta-barrier
theorem must land first, and the natural-proof review must clear
V2-A.2, before fp3b3_5_* opens.  Skipping the review and dispatching
V2-A.2 directly would re-instate the Razborov-Rudich barrier that
V2-A's original design escaped — a regression, not a fix.

## 11. Closing note

> V2-A.1 is the **first attempted patch** of V2-A under the
> kernel-checked anti-evidence of NOGO-000008.  It targets exactly
> the syntactic redundancies the rewrite attack exploited, no
> wider.  If it lands, the V2-* design space has a successor with
> measured Razborov-Rudich re-entry — a clean intermediate point
> between "fully non-extensional but trivially defeatable" (V2-A)
> and "fully extensional but barrier-bound" (V2-A.2).  If it
> fails on T1's structural impossibility, that is itself a result:
> the audit predicate's escape from the barrier may be inseparable
> from its rewrite vulnerability, and `fp3b3_4_*` opens.

Round 1 cap: T1, T2 only.  Round 2 (T3, T4, T5) opens when T1 + T2
have landed.  Do not stage Round 2 artifacts in a Round 1 commit.
Do not stage `fp3b3_4_*` artifacts here either — that is an operator
decision after Round 1 outcome.
