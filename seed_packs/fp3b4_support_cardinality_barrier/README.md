# Seed pack `fp3b4_support_cardinality_barrier`

> **Track:** Research-A — meta-barrier theorem.
> **Parent dependency:** `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`
> shipped `NOGO-000006` (concrete obstruction).
> **Status:** OPEN — eligible for Pilot Wave 1 parallel attack.
> **Method family:** `ac0_locality_support`.
> **Priority:** **highest** — must ship before `fp3b3` Phase 2 to
> sharpen v2 design space.

## 0. TL;DR

`NOGO-000006` (kernel-checked at
`pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean:101`)
is a CONCRETE obstruction: it exhibits a specific family
(`adversaryWitness_v_arbpayload`) that satisfies the FP-3 candidate
filter `InSupportFunctionalDiversity`.

This seed pack lifts that to a **meta-barrier theorem**:

> Any filter `Π : InPpolyFormula L → Prop` that depends ONLY on the
> support cardinality function `n ↦ (support (w.family n)).card` —
> regardless of formula shape, polyBound shape, gate types, or
> language — admits a hardwiring family if it admits any honest
> family with sublinear support.

The result formally **rules out an entire class of v2 filter
candidates** (those that look only at support cardinality) before
`fp3b3` workers spend time designing them.  After this lands,
`fp3b3` v2 candidates have a kernel-checked precondition: "must
NOT be support-cardinality-only" — sharper search space.

This is a **negative breakthrough in the spirit of Razborov–Rudich**,
locally scoped: a fourth structural barrier theorem in
`pnp3/Magnification/AuditRoutes/`, complementary to the existing
`pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`.

## 1. Why this strengthens NOGO-000006

`NOGO-000006`: there exists ONE family that satisfies the filter.
Single counterexample.

`fp3b4` target: **any** support-cardinality-only filter that admits
a sublinear-support honest witness ALSO admits a hardwiring witness
with the same support function.  Universal claim.

Concretely: after `fp3b4` lands, any v2 filter `Π_v2` proposed in
`fp3b3` that satisfies "Π_v2 is support-cardinality-only AND
admits parity" is **automatically dead** — by the barrier theorem,
it admits a hardwiring twin, contradicting "v2 must exclude
hardwiring."

This is the durable artifact `fp3b3` workers cannot bypass.

## 2. Goal (precise)

Produce three Lean terms plus a headline theorem, no
`sorry`/`admit`, no `axiom`:

```lean
def canonicalHardwiringFamily (s : Nat → Nat) (hs : ∀ n, s n ≤ n)
    : ∀ n, FormulaCircuit n
def canonicalHardwiringWitness (s : Nat → Nat) (hs : ∀ n, s n ≤ n)
    : InPpolyFormula (canonicalHardwiringLanguage s hs)

def IsSupportCardinalityOnly
    (Π : ∀ {L : Language}, InPpolyFormula L → Prop) : Prop

theorem support_cardinality_barrier
    (Π : ∀ {L : Language}, InPpolyFormula L → Prop)
    (hInvariant : IsSupportCardinalityOnly Π)
    {L_honest : Language}
    (w_honest : InPpolyFormula L_honest)
    (hHonest : Π w_honest)
    (hSubLinear : ∀ n, (FormulaCircuit.support (w_honest.family n)).card ≤ n) :
    Π (canonicalHardwiringWitness
        (fun n => (FormulaCircuit.support (w_honest.family n)).card)
        hSubLinear)
```

## 3. Slot decomposition (6 slots, parallel-attackable)

Disjoint file paths under
`pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/`.

### T1 — canonical hardwiring family + language

**File:** `SupportCardinalityBarrier/CanonicalHardwiringFamily.lean`

```lean
def canonicalHardwiringFamily
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) (n : Nat) : FormulaCircuit n :=
  prefixAnd n (s n) (hs n)

def canonicalHardwiringLanguage
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) : Language :=
  fun n x => FormulaCircuit.eval (canonicalHardwiringFamily s hs n) x
```

Reuse `prefixAnd` from
`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd`
(landed in fp3b1 Family_NatLog2.lean).  This slot is **mostly
import + parameterization**; expected ≤ 25 LOC.

### T2 — support cardinality is exactly s

**File:** `SupportCardinalityBarrier/CanonicalHardwiringSupport.lean`

```lean
theorem canonicalHardwiringFamily_support_card
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) (n : Nat) :
    (FormulaCircuit.support (canonicalHardwiringFamily s hs n)).card = s n
```

Direct corollary of fp3b1's `prefixAnd_support_card`
(`Composition.lean:79–98`).  Expected ≤ 15 LOC, possibly a one-line
proof.

### T3 — InPpolyFormula packaging

**File:** `SupportCardinalityBarrier/CanonicalHardwiringWitness.lean`

```lean
def canonicalHardwiringWitness
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) :
    InPpolyFormula (canonicalHardwiringLanguage s hs) where
  family := canonicalHardwiringFamily s hs
  polyBound := fun n => 2 * n + 1
  polyBound_poly := ⟨2, ?_⟩      -- via 2*n+1 ≤ n^2 + 2 ≤ n^2 + 2
  family_size_le := fun n => ?_  -- via prefixAnd_size + arithmetic
  correct := fun _ _ => rfl
```

Generalization of fp3b1's `adversaryWitness_v_natlog2`
(Family_NatLog2.lean:104–109) from `s = logWidthNat` to arbitrary
`s : Nat → Nat` with `s n ≤ n`.  Expected ≤ 50 LOC.

### T4 — IsSupportCardinalityOnly predicate

**File:** `SupportCardinalityBarrier/SupportCardinalityOnly.lean`

```lean
def IsSupportCardinalityOnly
    (Π : ∀ {L : Language}, InPpolyFormula L → Prop) : Prop :=
  ∀ {L₁ L₂ : Language} (w₁ : InPpolyFormula L₁) (w₂ : InPpolyFormula L₂),
    (∀ n, (FormulaCircuit.support (w₁.family n)).card =
          (FormulaCircuit.support (w₂.family n)).card)
    → (Π w₁ ↔ Π w₂)
```

This is the **weak invariance** definition: filter doesn't
distinguish witnesses with the same support cardinality function.
Worker discretion: alternative formulations (strict version, or
strong version that includes polyBound) are acceptable IF justified
in the docstring AND if the barrier theorem (T5) still goes
through.  Expected ≤ 25 LOC including docstring.

### T5 — barrier theorem

**File:** `SupportCardinalityBarrier/Barrier.lean`

```lean
theorem support_cardinality_barrier
    (Π : ∀ {L : Language}, InPpolyFormula L → Prop)
    (hInvariant : IsSupportCardinalityOnly Π)
    {L_honest : Language}
    (w_honest : InPpolyFormula L_honest)
    (hHonest : Π w_honest)
    (hSubLinear : ∀ n, (FormulaCircuit.support (w_honest.family n)).card ≤ n) :
    Π (canonicalHardwiringWitness
        (fun n => (FormulaCircuit.support (w_honest.family n)).card)
        hSubLinear) := by
  apply (hInvariant w_honest _).mp hHonest
  intro n
  rw [canonicalHardwiringFamily_support_card]
```

Three-line proof: pull s = w_honest's support function, build
canonical hardwiring witness, apply hInvariant.  Expected ≤ 30 LOC
including docstring.

### T6 — application + ledger upgrade

**File:** `SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean`

Two artifacts:

(i) Sanity smoke — show that `InSupportFunctionalDiversity` is
support-cardinality-only:

```lean
theorem inSupportFunctionalDiversity_is_support_cardinality_only :
    IsSupportCardinalityOnly @FP3Attempt.InSupportFunctionalDiversity
```

This is mechanical because `InSupportFunctionalDiversity` is
literally defined in terms of support cardinality (FixedParamsProbe.lean:231).

(ii) Apply the barrier to derive a more general version of
NOGO-000006:

```lean
theorem any_honest_sublinear_support_witness_has_hardwiring_twin
    {L : Language}
    (w_honest : InPpolyFormula L)
    (hHonest : FP3Attempt.InSupportFunctionalDiversity w_honest)
    (hSubLinear : ∀ n, (FormulaCircuit.support (w_honest.family n)).card ≤ n) :
    FP3Attempt.InSupportFunctionalDiversity
      (canonicalHardwiringWitness
        (fun n => (FormulaCircuit.support (w_honest.family n)).card)
        hSubLinear)
```

Append `NOGO-000007` to `outputs/nogolog.jsonl` with:
* `status = "formalized"`,
* `supersedes = null` (NOGO-000007 generalizes but does not
  invalidate NOGO-000006; both remain valid Lean theorems),
* `failure_class = "hardwiring"`,
* `formal_witness = "<path>:<line>"` of the barrier theorem,
* notes referencing NOGO-000006 as the concrete instance and
  NOGO-000007 as the meta-version.

Append one `outputs/attempts.jsonl` entry with
`seed_pack_id = "fp3b4_support_cardinality_barrier"`,
`verifier_status = "PASS_SHAPE_ONLY"`, `critic_status = "pass"`,
referencing
`seed_packs/fp3b4_support_cardinality_barrier/critic_report.md`
(six-attack report).

Expected ≤ 80 LOC for the Lean side plus the ledger writes.

## 4. Allowed / forbidden scope

### Allowed (per slot)

* New files under
  `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/`.
* `lakefile.lean` — append new modules to the existing
  `Glob.one ...` list.
* Optional smoke at
  `pnp3/Tests/AuditRoutes_SupportCardinalityBarrier_Smoke.lean`.
* T6 only: `outputs/nogolog.jsonl` (append `NOGO-000007`),
  `outputs/attempts.jsonl` (append one entry),
  `seed_packs/fp3b4_support_cardinality_barrier/critic_report.md`.

### Forbidden (HARD)

* Trust root: `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `pnp3/Magnification/LocalityProvider_Partial.lean`,
  `pnp3/Magnification/FinalResultMainline.lean`,
  `pnp3/Magnification/FinalResultAuditRoutes.lean`,
  any file declaring `ResearchGapWitness` /
  `NP_not_subset_PpolyDAG` / `P_ne_NP*`.
* Editing `FP3Attempt.InSupportFunctionalDiversity` — attack the
  ALREADY-COMMITTED filter shape.
* Editing fp3b1's `FP3b1.adversaryFamily/Witness` placeholder or
  fp3b1/fp3b2/Composition.lean theorem bodies — generalize, don't
  rewrite.
* Editing existing JSONL log entries (Rule 9 — append-only).
* `axiom`, `opaque`, `Fact`, typeclass-payload (Rule 16).
* `sorry` / `admit` anywhere in committed Lean code (Rule 1).
* `pnp3/Candidates/<id>/` creation (audit-only routing).
* `gap_from_*`, `SourceTheorem_*` (FP-4 territory; gated on v2).
* `ProvenanceFilter_v1` promotion to `accepted`.
* `ProvenanceFilter_v2` design (that's `fp3b3`).
* Wave 1 activation by force.

## 5. Slot acceptance criteria

A slot Sₖ is **complete** when:

1. The Lean theorem(s) listed for Sₖ compile in the target file
   path with no `sorry` / `admit`.
2. `lake build PnP3 Pnp4` green.
3. `./scripts/check.sh` 17/17 + sub-steps green.
4. PR description names each new theorem and its file:line.

T6 additionally requires:

5. `outputs/nogolog.jsonl` validated with the new `NOGO-000007`
   entry, `status="formalized"`, non-null `formal_witness`.
6. `outputs/attempts.jsonl` has the new audit entry referencing a
   non-template six-attack Critic report.
7. `seed_packs/fp3b4_support_cardinality_barrier/critic_report.md`
   exists and follows `spec/critic_protocol.md` §1–3.

## 6. Per-slot failure criterion

If a slot's worker concludes the sub-target is **structurally
unreachable within the allowed scope**, ship a markdown failure
report at

```
seed_packs/fp3b4_support_cardinality_barrier/failures/T<k>_<short>.md
```

with the four sections:

1. What was attempted.
2. Where it broke (Lean error message verbatim).
3. Local vs global obstruction.
4. What the integrator must know.

A `global` obstruction here is itself a result: the support-
cardinality-only barrier may be **false** in a stronger sense (e.g.,
the construction `prefixAnd` doesn't actually live in
`InPpolyFormula L` for arbitrary `L`).  Document carefully — this
would be a meta-meta finding.

## 7. Critic angles (six attacks for T6 critic_report.md)

* **Hidden-payload attack.**  Does the barrier theorem use
  `Classical.choice` of a non-trivial existential, smuggling
  payload via `class`/`instance`/`Fact`/`opaque`?  Expected: no.
  Proof is constructive (specific `canonicalHardwiringWitness`
  exhibited).
* **Hardwiring attack.**  This IS the intended construction —
  intentional `break found`-style result, but the report should
  classify as `no break found` per the same logic as fp3b2's
  Critic report (the obstruction is the result, not a defect).
* **KnownGuards-factorization attack.**  Same logic as fp3b2.
* **Barrier audit (natural-proof / relativization / algebrization).**
  Expected `attack not applicable` — the theorem is a Lean-internal
  meta-result about FP-N filter shapes, not a complexity-class
  separation.
* **Collapse-not-contradiction audit.**  Verify that the theorem
  doesn't collapse to a vacuous statement.  Specifically: confirm
  the non-vacuity hypothesis (`hHonest : Π w_honest`) is non-
  removable — without it, the theorem is trivially true.
* **Vacuity / source-theorem rephrasing audit.**  Verify
  NOGO-000007 doesn't rephrase NOGO-000006 — it generalizes.
  Concrete check: NOGO-000007's conclusion quantifies over Π,
  NOGO-000006's doesn't.

## 8. What this seed pack does NOT do

* Design `ProvenanceFilter_v2` (that's `fp3b3`).
* Construct `gap_from_*` bridge (FP-4 territory).
* Edit the trust root (Rule 0).
* Promote any guard.
* Move Pilot Wave 1 from technical readiness to activation.
* Produce a fourth classical barrier theorem at the level of
  Razborov-Rudich (`pnp3/Barrier/NaturalProofs.lean`) — `fp3b4`'s
  barrier is local to the FP-N filter design space, not the full
  P-vs-NP barrier landscape.

## 9. Cross-references

* Concrete predecessor: `outputs/nogolog.jsonl::NOGO-000006`.
* Existing classical barriers (parallel level, but global):
  `pnp3/Barrier/{Relativization,NaturalProofs,Algebrization}.lean`.
* `prefixAnd` + `prefixAnd_support_card` building blocks:
  `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1.LogWidthAdversary.prefixAnd`,
  `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean::prefixAnd_support_card`.
* `InSupportFunctionalDiversity` filter under attack:
  `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:231`.
* `spec/critic_protocol.md` — Critic report format.
* `seed_packs/PILOT_WAVE_0_PROTOCOL.md` — worker cycle.

## 10. Closing note

> The repository's strength is the verifier, not the Generator.
> This seed pack continues that pattern: instead of inventing a
> stronger filter, we strengthen the **meta-obstruction** so any
> proposed v2 filter has a kernel-checked invariance bar to clear.
> After T6 lands, `fp3b3` workers MUST exhibit non-support-
> cardinality dependence in their proposals, or face
> automatic rejection by `support_cardinality_barrier`.

Pilot Wave 1 cap is 20 workers; this seed pack's 6 slots fit
comfortably alongside `fp3b3`'s 4 directions.  T6 integration is
gated on T1..T5 stabilising; do not start T6 until at least one
viable path through T1..T5 lands.
