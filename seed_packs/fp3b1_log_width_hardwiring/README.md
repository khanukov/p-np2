# Seed pack `fp3b1_log_width_hardwiring`

> **Track:** Research-A (FixedParams Probe research thread).
> **Status:** open.
> **Method family:** `ac0_locality_support`.
> **Created:** FP-3b.0 (commit `80f0f72` introduced
> `NOGO-000003 needs_review`; this seed pack is the FP-3b.1 follow-up
> that aims to upgrade NOGO-000003 to `formalized`).

## 1. Goal

Construct a Lean-level adversary that satisfies the audit-only
candidate filter

```lean
Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.InSupportFunctionalDiversity
```

while internally being a polynomial-size **truth-table-shaped**
hardwired family on a sublinear / log-width window of variables.

If the construction succeeds, the candidate filter
`InSupportFunctionalDiversity` is dead as a provenance filter (it
admits exactly the hardwiring shapes it was meant to exclude), and
`outputs/nogolog.jsonl::NOGO-000003` is upgraded from
`status = "needs_review"` to `status = "formalized"` (or superseded
by `NOGO-000004 status = "formalized"`).

This seed pack does **NOT** start FP-4.  It does **NOT** propose a
stronger filter.  It does **NOT** promote
`spec/known_guards.toml::guards.ProvenanceFilter_v1` to `accepted`.

## 2. Allowed scope

The worker MAY add or modify:

* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` — extend
  the `FP3Attempt` namespace with the new adversary's data and
  proofs.  Use a sub-namespace `FP3b1` inside `FP3Attempt` to keep
  the FP-3-actual surface stable.
* `pnp3/Tests/FixedParams_Probe_NoGo.lean` — append regression
  smoke tests for the new artifacts.
* `outputs/nogolog.jsonl` — append a NEW entry (`NOGO-000004`?)
  with `supersedes = "NOGO-000003"` and `status = "formalized"`,
  including a `formal_witness` `path:line` pointer to the new
  Lean theorem.
* `outputs/attempts.jsonl` — append exactly one
  `AttemptLedgerEntry` line via `scripts/attempts_append.py`.
* `seed_packs/fp3b1_log_width_hardwiring/critic_report.md` — file a
  six-attack Critic report per `spec/critic_protocol.md` against
  the new adversary's role as a counterexample (e.g. "is the
  adversary itself hidden-payload?  is its attempted application a
  known-guards factorization?").
* `FixedParams_Probe.md` — flip the §FP-3-actual classification
  block from "under-investigation / C-shaped but blocked" to
  "Outcome A — support-cardinality-only filter dead via log-width
  hardwiring".

## 3. Forbidden scope

The worker MAY NOT:

* edit `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `pnp3/Magnification/LocalityProvider_Partial.lean`,
  `pnp3/Magnification/FinalResultMainline.lean`,
  `pnp3/Magnification/FinalResultAuditRoutes.lean`,
  or any file declaring `ResearchGapWitness` /
  `NP_not_subset_PpolyDAG` / `P_ne_NP*`;
* edit the existing `FP3Attempt.InSupportFunctionalDiversity`
  definition — the new adversary works against the
  ALREADY-COMMITTED filter shape;
* introduce `axiom`, `opaque`, `Fact`, typeclass payload, or
  `sorry`/`admit` anywhere in committed code (Rule 16, Rule 1);
* edit existing JSONL log entries;
* promote any guard in `spec/known_guards.toml` to
  `status = "accepted"`;
* create `pnp3/Candidates/<id>/` for this seed pack (audit-only
  routing — see `spec/critic_protocol.md` §7).

## 4. CRITICAL packaging correction

The original FP-3b.1 sketch in `outputs/nogolog.jsonl::NOGO-000003`
notes mentioned packaging into

```lean
InPpolyFormula (fun _ _ => false)
```

That packaging is **incorrect** for an arbitrary truth-table
hardwired family: the `InPpolyFormula` record's `correct` field

```lean
correct : ∀ n (x : Bitstring n), FormulaCircuit.eval (family n) x = L n x
```

would not hold for `L = const false` unless the family also
evaluates to `false` everywhere — which is NOT the case for an
adversary that hardwires arbitrary Boolean functions on a
log-width window.

**Use this packaging instead:**

```lean
namespace FP3Attempt.FP3b1

/-- Audit-only adversarial family of formulas.  The width window
    `k(n)` is sublinear (e.g. ⌈log₂(n+1)⌉ or, for the simpler
    power-of-two-slice variant, the function that returns `t` at
    `n = 2^t` and `0` elsewhere). -/
def adversaryFamily : ∀ n, FormulaCircuit n := ...

/-- The language is **defined to be** what the family computes.
    This makes the `correct` field trivially `rfl`. -/
def adversaryLanguage : Pnp3.ComplexityInterfaces.Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily n) x

def adversaryWitness :
    Pnp3.ComplexityInterfaces.InPpolyFormula adversaryLanguage where
  family := adversaryFamily
  polyBound := <fill in>
  polyBound_poly := <fill in>
  family_size_le := <fill in>
  correct := by intro n x; rfl

end FP3Attempt.FP3b1
```

The `correct` field becomes `by intro n x; rfl` because the
language is *defined* to match the family's `eval`.  This sidesteps
the need to choose a fixed Boolean function (parity / XOR / etc.)
and prove a separate correctness lemma.

## 5. Simpler power-of-two variant

If the full `Nat.log 2 (n+1)` machinery proves too heavy (it
requires lemmas about `Nat.log`, `Nat.pow`, and a bound
`Nat.log 2 (n+1) ≤ n`), use the **power-of-two-slice variant**:

* width function `k_pow2 : Nat → Nat` defined by `k_pow2 n := t`
  if `n = 2^t` for some `t`, else `k_pow2 n := 0`;
* family `family n := if h : n = 2^t (some t) then rename (Fin.castLE _) (ttFormula (arbitrary at width t)) else const false`;
* support cardinality at `n = 2^t` is `t`, at other `n` it is `0`;
* unboundedness: take `n = 2^(B+1)`, support card is `B+1 > B`;
* infinitely-often-non-saturated: take `n = 2^t ≥ N` with `t ≥ 2`,
  then support card `= t < 2^t = n`;
* size at `n = 2^t` is `O(2^t · t) = O(n · log₂ n)`, polynomially
  bounded by `n²`.

The `if h : n = 2^t` shape requires a decidability instance, which
Mathlib provides via `Nat.isPowerOfTwo` (or can be hand-rolled).
The case where `n` is not a power of two contributes `const false`
to the family, which has empty support — fine for the
infinitely-often-non-saturated conjunct.

## 6. Required lemmas (rough estimate)

1. **Width-function lemmas.** Either `Nat.log` helpers or
   `Nat.isPowerOfTwo` decidability + `pow2_log` round-trip.
   Estimate: 20–40 lines.
2. **`(ttFormula f).size ≤ 6 · 2^k`** — by induction on `k`.
   Estimate: 15–25 lines.
3. **`FormulaCircuit.rename` preserves size; transports support
   along an injective `σ` with cardinality preservation.**
   Estimate: 30–50 lines.
4. **`InPpolyFormula adversaryLanguage` packaging.** Estimate:
   20–40 lines.
5. **Diversity-witness theorem.**
   `theorem adversary_satisfies_diversity :
        FP3Attempt.InSupportFunctionalDiversity adversaryWitness`.
   Estimate: 20–40 lines.

Total estimate: 100–200 lines of Lean.  No `sorry`.

## 7. Acceptance criteria

The seed pack is COMPLETE when ALL of:

1. `lake build PnP3 Pnp4` is green.
2. `scripts/check.sh` is 17/17 green.
3. `scripts/run_smoke_probes.sh` is 8/8 green.
4. The new theorem `adversary_satisfies_diversity` (or equivalent)
   is committed and proves the diversity property without `sorry`.
5. A new regression test exists in
   `pnp3/Tests/FixedParams_Probe_NoGo.lean`.
6. `outputs/nogolog.jsonl` has either
   (a) an upgraded entry that supersedes `NOGO-000003` with
       `status = "formalized"` and a non-null `formal_witness`, or
   (b) `NOGO-000003` re-classified via a new entry with
       `failure_class` accurately describing the formalised
       counterexample.
7. `outputs/attempts.jsonl` has a new line with
   `seed_pack_id = "fp3b1_log_width_hardwiring"`,
   `verifier_status = PASS_SHAPE_ONLY` (this is audit-only routing,
   not a candidate package),
   and `critic_status` populated based on the Critic report.
8. `seed_packs/fp3b1_log_width_hardwiring/critic_report.md` exists
   and follows `spec/critic_protocol.md` §1–3.
9. `FixedParams_Probe.md` §FP-3-actual block is updated to reflect
   the formalised log-width-hardwiring attack.
10. `spec/known_guards.toml::guards.ProvenanceFilter_v1` is
    UNCHANGED — still `status = "informal"`,
    `formal_name = ""`.
11. No `pnp3/Candidates/` directory is created.
12. No bridge, no SourceTheorem, no final endpoint.

## 8. Out of scope (by design)

* Proposing a stronger `ProvenanceFilter_v2` that excludes
  log-width hardwiring — that is **FP-3b.2**, NOT this seed pack.
* Constructing any `gap_from_*` bridge — that is FP-4.
* Editing the trust root — Rule 0.
* Extending `pnp3/Magnification/UnconditionalResearchGap.lean` —
  Rule 0.
* Touching `ResearchGapWitness` — Rule 0.

## 9. References

* `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 5, 9, 12, 16.
* `FixedParams_Probe.md` §FP-3 actual / §FP-3b.0 / §8.7.
* `outputs/nogolog.jsonl::NOGO-000003` — the open caveat.
* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3Attempt`
  — the candidate filter under attack.
* `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean::ttFormula`
  / `::FormulaCircuit.rename` — pre-existing infrastructure to
  build the adversary.
* `spec/critic_protocol.md` — required Critic report format for
  the seed pack's deliverable.
