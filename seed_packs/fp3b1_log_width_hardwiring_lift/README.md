# Seed pack `fp3b1_log_width_hardwiring_lift`

> **Track:** Research-A — parallel decomposition of FP-3b.2.
> **Parent:** `seed_packs/fp3b1_log_width_hardwiring/README.md` —
> the single-worker version of this goal.
> **Status:** OPEN — eligible for Pilot Wave 0 / Wave 1
> parallel-attack across 10 independent worker slots.
> **Method family:** `ac0_locality_support`.
> **Created:** v0.4.3 follow-up.

## 0. TL;DR

The repo already proves FP-2 (an `OverbroadUniformProvenance` route is
ex-falso, kernel-checked at
`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:155`).  The
candidate filter `FP3Attempt.InSupportFunctionalDiversity` was
proposed as the next step but `outputs/nogolog.jsonl::NOGO-000003`
records that **log-width truth-table hardwiring evades it**.  That
NoGoLog entry is `status = "needs_review"` because the
counterexample has not been kernel-checked.

The goal of this seed pack is to **lift `NOGO-000003` to
`status = "formalized"`** by producing a Lean theorem of the
shape

```lean
theorem logWidthAdversary_satisfies_diversity :
    FP3Attempt.InSupportFunctionalDiversity adversaryWitness
```

where `adversaryWitness` is an `InPpolyFormula` packaging of a
log-width / power-of-two-slice truth-table-shaped family.

This is a **negative breakthrough in the spirit of
Razborov–Rudich** — not "P ≠ NP", but "this entire class of
filters is provably insufficient, kernel-checked".  Any future
`ProvenanceFilter_v2` will have to clear this bar.

## 1. Why parallel-decompose, and why 10 slots

The existing single-worker seed pack
(`seed_packs/fp3b1_log_width_hardwiring/`) describes the work as
≈100–200 lines of Lean across five lemma groups.  Sequential
execution is slow; in parallel, the lemma groups fit naturally
into 10 worker slots with mostly-non-overlapping write surfaces:

* 5 **independent base lemmas** (Tier 1) — can start immediately.
* 3 **integration tasks** (Tier 2) — depend on Tier 1, but
  different slots can integrate via different decomposition
  strategies (compare which is cleaner before merging).
* 2 **diversity-conjunct proofs** (Tier 3) — depend on Tier 2.

Slot 11 — the final composition + ledger upgrade — is intentionally
a *single-worker* job that can only run after a sufficient set of
Tier 1–3 results are committed.  The remaining 10 slots fan out
work independently.

The **honest payoff structure**:

* If ≥ 1 worker per Tier completes its slot AND the composition
  goes through → `NOGO-000003` flips to `formalized`.  Real
  scientific artifact, repository commits.
* If any slot proves its goal **impossible** (e.g. the log-width
  family does not actually live inside `InPpolyFormula L` for the
  language `L = eval (family ·)` under the polyBound coercion) →
  even better.  That's a meta-NoGoLog entry: the FP-3b.2 program
  itself is structurally blocked, and we redirect to the next
  strategy.
* If neither — workers ship structured failure reports (see §6)
  and the next round picks up where they left off.  Failure is
  cheap, not a regression.

## 2. Goal (precise)

Produce a Lean term

```lean
def adversaryFamily   : ∀ n : Nat, FormulaCircuit n
def adversaryLanguage : Pnp3.ComplexityInterfaces.Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily n) x
def adversaryWitness  : Pnp3.ComplexityInterfaces.InPpolyFormula
                          adversaryLanguage

theorem logWidthAdversary_satisfies_diversity :
    Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt
      .InSupportFunctionalDiversity adversaryWitness
```

with **no `sorry` / `admit`** and `lake build PnP3` green.  The
existing FP-3b.1 placeholder
(`FP3Attempt.FP3b1.adversaryFamily := fun _ => const false`) has
the right *packaging* but the wrong *body*; the body must be
replaced.

## 3. Recommended sub-target decomposition (5 lemmas)

Each numbered sub-target below is independently verifiable.  A
slot "succeeds" when its Lean theorem compiles and is committed
to a designated path.

### T1 — Width-function helpers

Either path is acceptable:

* **T1.A (mathlib path):** lemmas about `Nat.log2` (or `Nat.log 2`):
  - `logWidth_le        : ∀ n, Nat.log2 (n+1) ≤ n`
  - `logWidth_unbounded : ∀ B, ∃ n, B < Nat.log2 (n+1)`
  - `logWidth_lt_self   : ∀ N, ∃ n, N ≤ n ∧ Nat.log2 (n+1) < n`
* **T1.B (hand-rolled path):** define `k_pow2 : Nat → Nat`
  (`t` if `n = 2^t`, else `0`), prove the same three properties
  for `k_pow2` instead of `Nat.log2`.  Useful as a fallback if
  T1.A's mathlib import dependencies turn out to be heavier than
  expected.

Both end states unblock T2.A (T1.A) or T2.B (T1.B) respectively.
Worker discretion: which path is cleaner.

### T2 — `(ttFormula f).size` upper bound

Theorem:

```lean
theorem ttFormula_size_le (k : Nat) (f : Bitstring k → Bool) :
    FormulaCircuit.size (ttFormula f) ≤ 6 * 2 ^ k
```

By induction on `k`.  Base `k = 0`: `ttFormula f = const (f …)`,
size = 1, bound = 6 ≥ 1.  Inductive step: each level adds a fixed
number of gates around two recursive calls, bounded by `6` by the
constructor count of `ttFormula`'s `(n+1)`-case.

### T3 — `FormulaCircuit.rename` size + support transport

Two lemmas:

```lean
theorem rename_size {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    FormulaCircuit.size (FormulaCircuit.rename σ c) =
      FormulaCircuit.size c
```

(direct structural induction; `rename` only changes the `input i`
constructor's argument).

```lean
theorem rename_support_card {m n : Nat} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (c : FormulaCircuit m) :
    (FormulaCircuit.support (FormulaCircuit.rename σ c)).card =
      (FormulaCircuit.support c).card
```

(via `Finset.image` and the injective-σ cardinality lemma).

### T4 — adversary family + InPpolyFormula packaging

Define

```lean
namespace Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1
namespace LogWidthAdversary

def widthFn (n : Nat) : Nat := …                    -- T1
def someBooleanFn (k : Nat) : Bitstring k → Bool := -- pick a fixed
  fun _ => true                                       -- non-trivial Bool fn
def adversaryFamily (n : Nat) : FormulaCircuit n :=
  if h : widthFn n ≤ n then
    FormulaCircuit.rename
      ⟨Fin.castLE h, …⟩
      (ttFormula (someBooleanFn (widthFn n)))
  else
    FormulaCircuit.const false

def adversaryLanguage : Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily n) x

def adversaryWitness : InPpolyFormula adversaryLanguage where
  family := adversaryFamily
  polyBound := fun n => 6 * (n + 1)
  polyBound_poly := …       -- T1 + arithmetic
  family_size_le := …       -- T1 + T2 + T3 (rename_size)
  correct := fun _ _ => rfl -- trivial by construction
```

The exact `widthFn` choice is at worker discretion; document the
choice in the slot's writeup.  `someBooleanFn` can be `fun _ => true`
or any fixed Boolean function — the diversity proof only needs
non-empty support, not a specific function.

**Important: `someBooleanFn := fun _ => true` makes `ttFormula
(someBooleanFn k) = const true`, which has support `∅` — so the
diversity proof fails.** Use a Boolean function whose `ttFormula`
has full support `Finset.univ`, e.g. `someBooleanFn k :=
fun x => x ⟨0, h⟩` (the first input bit) for `k ≥ 1`, with a
special case at `k = 0`.  Worker discretion to pick a clean
formulation.

### T5 — diversity conjuncts

Two theorems composing into the final goal:

```lean
theorem adversary_support_unbounded :
    ∀ B, ∃ n,
      B < (FormulaCircuit.support (adversaryFamily n)).card
-- Witness: pick n = 2 ^ (B + 1), use T1 + T3 (rename_support_card).

theorem adversary_support_below_n_io :
    ∀ N, ∃ n,
      N ≤ n ∧
      (FormulaCircuit.support (adversaryFamily n)).card < n
-- Witness: pick n = 2 ^ t for t ≥ 2, t ≥ N, support card = t < 2^t.
```

Compose into

```lean
theorem logWidthAdversary_satisfies_diversity :
    FP3Attempt.InSupportFunctionalDiversity adversaryWitness :=
  ⟨adversary_support_unbounded, adversary_support_below_n_io⟩
```

## 4. Slot assignment for 10 parallel workers

Each row = one worker slot.  Slots write to **disjoint files** to
avoid merge conflicts; the integration slot (S11) glues everything
together at the end.

| Slot | Sub-target | File path                                                                        | Output (theorem name)                              | Depends on |
| ---- | ---------- | -------------------------------------------------------------------------------- | -------------------------------------------------- | ---------- |
| S1   | T1.A       | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Width_NatLog2.lean`            | `logWidth_le`, `logWidth_unbounded`, `logWidth_lt_self` | —          |
| S2   | T1.B       | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Width_PowOfTwoSlice.lean`      | `k_pow2_le`, `k_pow2_unbounded`, `k_pow2_lt_self`  | —          |
| S3   | T2         | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/TTFormulaSizeBound.lean`       | `ttFormula_size_le`                                | —          |
| S4   | T3 (size)  | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/RenameSize.lean`               | `rename_size`                                      | —          |
| S5   | T3 (support) | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/RenameSupport.lean`          | `rename_support_card`                              | —          |
| S6   | T4 (variant A) | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Family_NatLog2.lean`       | `adversaryFamily_v_natlog2`, `adversaryWitness_v_natlog2` | S1, S3, S4, S5 |
| S7   | T4 (variant B) | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Family_PowOfTwoSlice.lean` | `adversaryFamily_v_pow2`, `adversaryWitness_v_pow2` | S2, S3, S4, S5 |
| S8   | T5 (unbounded) | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Diversity_Unbounded.lean`  | `adversary_support_unbounded` (against EITHER S6 or S7's family) | S6 or S7 |
| S9   | T5 (below-n) | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Diversity_BelowN.lean`       | `adversary_support_below_n_io` (against same family) | S6 or S7 |
| S10  | sanity     | `pnp3/Tests/AuditRoutes_LogWidthAdversary_Smoke.lean`                            | regression `#check`s of all of the above; `theorem logwidth_smoke_loaded : True := trivial` | runs concurrently with S1–S9 — uses `#check` so it can compile against the placeholder declarations and tighten as real ones land |

Final integration (NOT a parallel slot — single worker, after
S1..S9 stabilise):

| S11 | Composition + ledger flip | edits to existing
`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1`,
new `outputs/nogolog.jsonl` entry, `outputs/attempts.jsonl` entry,
`seed_packs/fp3b1_log_width_hardwiring/critic_report.md` | the final
`logWidthAdversary_satisfies_diversity` theorem | S6∨S7 + S8 + S9 |

The S6 vs S7 choice is decided AFTER both land — whichever has
the cleaner proof becomes the canonical body of FP3b1's
`adversaryFamily`.  The other goes into the pack as a "second
realization" footnote in the critic report.

## 5. Allowed scope — per slot

Each slot may add NEW files at the path listed in §4, and edit
ONLY:

* its own new file;
* `lakefile.lean` to wire its new file into the `Glob.one` list
  for `Magnification.AuditRoutes.LogWidthAdversary.<basename>`;
* `pnp3/Tests/AuditRoutes_LogWidthAdversary_Smoke.lean` (S10
  only).

The integration slot S11 may additionally edit:

* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` —
  ONLY the body of `FP3b1.adversaryFamily`, the `polyBound` /
  `family_size_le` proofs in `FP3b1.adversaryWitness`, and the
  added theorem `logWidthAdversary_satisfies_diversity`;
* `outputs/nogolog.jsonl` — append ONE entry that supersedes
  `NOGO-000003`;
* `outputs/attempts.jsonl` — append ONE attempt entry via
  `scripts/attempts_append.py`;
* `seed_packs/fp3b1_log_width_hardwiring/critic_report.md` and
  `seed_packs/fp3b1_log_width_hardwiring_lift/critic_report.md`
  — Critic reports per `spec/critic_protocol.md`.

## 6. Forbidden scope (all slots)

* Trust root — `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `pnp3/Magnification/LocalityProvider_Partial.lean`,
  `pnp3/Magnification/FinalResultMainline.lean`,
  `pnp3/Magnification/FinalResultAuditRoutes.lean`,
  any file declaring `ResearchGapWitness` /
  `NP_not_subset_PpolyDAG` / `P_ne_NP*` (Rule 0).
* Editing the existing `FP3Attempt.InSupportFunctionalDiversity`
  predicate — the adversary attacks the ALREADY-COMMITTED filter
  shape (Rule 1).
* `axiom`, `opaque`, `Fact`, typeclass payload (Rule 16).
* `sorry` / `admit` anywhere in committed code.
* Editing existing JSONL log entries (Rule 9 — corrections via
  `supersedes`).
* Promoting any guard in `spec/known_guards.toml` to
  `status = "accepted"`.
* Creating `pnp3/Candidates/<id>/` for this seed pack (audit-only
  routing, see `spec/critic_protocol.md` §7).
* Cross-slot writes — slot Sₖ writes only to its own §4 path.  If
  a slot needs a definition from another slot, it imports the
  module (no copy-paste).
* Any `gap_from_*` bridge or `SourceTheorem_*` (FP-4 territory).

## 7. Per-slot success criterion

A slot Sₖ is **complete** when:

1. The theorem listed in §4 for Sₖ compiles in the target file
   path with no `sorry`.
2. `lake build PnP3` succeeds with the file wired into
   `lakefile.lean`.
3. `scripts/check.sh` 17/17 + sub-steps green (no regression).
4. The slot's PR description names the theorem and its file:line.

Note: a slot is INTENTIONALLY allowed to ship a NARROWER theorem
than §3 specifies, as long as the integration slot can still
close `logWidthAdversary_satisfies_diversity` from the union of
shipped slot outputs.  Worker judgement.

## 8. Per-slot failure criterion (structured)

If a slot's worker concludes the sub-target **cannot be discharged
within the allowed scope**, the worker commits a structured
failure report at

```
seed_packs/fp3b1_log_width_hardwiring_lift/
  failures/S<k>_<short-name>.md
```

with the following sections (kept brief):

1. **What was attempted.**  Code path tried; mathlib lemmas
   considered.
2. **Where it broke.**  Specific definitional or proof obstruction
   — e.g. "`FormulaCircuit.support` is not actually defined; only
   `support`-via-`semantics` is, and that's an `opaque`".
3. **Whether the obstruction is local or global.**  Local = a
   missing helper lemma.  Global = the FP-3b.2 *target* is
   structurally unreachable from the current Lean state.  This
   distinction is the whole point — a global obstruction is itself
   a research result (it argues against the FP-N program direction).
4. **What an integration slot would need to know.**  E.g. "S6 must
   pick T1.B (S2's path) because T1.A relies on a mathlib lemma
   not yet imported in this build's mathlib pin."

A failure report is itself a PR-mergeable artifact; the worker
appends an `outputs/attempts.jsonl` entry with
`verifier_status = PASS_SHAPE_ONLY` and
`critic_status = "not_run"`.  No NoGoLog entry until S11 reviews.

## 9. Integration (S11) acceptance criterion

S11 is **complete** when ALL of:

1. `lake build PnP3 Pnp4` is green.
2. `scripts/check.sh` 17/17 + sub-steps green.
3. `scripts/run_smoke_probes.sh` 8/8 green.
4. The theorem `logWidthAdversary_satisfies_diversity` (or an
   equivalently-named theorem with the same statement) is
   committed and proves the diversity property without `sorry`.
5. A regression test `#check`'s the theorem at
   `pnp3/Tests/FixedParams_Probe_NoGo.lean` (or the new
   `AuditRoutes_LogWidthAdversary_Smoke.lean`).
6. `outputs/nogolog.jsonl` has a NEW entry (next available
   `NOGO-NNNNNN`) with `supersedes = "NOGO-000003"`,
   `status = "formalized"`, `failure_class = "hardwiring"`,
   non-null `formal_witness` pointing at the new theorem's
   file:line.
7. `outputs/attempts.jsonl` has a new line with
   `seed_pack_id = "fp3b1_log_width_hardwiring_lift"`,
   `verifier_status = PASS_SHAPE_ONLY`,
   `critic_status` populated based on the Critic report at §10.
8. `seed_packs/fp3b1_log_width_hardwiring_lift/critic_report.md`
   exists and follows `spec/critic_protocol.md` §1–3.
9. `spec/known_guards.toml::guards.ProvenanceFilter_v1` is
   UNCHANGED — still `status = "informal"`, `formal_name = ""`.
10. No `pnp3/Candidates/` directory created.
11. No bridge / SourceTheorem / final endpoint touched (Rule 0).

## 10. Critic angles (six attacks per `spec/critic_protocol.md`)

The Critic report S11 ships should explicitly address:

* **Hidden-payload attack.**  Does any of S1..S9's lemmas use
  `class`/`instance`/`Fact`/`opaque`/typeclass payload to smuggle
  the diversity property?  Expected: no.
* **Tautology attack.**  Is `adversaryWitness` somehow definitionally
  excluded from `InPpolyFormula L` — e.g. is the `correct` field
  vacuous because `polyBound n = 0`?  Expected: no, `polyBound n
  = 6·(n+1) > 0`.
* **Known-guards factorisation.**  Does the diversity proof
  factor through `HardwiringGuard`?  Expected: yes — the adversary
  IS a hardwiring witness, and the diversity proof exposes that
  the existing guard is too coarse to exclude it.
* **Bridge non-vacuity.**  N/A — no bridge in scope.
* **Audit-route quarantine.**  All new files live under
  `pnp3/Magnification/AuditRoutes/` or `pnp3/Tests/`.  No edits to
  `Magnification/UnconditionalResearchGap.lean`.
* **Reproducibility.**  All proofs `rfl` / structural induction;
  no `decide` on unbounded numerics.

## 11. What this seed pack is NOT trying to do

* Propose `ProvenanceFilter_v2`.  That is FP-3b.3, a separate seed
  pack.  The right time to start it is AFTER `NOGO-000003` is
  formalized.
* Construct any `gap_from_*` bridge (FP-4 territory).
* Edit the trust root.
* Promote `ProvenanceFilter_v1` from informal to accepted.
* Move Pilot Wave 1 from technical-readiness GO to activation.
  Activation requires cycles in
  `outputs/attempts.jsonl`, but THIS seed pack only contributes
  one or two attempt entries; it does NOT by itself satisfy
  `min_clean_cycles = 30`.

## 12. References

* `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.
* Parent: `seed_packs/fp3b1_log_width_hardwiring/README.md` —
  single-worker version of this same goal.
* `outputs/nogolog.jsonl::NOGO-000003` — the open caveat (the
  `notes` field has the construction sketch).
* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1` —
  the placeholder skeleton this seed pack replaces.
* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean
  ::InSupportFunctionalDiversity` (line 231) — the candidate
  filter under attack.
* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean
  ::InSupportFunctionalDiversity_excludes_uniformPolyBound`
  (line 265) — companion theorem; reading it tells you the
  shape of arguments the diversity proof needs to clear.
* `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` —
  pre-existing infrastructure: `FormulaCircuit.rename` (line 107),
  `FormulaCircuit.eval_rename` (line 115), `ttFormula` (line 130).
* `spec/critic_protocol.md` — Critic report format.
* `seed_packs/PILOT_WAVE_0_PROTOCOL.md` — the worker cycle each
  slot follows.

## 13. Closing note

> The repository's strength is the verifier, not the Generator.
> This seed pack reflects that: it asks workers to *prove the
> filter dies*, not to *invent a better filter*.  The
> Razborov–Rudich analogy is intentional — a kernel-checked
> obstruction is more durable than yet another candidate.

Pilot Wave 1 cap is 20 workers.  This seed pack's S1..S10 fits
inside that cap with room to spare.  Slot S11 runs solo after a
human Reviewer signs off on the union of S1..S9 outputs.
