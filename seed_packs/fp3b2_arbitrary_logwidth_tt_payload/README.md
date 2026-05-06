# Seed pack `fp3b2_arbitrary_logwidth_tt_payload`

> **Track:** Research-A — strengthening of FP-3b.2.
> **Parent:** `seed_packs/fp3b1_log_width_hardwiring_lift/README.md`
> (closed via NOGO-000004; scope-corrected by NOGO-000005).
> **Status:** OPEN — eligible for Pilot Wave 1 parallel attack.
> **Method family:** `ac0_locality_support`.
> **Created:** v0.4.3-followup post-review scope correction.

## 0. TL;DR

NOGO-000004 (the kernel-checked obstruction shipped at
`pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean:208`)
formalises only the **prefix-AND specialisation** of the original
NOGO-000003 sketch:

```text
prefixAnd n (Nat.log2 (n+1)) _   ⊨   InSupportFunctionalDiversity
```

The original sketch was stronger: it asked for **arbitrary
all-essential** Boolean functions `f_n : Bitstring k(n) → Bool`
on a log-width window `k(n) = Θ(log n)`, packaged via

```lean
FormulaCircuit.rename σ_n (ttFormula f_n) : FormulaCircuit n
```

with `σ_n : Fin (k n) → Fin n` an injective embedding.

This seed pack is the formal lift of that strengthening.  Success
upgrades the NoGoLog chain to **NOGO-000006** (status="formalized",
supersedes="NOGO-000005").  Failure (or partial completion)
records a structured failure report and leaves the chain at
NOGO-000005.

This seed pack is the **strict prerequisite** for designing
`ProvenanceFilter_v2`.  Without it, any candidate v2 risks
excluding prefix-AND while still admitting arbitrary `ttFormula`
payload — exactly the failure mode the original NOGO-000003
sketch warned against.

## 1. Goal (precise)

Produce three Lean terms plus a headline theorem:

```lean
def AllEssential {k : Nat} (f : Bitstring k → Bool) : Prop := …

def adversaryFamily_v_arbpayload (F : ∀ n, Bitstring (widthFn n) → Bool)
    (n : Nat) : FormulaCircuit n :=
  FormulaCircuit.rename (embed n) (ttFormula (F n))

def adversaryWitness_v_arbpayload
    (F : ∀ n, Bitstring (widthFn n) → Bool)
    (hF : ∀ n, AllEssential (F n)) :
    InPpolyFormula (adversaryLanguage_v_arbpayload F)

theorem arbitraryLogWidthTT_satisfies_diversity
    (F : ∀ n, Bitstring (widthFn n) → Bool)
    (hF : ∀ n, AllEssential (F n)) :
    Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt
      .InSupportFunctionalDiversity (adversaryWitness_v_arbpayload F hF)
```

`widthFn` is `Nat.log2 (n+1)` (S1's existing helper) by default.
Worker discretion to use the power-of-two-slice variant.

`lake build PnP3 Pnp4` and `./scripts/check.sh` MUST remain green
after the patch.  No proof-suspension placeholders, no `axiom`.

## 2. Why this is the next bar (not ProvenanceFilter_v2)

External review of the v0.4.3-followup integration accepted the
NOGO-000004 lift as valid but **scope-narrower** than the original
NOGO-000003 claim.  The post-review scope-correction NOGO-000005
makes the narrowing explicit.  Until arbitrary-payload is
formalised:

* a `ProvenanceFilter_v2` design has only the prefix-AND
  obstruction to test against — too narrow a target;
* a v2 that excludes prefix-AND may still admit arbitrary
  `FormulaCircuit.rename σ (ttFormula f)`, leaving the
  hardwiring leak open;
* the NoGoLog chain stops at NOGO-000005, with NOGO-000006
  unresolved.

`fp3b2` closes that gap.  After NOGO-000006 lands, designing v2
is meaningful because v2 must clear BOTH obstructions
simultaneously.

## 3. Slot decomposition (6 slots, parallel-attackable)

The slots are read-mostly-disjoint at file granularity.  Each
slot writes one new Lean module under
`pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/<slot>.lean`.
Slot T6 is the integration; it depends on T1..T5.

### Slot T1 — `AllEssential` predicate

**File:** `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/AllEssential.lean`

**Goal:**

```lean
def AllEssential {k : Nat} (f : Bitstring k → Bool) : Prop :=
  ∀ i : Fin k, ∃ x : Bitstring k,
    f x ≠ f (Function.update x i (! x i))
```

(Worker discretion: alternate but equivalent definitions are
acceptable, e.g. via `Function.update` or a custom `flipBit`
helper.  The downstream slots only need a stable name and a
"flip-bit-at-i changes value" specification.)

**Sanity smoke:** prove that not-AllEssential implies the
function is independent of some coordinate, and conversely.  At
minimum prove `AllEssential` is not vacuous (e.g. exhibit one
small `f` for which it holds).

### Slot T2 — `ttFormula` support cardinality from AllEssential

**File:** `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/TTFormulaSupport.lean`

**Goal (one of):**

```lean
-- Tight version (preferred):
theorem ttFormula_support_card_of_allEssential
    {k : Nat} {f : Bitstring k → Bool} (hf : AllEssential f) :
    (FormulaCircuit.support (ttFormula f)).card = k

-- Acceptable looser pair:
theorem ttFormula_support_card_le {k : Nat} (f : Bitstring k → Bool) :
    (FormulaCircuit.support (ttFormula f)).card ≤ k
theorem ttFormula_support_card_ge_of_allEssential
    {k : Nat} {f : Bitstring k → Bool} (hf : AllEssential f) :
    k ≤ (FormulaCircuit.support (ttFormula f)).card
```

**Hint:** `ttFormula` is defined recursively in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:130`.
Each `(n+1)` step splits on the first input bit, so the support
includes that input AND the rename-shifted supports of the two
recursive subformulas.  AllEssential ensures the first input bit
is genuinely needed (otherwise the formula degenerates).

The upper-bound part likely needs only structural induction +
`rename_support_card`-style reasoning (S5 RenameSupport already
shipped this).  The lower-bound part needs AllEssential to
exclude `f`-degenerate cases.

### Slot T3 — rename + injective embedding

**File:** `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/RenamePayload.lean`

**Goal:**

```lean
def embed {k n : Nat} (h : k ≤ n) : Fin k → Fin n :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem embed_injective {k n : Nat} (h : k ≤ n) :
    Function.Injective (embed h)

theorem renamed_ttFormula_support_card_of_allEssential
    {k n : Nat} (h : k ≤ n)
    {f : Bitstring k → Bool} (hf : AllEssential f) :
    (FormulaCircuit.support
       (FormulaCircuit.rename (embed h) (ttFormula f))).card = k
```

Builds on T2 + S5's `rename_support_card`.  This is mostly
plumbing.

### Slot T4 — arbitrary-payload family + language

**File:** `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean`

**Goal:**

```lean
def widthFn (n : Nat) : Nat := Nat.log2 (n + 1)

def widthFn_le (n : Nat) : widthFn n ≤ n := …  -- reuse S1

abbrev PayloadFamily := ∀ n, Bitstring (widthFn n) → Bool

def AllEssentialPayload (F : PayloadFamily) : Prop :=
  ∀ n, AllEssential (F n)

def adversaryFamily_v_arbpayload
    (F : PayloadFamily) (n : Nat) : FormulaCircuit n :=
  FormulaCircuit.rename (embed (widthFn_le n)) (ttFormula (F n))

def adversaryLanguage_v_arbpayload (F : PayloadFamily) : Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily_v_arbpayload F n) x
```

Worker discretion: choose `widthFn` from S1 (`Nat.log2 (n+1)`) or
from S2 (`k_pow2`).  Both work.  Document the choice in the
slot's docstring.

The language MUST be defined as the family's `eval` so the
`correct` field of T5's `InPpolyFormula` is `rfl`.

### Slot T5 — `InPpolyFormula` packaging

**File:** `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Witness.lean`

**Goal:**

```lean
def adversaryPolyBound_v_arbpayload (n : Nat) : Nat := 7 * (n + 1)

theorem adversaryPolyBound_v_arbpayload_poly :
    ∃ c : Nat, ∀ n, adversaryPolyBound_v_arbpayload n ≤ n ^ c + c

theorem adversaryFamily_v_arbpayload_size_le
    (F : PayloadFamily) (n : Nat) :
    FormulaCircuit.size (adversaryFamily_v_arbpayload F n)
      ≤ adversaryPolyBound_v_arbpayload n

def adversaryWitness_v_arbpayload
    (F : PayloadFamily) (hF : AllEssentialPayload F) :
    InPpolyFormula (adversaryLanguage_v_arbpayload F) where
  family := adversaryFamily_v_arbpayload F
  polyBound := adversaryPolyBound_v_arbpayload
  polyBound_poly := adversaryPolyBound_v_arbpayload_poly
  family_size_le := adversaryFamily_v_arbpayload_size_le F
  correct := fun _ _ => rfl
```

The size bound uses S3 retry's `ttFormula_size_le` (constant 7,
not 6 — the seed pack's original 6 was wrong; see
`pnp3/Magnification/AuditRoutes/LogWidthAdversary/TTFormulaSizeBound.lean`)
plus T3's `rename_size`-style preservation.  The constant `7 *
(n + 1)` follows from `7 * 2^widthFn(n) ≤ 7 * (n + 1)` because
`2^widthFn(n) = 2^Nat.log2(n+1) ≤ n + 1`.

`hF` is NOT consumed by the witness packaging proofs; it's only
needed by T6's diversity theorem.  Keep the type signatures
clean — do not drag `hF` through size proofs unnecessarily.

### Slot T6 — final diversity theorem + NOGO-000006

**File:** `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean`

**Goal:**

```lean
theorem arbitraryLogWidthTT_support_unbounded
    (F : PayloadFamily) (hF : AllEssentialPayload F) :
    ∀ B, ∃ n,
      B < (FormulaCircuit.support
        ((adversaryWitness_v_arbpayload F hF).family n)).card

theorem arbitraryLogWidthTT_support_below_n_io
    (F : PayloadFamily) (hF : AllEssentialPayload F) :
    ∀ N, ∃ n, N ≤ n ∧
      (FormulaCircuit.support
        ((adversaryWitness_v_arbpayload F hF).family n)).card < n

theorem arbitraryLogWidthTT_satisfies_diversity
    (F : PayloadFamily) (hF : AllEssentialPayload F) :
    FP3Attempt.InSupportFunctionalDiversity
      (adversaryWitness_v_arbpayload F hF) :=
  ⟨arbitraryLogWidthTT_support_unbounded F hF,
   arbitraryLogWidthTT_support_below_n_io F hF⟩
```

Use S8's `adversary_support_unbounded` reducer with
`width := widthFn`, `hWidthBySupport` from
`renamed_ttFormula_support_card_of_allEssential` (T3) +
equality, `hWidthUnbounded` from S1's `logWidth_unbounded`.

Use S9's `adversary_support_below_n_io` reducer symmetrically.

After T6 lands, append `NOGO-000006` to `outputs/nogolog.jsonl`
with `supersedes = "NOGO-000005"`, `status = "formalized"`,
`formal_witness` pointing at `Composition.lean:<line>` of the
new theorem.  Append one `outputs/attempts.jsonl` entry with
`seed_pack_id = "fp3b2_arbitrary_logwidth_tt_payload"`,
`verifier_status = "PASS_SHAPE_ONLY"`, `critic_status = "pass"`,
referencing a six-attack Critic report at
`seed_packs/fp3b2_arbitrary_logwidth_tt_payload/critic_report.md`.

## 4. Allowed scope — per slot

Each slot may add NEW files at the path listed in §3, and edit
ONLY:

* its own new file under
  `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/<slot>.lean`;
* `lakefile.lean` to wire its new module into the `Glob.one`
  list;
* (T6 only) `pnp3/Tests/AuditRoutes_ArbitraryLogWidthTT_Smoke.lean`
  for regression `#check`s;
* (T6 only) `outputs/nogolog.jsonl` (append `NOGO-000006`),
  `outputs/attempts.jsonl` (append one entry),
  `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/critic_report.md`
  (six-attack report).

If a slot worker concludes the goal is structurally unreachable
within the allowed scope, the slot ships a structured failure
report at
`seed_packs/fp3b2_arbitrary_logwidth_tt_payload/failures/T<k>_<short-name>.md`
with the four sections (what was attempted, where it broke,
local vs global obstruction, what the integrator must know).

## 5. Forbidden scope (HARD, identical to fp3b1_log_width_hardwiring_lift)

You MAY NOT:

* edit the trust root (`pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `pnp3/Magnification/LocalityProvider_Partial.lean`,
  `pnp3/Magnification/FinalResultMainline.lean`,
  `pnp3/Magnification/FinalResultAuditRoutes.lean`,
  any file declaring `ResearchGapWitness` /
  `NP_not_subset_PpolyDAG` / `P_ne_NP*`);
* edit `FP3Attempt.InSupportFunctionalDiversity` — you attack
  the ALREADY-COMMITTED filter shape;
* edit `FP3Attempt.FP3b1.adversaryFamily` /
  `adversaryWitness` / `LogWidthAdversary.*` — those are
  fp3b1's artefacts and stay untouched;
* edit existing JSONL log entries (Rule 9 — append-only);
* introduce `axiom`, `opaque`, `Fact`, typeclass payload
  (Rule 16);
* ship `sorry` / `admit` anywhere in committed Lean code;
* create `pnp3/Candidates/<id>/`;
* construct any `gap_from_*` bridge or `SourceTheorem_*`
  (FP-4 territory);
* promote any guard in `spec/known_guards.toml` to
  `status = "accepted"`;
* design `ProvenanceFilter_v2` here (that is FP-3b.3, post-T6).

## 6. Slot acceptance criteria

A slot is **complete** when:

1. The Lean theorem(s) listed in §3 for the slot compile in the
   target file path with no `sorry` / `admit`.
2. `lake build PnP3 Pnp4` succeeds with the file wired into
   `lakefile.lean`.
3. `./scripts/check.sh` 17/17 + sub-steps green (no regression
   on existing modules).
4. The slot's PR description names each new theorem and its
   file:line.

T6 additionally requires:

5. `outputs/nogolog.jsonl` validated and contains
   `NOGO-000006` with `supersedes = "NOGO-000005"`,
   `status = "formalized"`, non-null `formal_witness`.
6. `outputs/attempts.jsonl` contains a new entry with
   `seed_pack_id = "fp3b2_arbitrary_logwidth_tt_payload"` and
   `critic_status = "pass"`, referencing a non-template
   six-attack Critic report.
7. `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/critic_report.md`
   exists and follows `spec/critic_protocol.md` §1–3.

## 7. Cross-references

* Parent: `seed_packs/fp3b1_log_width_hardwiring_lift/README.md`
  — closes the prefix-AND specialisation.
* `outputs/nogolog.jsonl::NOGO-000003` — original sketch.
* `outputs/nogolog.jsonl::NOGO-000004` — first formal lift
  (prefix-AND only).
* `outputs/nogolog.jsonl::NOGO-000005` — scope correction.
* Open: `NOGO-000006` (this seed pack's deliverable).
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean`
  — the prefix-AND composition; T6 mirrors its structure.
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/TTFormulaSizeBound.lean`
  — S3-retry's exact closed form `7 * 2^k - 6` for `ttFormula` size,
  used by T5's polyBound proof.
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/RenameSupport.lean`
  — S5's `rename_support_card` lemma, used by T3.
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Diversity_Unbounded.lean`
  / `Diversity_BelowN.lean` — S8/S9 parametric reducers, used by T6.

## 8. What this seed pack is NOT trying to do

* Design `ProvenanceFilter_v2`.  That is FP-3b.3, gated on
  NOGO-000006 landing.
* Construct any `gap_from_*` bridge (FP-4 territory).
* Edit the trust root.
* Promote `ProvenanceFilter_v1`.
* Move Pilot Wave 1 from technical readiness to activation.
* Re-prove anything fp3b1 already shipped.

## 9. Closing note

> The repository's strength is the verifier, not the Generator.
> This seed pack continues that pattern: instead of inventing a
> stronger filter, we strengthen the **obstruction** until any
> proposed filter has a kernel-checked bar to clear.  After T6
> lands, the FP-N program has a precise, kernel-checked target
> that ProvenanceFilter_v2 must defeat.

Pilot Wave 1 cap is 20 workers; this seed pack's six slots fit
comfortably.  T6 is the integration, gated on T1..T5; do not
start T6 until at least one viable path through T1..T5 lands.
