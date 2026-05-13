# Worker prompt — fp3b4_support_cardinality_barrier

> Send this entire file as the prompt body to one independent
> research engineer (human + LLM session) per slot.  Workers
> self-pick `<HANDLE>` and `<SLOT>`.  Multiple workers may attack
> the same slot; the cleanest output is merged at audit-review.

---

You are working on slot `T<k>` (1..6) of seed pack
`fp3b4_support_cardinality_barrier/`.  The seed pack lifts the
concrete `NOGO-000006` obstruction into a meta-barrier theorem
about support-cardinality-only filters.

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN before you start.  If RED on a fresh
checkout, stop and report.

## 1. Required reading

1. `seed_packs/fp3b4_support_cardinality_barrier/README.md` —
   the goal, slot decomposition, allowed/forbidden scope.
2. `outputs/nogolog.jsonl::NOGO-000006` (concrete predecessor) and
   `outputs/nogolog.jsonl::NOGO-000005` (scope correction context).
3. `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`:
   `FP3Attempt.InSupportFunctionalDiversity` (line 231),
   `FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd` (line ~360),
   the FP3b1 placeholder.
4. `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean`
   — `prefixAnd_support_lt`, `prefixAnd_support_card`.  These are
   the building blocks T2 reuses.
5. `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean`
   — `adversaryFamily_v_arbpayload`, `adversaryFamily_v_arbpayload_support_card`.
   The fp3b2 generalisation is the closest precedent to this seed
   pack's T1–T3 (parameterise from `s = logWidthNat` to arbitrary
   `s : Nat → Nat` with `s n ≤ n`).
6. `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.

## 2. Slot list (pick one)

**Dependency chain (read carefully before picking):**

```text
T1 (canonicalHardwiringFamily)  ← independent
T4 (IsSupportCardinalityOnly)   ← independent
T2 (canonicalHardwiringFamily_support_card)  ← depends on T1
T3 (canonicalHardwiringWitness)              ← depends on T1, T2
T5 (Barrier theorem)            ← depends on T1, T2, T3, T4
T6 (Application + NOGO-000007)  ← depends on T5
```

T1 and T4 may start immediately in parallel.  T2/T3 may start in
parallel **only with explicit dependency awareness**:

* If T1 has landed in the tree → import T1's module, proceed
  normally.
* If T1 has NOT landed yet → DO NOT redefine
  `canonicalHardwiringFamily` or `canonicalHardwiringLanguage`
  in your slot file (that's T1's job; duplicating creates merge
  conflict and namespace collision).  Instead, ship a structured
  **blocker report** at
  `seed_packs/fp3b4_support_cardinality_barrier/failures/T<k>_<HANDLE>_blocked_on_T1.md`
  with one section: "T1 not yet in tree as of `<commit-hash>`;
  resuming when T1 lands."  Then stop.

T5 and T6 are NOT in scope for this dispatch round; do not pick
them.

| Slot | File | Goal | Depends on |
| ---- | ---- | ---- | ---------- |
| T1 | `SupportCardinalityBarrier/CanonicalHardwiringFamily.lean` | `canonicalHardwiringFamily` + `canonicalHardwiringLanguage` (parameterised by `s : Nat → Nat`, `hs : ∀ n, s n ≤ n`) | — (independent) |
| T2 | `SupportCardinalityBarrier/CanonicalHardwiringSupport.lean` | `canonicalHardwiringFamily_support_card : (support …).card = s n` | **T1** |
| T3 | `SupportCardinalityBarrier/CanonicalHardwiringWitness.lean` | `canonicalHardwiringWitness : InPpolyFormula (canonicalHardwiringLanguage s hs)` with linear `polyBound n := 2*n+1` | **T1**, **T2**, fp3b1's `prefixAnd_size` |
| T4 | `SupportCardinalityBarrier/SupportCardinalityOnly.lean` | `IsSupportCardinalityOnly Π : Prop` (weak invariance: filter doesn't distinguish witnesses with same support function) | — (independent) |
| T5 | `SupportCardinalityBarrier/Barrier.lean` | `support_cardinality_barrier` headline theorem (3-line proof using T2 + T4) | T1, T2, T3, T4 — **NOT in this dispatch round** |
| T6 | `SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean` + `outputs/nogolog.jsonl` (`NOGO-000007`) + `outputs/attempts.jsonl` + `seed_packs/fp3b4_support_cardinality_barrier/critic_report.md` | Apply barrier to `InSupportFunctionalDiversity`; ship NOGO-000007 + Critic report | T1–T5 — **NOT in this dispatch round** |

T6 is the integration slot; it can ship only after T1..T5 land
AND a separate dispatch round opens it.

## 3. File-path convention

If multiple workers attack the same slot in parallel, each picks
`<YOUR-HANDLE>` and uses

```
pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/<SlotName>_<YOUR-HANDLE>.lean
```

so the patches don't collide.  At audit-review, the cleanest
attempt is renamed to canonical (without handle) and merged.

If only one worker is active per slot, ship at the canonical path
directly (no handle suffix).

Wire each new module into `lakefile.lean` under the existing
`Glob.one ...` list.

## 4. Allowed / forbidden scope

See seed pack `README.md` §4.  The hard rules:

* No trust-root edit.
* No editing existing JSONL log entries (Rule 9 — append-only).
* No `sorry` / `admit` in committed Lean (Rule 1).
* No `axiom` / `opaque` / `Fact` / typeclass-payload (Rule 16).
* No editing `FP3Attempt.InSupportFunctionalDiversity` predicate or
  any fp3b1/fp3b2 theorem bodies — generalise, don't rewrite.
* No `pnp3/Candidates/` creation.
* No `gap_from_*` / `SourceTheorem_*` / final endpoint.
* No `ProvenanceFilter_v1` promotion to `accepted`.
* No `ProvenanceFilter_v2` design — that's `fp3b3`.
* No Wave 1 activation by force.

## 5. Output (exactly ONE of two)

### Outcome A — slot theorem(s) landed

Submit a unified diff or branch named
`worker/fp3b4/<SLOT>_<YOUR-HANDLE>` containing:

* New Lean file(s) at the slot path with the named theorem(s).
* Updated `lakefile.lean` wiring.
* (T6 only) `outputs/nogolog.jsonl` append, `outputs/attempts.jsonl`
  append, `seed_packs/fp3b4_support_cardinality_barrier/critic_report.md`.
* One-paragraph commit message naming each new theorem and its
  file:line.

**Acceptance checklist (all must be true):**

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` green (17/17 + 12.b/c/d/e/f/g/h/j/k).
- [ ] `rg "\bsorry\b|\badmit\b" -g"*.lean"
       pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/`
      returns nothing.
- [ ] No file outside §4 allowed scope is modified.
- [ ] (T6 only) `validate_jsonl.py` green on both ledgers.

### Outcome B — structured failure report

If the slot is structurally unreachable, ship a markdown file at

```
seed_packs/fp3b4_support_cardinality_barrier/failures/T<k>_<YOUR-HANDLE>.md
```

with EXACTLY these four sections:

1. **What was attempted.**
2. **Where it broke.**  Paste the Lean error message verbatim.
3. **Local vs global obstruction.**
   * Local: missing helper lemma.
   * Global: the meta-barrier shape is structurally wrong (e.g.
     `prefixAnd` doesn't actually live in `InPpolyFormula L` for
     arbitrary `L`).  This is a research result.
4. **What an integrator must know.**

Broken Lean files MUST NOT be committed.

## 6. What success means scientifically

Closes a class of v2 filter candidates: any v2 that depends only
on support cardinality is automatically refuted by
`support_cardinality_barrier`.  The repo gains a fourth Lean
barrier theorem (audit-only, scoped to FP-N filter design rather
than the full P-vs-NP landscape).  After this lands, `fp3b3`
workers have a sharp precondition: their v2 candidate must use
information beyond support cardinality.

## 7. Begin

1. Pick `<YOUR-HANDLE>` and `<SLOT>`.
2. Verify the green baseline.
3. Read §1 materials.
4. Choose your decomposition strategy within the slot.
5. Iterate until Outcome A or Outcome B.
6. Submit and stop.

End of prompt.
