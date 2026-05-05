# Worker prompt — fp3b1_log_width_hardwiring_lift

> Single unified prompt sent independently to 10 research engineers
> (human + LLM sessions).  Each engineer/session works without
> knowing what the other 9 produce; the dispatcher (the user)
> collects all 10 outputs and a separate integration phase picks
> the cleanest one for canonical merge.
>
> Send this entire file as the prompt body.  No customisation
> needed.

---

You are ONE of 10 independent research engineers attacking the same
Lean goal in parallel.  You do NOT know what the other 9 are
producing.  Expect multiple parallel attempts; only the cleanest
will be merged into the canonical position, but **every output is
valuable**, including failure reports.

Pick a unique handle for yourself — your initials, your model name,
or `<role>-<date>-<random>` (e.g. `alice`, `opus-001`,
`gpt-2026-05-05-am`).  Use this handle in EVERY file path you
create so your work cannot collide with another parallel attempt.

## 0. Repository setup (read-only verification first)

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

If the baseline is RED on a fresh checkout, STOP and report —
do not attempt the goal.  The goal builds on a green baseline.

## 1. Required reading (in order, do not skip)

1. `seed_packs/fp3b1_log_width_hardwiring_lift/README.md` — the
   parallel-decomposition seed pack.  Read §0–§3, §5, §6, §10 in
   full.  The slot table in §4 is a *suggested roadmap*, not your
   assignment — you may follow it or roll your own decomposition.
2. `outputs/nogolog.jsonl::NOGO-000003` — find this entry by
   `id` field.  Its `notes` field contains the construction sketch
   you are trying to formalise.  Read the entire `notes` text.
3. `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`:
   - lines 231–234: `FP3Attempt.InSupportFunctionalDiversity` —
     the predicate you must satisfy.
   - lines 265–280: `InSupportFunctionalDiversity_excludes_uniformPolyBound`
     — companion theorem; reading it tells you the shape of
     arithmetic the diversity proof needs.
   - lines 340–431: `FP3Attempt.FP3b1` — placeholder skeleton with
     `adversaryFamily := fun _ => FormulaCircuit.const false`.
     Your work conceptually replaces this body, but you do NOT
     edit this file (see §3 forbidden scope).
4. `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`:
   - line 107: `FormulaCircuit.rename` — already defined.
   - line 115: `FormulaCircuit.eval_rename` — already proved.
   - line 130: `ttFormula` — recursive truth-table-shape formula.
   Use these as building blocks; do not redefine.
5. `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.  Hard
   constraints; non-negotiable.

## 2. Goal (single, kernel-checked, no `sorry`)

Produce a Lean term equivalent to

```lean
theorem logWidthAdversary_satisfies_diversity :
    Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt
      .InSupportFunctionalDiversity adversaryWitness
```

where:

* `adversaryFamily : ∀ n : Nat, FormulaCircuit n` is a
  polynomial-size truth-table-shaped family on a sublinear /
  log-width window of variables (NOT a constant family — see
  §5 trap below);
* `adversaryLanguage : Pnp3.ComplexityInterfaces.Language` is
  defined as `fun n x => FormulaCircuit.eval (adversaryFamily n) x`
  so that the `correct` field of `InPpolyFormula` is provable by
  `rfl`;
* `adversaryWitness : Pnp3.ComplexityInterfaces.InPpolyFormula
   adversaryLanguage` packages the family with a `polyBound` of
  the form `polyBound n := 6 * (n + 1)` (or any concrete
  polynomial bound that holds and clears `polyBound_poly`).

`lake build PnP3 Pnp4` and `./scripts/check.sh` MUST remain green
after your patch.

## 3. File path convention (PREVENTS COLLISIONS)

Place ALL your new Lean files under

```
pnp3/Magnification/AuditRoutes/LogWidthAdversary/Attempt_<YOUR-HANDLE>/
```

Pick `<YOUR-HANDLE>` once and use it consistently.  Examples:

* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Attempt_alice/Width.lean`
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Attempt_alice/Family.lean`
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Attempt_alice/Diversity.lean`

Wire each new module into `lakefile.lean` under the existing
`Glob.one ...` list (e.g.
`Glob.one \`Magnification.AuditRoutes.LogWidthAdversary.Attempt_alice.Width`).

You may also optionally add a sanity smoke test at

```
pnp3/Tests/AuditRoutes_LogWidthAdversary_Smoke_<YOUR-HANDLE>.lean
```

that `#check`s your top-level theorem.

## 4. Allowed scope

You MAY add or modify only:

* New files under
  `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Attempt_<YOUR-HANDLE>/`.
* `lakefile.lean` — append your new modules to the existing
  `Glob.one ...` list.  Do NOT remove or reorder existing entries.
* Optional smoke test at
  `pnp3/Tests/AuditRoutes_LogWidthAdversary_Smoke_<YOUR-HANDLE>.lean`.
* If you ship Outcome B (failure report) instead of Outcome A:
  `seed_packs/fp3b1_log_width_hardwiring_lift/failures/<YOUR-HANDLE>.md`.

## 5. Forbidden scope (HARD; non-negotiable)

You MAY NOT:

* edit anything outside §4 Allowed scope;
* edit `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/**`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `pnp3/Magnification/LocalityProvider_Partial.lean`,
  `pnp3/Magnification/FinalResultMainline.lean`,
  `pnp3/Magnification/FinalResultAuditRoutes.lean`,
  or any file declaring `ResearchGapWitness` /
  `NP_not_subset_PpolyDAG` / `P_ne_NP*` (Rule 0 — trust root);
* edit `FP3Attempt.InSupportFunctionalDiversity` —
  you attack the ALREADY-COMMITTED filter shape (Rule 1);
* edit `Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1` —
  the integration phase handles the canonical merge;
* edit any other engineer's
  `Attempt_<other-handle>/` directory — those are independent
  parallel attempts;
* edit `outputs/nogolog.jsonl` or `outputs/attempts.jsonl` (the
  integration phase handles ledger upgrades);
* edit any other existing JSONL log entry (Rule 9 — append-only,
  corrections via `supersedes`);
* introduce `axiom`, `opaque`, `Fact`, `class`/`instance` /
  typeclass payload (Rule 16);
* ship `sorry` / `admit` anywhere in committed Lean code;
* create `pnp3/Candidates/<id>/` (audit-only routing —
  `spec/critic_protocol.md` §7);
* construct any `gap_from_*` bridge or `SourceTheorem_*` (FP-4
  territory);
* promote any guard in `spec/known_guards.toml` to
  `status = "accepted"`.

### IMPORTANT TRAPS (engineers regularly fall in these)

* **Constant family fails.**  `adversaryFamily := fun _ =>
  FormulaCircuit.const false` (or `const true`) has empty / full
  support uniformly and FAILS the diversity unboundedness
  conjunct.  You MUST pick a body whose support cardinality is
  unbounded as `n → ∞`.  The standard trick is `family n :=
  FormulaCircuit.rename (Fin.castLE …) (ttFormula f_k)` for some
  Boolean function `f_k : Bitstring k → Bool` whose `ttFormula`
  has FULL support `Finset.univ` (e.g. `f_k x := x ⟨0, _⟩`,
  the first input bit, with a special case at `k = 0`).
* **Wrong `adversaryLanguage` packaging.**  Defining
  `adversaryLanguage := fun _ _ => false` and trying to prove
  `correct` against an arbitrary truth-table family CANNOT
  WORK.  Always define
  `adversaryLanguage n x := FormulaCircuit.eval (adversaryFamily n) x`
  so `correct = fun _ _ => rfl`.  This is documented in the
  seed pack §4 (parent) and FP3b1's docstring.
* **Width function pitfall.**  If you use `Nat.log2 (n+1)`, you
  need `Nat.log2 (n+1) ≤ n` (true).  If you use a
  power-of-two-slice scheme `k_pow2 n := if n = 2^t then t else 0`,
  you need decidable `n = 2^t`; mathlib provides this via
  `Nat.isPowerOfTwo` or you can hand-roll.
* **`InPpolyFormula.polyBound_poly` is not optional.**  Pick a
  bound like `polyBound n := 6*(n+1)` AND prove
  `∃ c, ∀ n, polyBound n ≤ n^c + c` for some explicit `c`
  (e.g. `c = 7` works for `6*(n+1) ≤ n + 7` for `n ≥ 1`, with
  the `n = 0` case handled separately).

## 6. Output (exactly ONE of two outcomes)

### Outcome A — theorem landed (preferred)

Submit a unified diff or a branch named
`worker/fp3b1lift/<YOUR-HANDLE>` containing:

1. New Lean files under
   `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Attempt_<YOUR-HANDLE>/`
   producing a kernel-checked theorem of type
   `FP3Attempt.InSupportFunctionalDiversity adversaryWitness`,
   with no `sorry` / `admit`.
2. Updated `lakefile.lean` wiring your modules.
3. Optional smoke test referenced in §4.
4. A one-paragraph commit message naming your top-level theorem,
   pointing to its file:line, and confirming the acceptance
   checklist below.

**Acceptance checklist (every item must be true):**

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` green (17/17 + sub-steps).
- [ ] `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` returns
      nothing.
- [ ] Top-level theorem has type
      `FP3Attempt.InSupportFunctionalDiversity adversaryWitness`
      (or definitionally equal).
- [ ] `adversaryFamily` is NOT a constant family.
- [ ] `adversaryLanguage` is defined as
      `fun n x => FormulaCircuit.eval (adversaryFamily n) x`,
      and the `correct` field of `InPpolyFormula` reduces to
      `fun _ _ => rfl`.
- [ ] No file outside `Attempt_<YOUR-HANDLE>/`,
      `lakefile.lean`, and the optional
      `Smoke_<YOUR-HANDLE>.lean` is modified.
- [ ] No `axiom` / `opaque` / typeclass-payload smuggled into
      the proof.
- [ ] No edits to other engineers' `Attempt_<other-handle>/`.

### Outcome B — structured failure report

If after honest effort you cannot discharge the goal, ship a
markdown file at

```
seed_packs/fp3b1_log_width_hardwiring_lift/failures/<YOUR-HANDLE>.md
```

with EXACTLY these four sections:

1. **What was attempted.**  Decomposition you tried, mathlib
   lemmas considered, file paths created.
2. **Where it broke.**  Specific definitional or proof
   obstruction.  Paste the Lean error message verbatim.
3. **Local vs global obstruction.**
   - **Local** = a missing helper lemma or import you didn't
     have time for.  The goal is reachable; another engineer
     can pick up.
   - **Global** = the goal is structurally unreachable from
     the current Lean state (e.g. `FormulaCircuit.support` does
     not have the property the seed pack assumed, OR the
     `InPpolyFormula` packaging does not actually admit a
     non-constant family with a polynomial `polyBound`).  This
     is itself a research result.
4. **Pointer.**  What a future integrator must know if they
   pick up where you left off.

A failure report does NOT need `lake build` green for incomplete
Lean files — but those broken Lean files MUST NOT be committed.
The committed delta is exactly the markdown failure file (and
nothing else).

## 7. Hard rules (re-stated; do not forget under any circumstance)

* No `sorry` / `admit` anywhere in committed Lean code.
* No trust-root edit.
* No final endpoint, no bridge, no `SourceTheorem`.
* No `pnp3/Candidates/` directory.
* No editing other handles' directories.
* No editing existing JSONL log entries.
* `lake build PnP3 Pnp4` + `./scripts/check.sh` must stay green.

## 8. What success means scientifically

The repository moves
`outputs/nogolog.jsonl::NOGO-000003` from
`status = "needs_review"` to `status = "formalized"` — a real
Lean theorem provably refuting the
`FP3Attempt.InSupportFunctionalDiversity` filter via log-width
truth-table hardwiring.  This is a **negative breakthrough in
the spirit of Razborov–Rudich**: not "P ≠ NP", but
"this entire class of provenance filters is provably
insufficient, kernel-checked".  Any future
`ProvenanceFilter_v2` will have to clear this bar.

You are one of 10 parallel attempts.  Only the cleanest
Outcome-A submission will be merged into the canonical FP3b1
namespace by the integration phase.  All 10 outputs (theorems
AND failure reports) feed into the integration decision.  Your
handle keeps your work attributable.

## 9. Begin

1. Pick `<YOUR-HANDLE>`.
2. Verify the green baseline (§0).
3. Read the required materials (§1).
4. Choose your decomposition strategy (§3 / seed-pack §4 is a
   suggested roadmap).
5. Iterate until either Outcome A or Outcome B holds.
6. Submit your patch / branch / failure report and stop.

Do not ask for clarification — the seed pack and the references
in §1 are the complete spec.  If something looks ambiguous, your
discretion + Lean's type checker resolve it.

End of prompt.
