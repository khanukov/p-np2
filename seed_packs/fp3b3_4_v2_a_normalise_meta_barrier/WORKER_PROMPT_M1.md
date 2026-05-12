# Worker prompt — fp3b3_4 M1 (meta-barrier statement candidate)

> Send this entire file as the prompt body to one independent
> research engineer (human + LLM session).  M1 is a
> **markdown-deliverable** exploration slot — no Lean code is
> committed in M1.  M2 and M3 are GATED on M1 landing and operator
> review.

---

You are working on slot **M1** of seed pack
`fp3b3_4_v2_a_normalise_meta_barrier/`.  The pack opens a parallel
research-insurance track exploring whether there is a formal
**meta-barrier theorem** that closes the V2-A.1 design space.  Your
deliverable is a single markdown file containing a Lean-syntax
candidate statement plus counterexample analysis.

This is **research-grade exploration**, not a Lean proof attempt.
You may sketch Lean syntax but you do NOT need to typecheck
anything against the current `pnp3` tree.

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
# No build required for M1 — markdown-only deliverable.
```

You may run `lake build PnP3 Pnp4` to confirm baseline if you wish,
but it is not required for M1.

## 1. Required reading (in order)

1. `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/README.md` —
   this pack's goal, slot decomposition, why it opened ahead of a
   `Global` classification.
2. `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/README.md` —
   the V2-A.1 design space the meta-barrier (if it exists) would
   close.  Especially §3 T1 (the structural normaliser
   requirements) and §10 (the negative-pivot protocol).
3. `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_g55_operator_audit.md` —
   the audit that opened this pack.  Note §2 (g55's `Local`
   classification verified) and §5(B) (operator override
   reasoning).
4. `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/failures/T1_g55.md` —
   g55's failure report and proposed local repair recipe.  Useful
   as a sanity check on whether the V2-A.1 design space might
   actually be alive (in which case M1 lands a `no-viable-statement`
   report).
5. **The attack the meta-barrier would be a meta-theorem about:**
   `outputs/nogolog.jsonl::NOGO-000008` and
   `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean`.
   In particular, `seedGate`, `rewritePrefixAndFamily`, and
   `v2A_rewrite_attack_prefixAnd`.
6. **The V2-A filter the normaliser would be composed with:**
   `pnp3/.../V2_A_gpt55/Filter.lean::ProvenanceFilter_v2_V2_A_gpt55_Filter`
   and `pnp3/.../V2_A_gpt55/NonVacuity.lean::seededPrefixAndWitness`.
7. **The audit-route barrier template** (for the formal shape any
   meta-barrier should fit):
   `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`.
8. **The trust root** (READ-ONLY):
   `pnp3/Complexity/Interfaces.lean` for `FormulaCircuit`, `eval`,
   `support`, `size`.
9. `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 12, 16.

## 2. Slot M1 goal

Produce a single markdown file at

```
seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_<YOUR-HANDLE>.md
```

containing:

### Section A — Predicate class `StructuralNormaliser`

A precise predicate, in Lean syntax (does NOT need to typecheck),
defining the class of normalisers we want to claim no
representative-of-this-class can simultaneously satisfy the
non-vacuity + barrier-elimination conjunction.

Suggested shape:

```lean
structure StructuralNormaliser where
  normalise   : ∀ {n : Nat}, FormulaCircuit n → FormulaCircuit n
  eval_pres  : ∀ {n : Nat} (C : FormulaCircuit n) (x : Bitstring n),
                  FormulaCircuit.eval (normalise C) x =
                  FormulaCircuit.eval C x
  size_le    : ∀ {n : Nat} (C : FormulaCircuit n),
                  FormulaCircuit.size (normalise C) ≤ FormulaCircuit.size C
  -- ... add the "no truth-table, no Classical.choose, no semantic
  -- quotient" constraints in Lean-formalisable terms (this is the
  -- hard part of M1).
```

The hard part is the **structurality constraint**.  Candidate
formalisations include:

* **Structural recursion shape:** `normalise` is definitionally
  equal to a `FormulaCircuit.rec`-style elimination with local
  per-constructor cases.  Lean-formalisable via `Function.LeftInverse`
  / pattern-match exhaustiveness arguments, possibly using
  meta-level induction.
* **Computability / decidability shape:** require
  `Decidable (normalise C₁ = normalise C₂)` is **propositionally
  decidable from syntactic data only**, ruling out semantic
  reconstruction.
* **Information-theoretic shape:** the syntactic depth of
  `normalise C` is bounded by a polynomial in the syntactic depth
  of `C` (not in the truth-table size of `eval C`).
* **Combination:** require all of the above as a conjunction.

Discuss which formalisation you propose and why.  Acknowledge
which formalisations are too strict (rule out g55's intended
syntactic normaliser, making the meta-barrier vacuously true) or
too loose (admit semantic quotients, making the meta-barrier
false-by-counterexample).

### Section B — Meta-barrier statement candidate

The candidate theorem statement, in Lean syntax (does NOT need to
typecheck), of roughly this shape:

```lean
theorem v2_a_structural_normalisation_meta_barrier :
    ∀ (𝒩 : StructuralNormaliser),
      -- Predicate (a): eliminates NOGO-000008 seed
      (∀ {n : Nat} (h : 1 ≤ n),
         𝒩.normalise (seedGate n h) = const true) →
      -- Predicate (b): preserves seededPrefixAndFamily as-is
      (∀ {n : Nat},
         𝒩.normalise (seededPrefixAndFamily n)
           = seededPrefixAndFamily n) →
      -- Implication: composing 𝒩 with V2-A's filter fails to
      -- simultaneously admit seededPrefixAnd AND reject
      -- rewritePrefixAnd.
      ¬ (V2_A_with_normaliser 𝒩 admits seededPrefixAndWitness ∧
         V2_A_with_normaliser 𝒩 rejects rewritePrefixAndWitness)
```

The exact predicates and the exact conclusion are your design
choice.  Document the design choices and explain what's at stake
in each choice.

### Section C — Counterexample analysis

For each of the following, evaluate whether your candidate
statement holds:

1. **Trivial-failure candidates** (worker must find at least
   three): structural normalisers that obviously fail one of the
   structurality constraints, demonstrating the statement is not
   vacuously true.
2. **Vacuous candidates** (worker must find at least three):
   conditions under which the conclusion is vacuously true (e.g.
   the conjunction in the conclusion is already false because
   the antecedents are inconsistent for trivial reasons).  If
   your statement is vacuous, document why and revise.
3. **g55's intended normaliser** (READ THE FAILURE REPORT):
   does your candidate statement classify g55's structural
   recursion as a `StructuralNormaliser` (i.e. would the
   meta-barrier apply to it)?  If YES, your candidate predicts
   g55's retry will fail in a specific, formalisable way — name
   that prediction concretely.  If NO, explain why g55's
   normaliser doesn't fit the class (this may be a bug in your
   class formalisation).
4. **Plausible existence proof** (anti-meta-barrier): can you
   construct, on paper, a `StructuralNormaliser` matching your
   class that DOES satisfy both predicates (a) and (b) AND
   refutes the meta-barrier?  If yes, the meta-barrier hypothesis
   is **discredited** at the M1 stage and you should ship a
   no-viable-statement report instead (see §6).

### Section D — Proof-strategy preview (NOT proof attempt)

Given your candidate statement, what kind of argument would prove
it?  Suggested sketch:

* **Adversarial-rewrite construction:** for any `𝒩` satisfying
  (a), construct (on paper) an adversarial family `rewriteAttack_𝒩`
  parametric in `𝒩`'s syntactic action, such that `𝒩.normalise
  (rewriteAttack_𝒩 n)` is forced into a specific syntactic shape
  that violates (b).
* **Information-theoretic argument:** the syntactic resolution of
  any structural normaliser cannot distinguish a certain class of
  semantically-equivalent rewrite variants of
  `seededPrefixAndFamily`, forcing collapse onto a single
  syntactic image whose semantics conflict with (b).
* **Diagonalisation:** for each `𝒩`, construct a specific
  `C_𝒩` whose normalisation `𝒩.normalise C_𝒩` cannot
  syntactically distinguish (a)-compliant from (b)-compliant
  outputs.

Pick the strategy you think most plausible and sketch its skeleton
in 50-100 lines.  This is the M2 deliverable preview — useful for
operator review of whether M1 + M2 should proceed to M3.

### Section E — Recommended next step

End with a one-paragraph recommendation:

* **`PROCEED to M2`:** the candidate statement is non-vacuous,
  resists obvious counterexamples, and a proof strategy is
  plausible.
* **`HOLD for revision`:** the candidate statement has known weak
  points but is salvageable; revisions outlined.
* **`DISCREDITED — ship no-viable-statement report`:** counterexample
  in Section C(4) refutes the meta-barrier hypothesis at M1 stage,
  and `fp3b3_3` T1 retry becomes the priority track.

## 3. File-path convention

Pick `<YOUR-HANDLE>` (short, lowercase, alphanumeric).  Your file
goes to:

```
seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_<YOUR-HANDLE>.md
```

The trailing handle means multiple workers can attack M1 in
parallel.  At operator review, the cleanest landed candidate is
promoted to the basis for M2.

## 4. Allowed / forbidden scope

### Allowed

* New markdown files under
  `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/`.
* Reading any existing file in the repo.
* Citing line numbers from any `pnp3/` or `pnp4/` file.

### Forbidden (HARD)

* Any Lean file creation or edit.  M1 is markdown-only.
* Editing fp3b3_3 files (it is the sibling track, not editable
  from here).
* Editing V2-A trust root or any module under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`.
* Editing `outputs/nogolog.jsonl`, `outputs/attempts.jsonl`,
  `spec/known_guards.toml`, or any registry/audit log.
* Promoting any guard or candidate.
* Creating `pnp3/Candidates/` entries.
* Proposing FP-4 / `SourceTheorem_*` / `gap_from_*` / final endpoint
  language.  Meta-barrier theorems are about a design space, not
  endpoints.
* Claiming P ≠ NP, ResearchGapWitness, or any unconditional
  separation language.
* Appending NOGO entries.  Meta-barriers (if landed) are positive
  theorems about a class of normalisers, not NOGO entries.

## 5. Acceptance checklist (for M1 landing)

- [ ] File `candidates/M1_<HANDLE>.md` exists.
- [ ] Sections A, B, C, D, E all present and substantive.
- [ ] At least 3 trivial-failure candidates in Section C(1).
- [ ] At least 3 vacuous candidates in Section C(2).
- [ ] Section C(3) explicitly addresses g55's normaliser.
- [ ] Section C(4) explicitly attempts an anti-meta-barrier
      counterexample (even if it fails — failure is informative).
- [ ] Section E gives one of three recommendations: PROCEED to M2,
      HOLD for revision, or DISCREDITED.
- [ ] No Lean files added or edited.
- [ ] No registry / log / spec files modified.

## 6. Failure mode — no viable statement

If after honest exploration you find that every candidate
meta-barrier statement is either trivially failing or vacuous, OR
if your Section C(4) anti-meta-barrier construction succeeds (i.e.
you can construct a plausible structural normaliser that satisfies
both (a) and (b)), ship a no-viable-statement report at

```
seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/failures/M1_no_viable_statement_<HANDLE>.md
```

with EXACTLY these four sections:

1. **What was attempted.**  Summary of candidate statements you
   tried and why each failed.
2. **Where it broke.**  Specific counterexample or vacuity argument
   that closed the most promising candidate.
3. **Local vs global obstruction.**  Local: this particular class
   formalisation didn't work; another might.  Global: the
   meta-barrier hypothesis is structurally false — every plausible
   structural normaliser class admits a representative that
   defeats NOGO-000008 while preserving non-vacuity.
4. **What an integrator must know.**  If Global: fp3b3_3 T1
   retry becomes the priority track and fp3b3_4 is archived.
   If Local: another M1 attempt with a different class
   formalisation may succeed.

## 7. Output format (response back to operator)

```
Slot: M1
Handle:
Branch:
Commit:
File: seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_<HANDLE>.md

Outcome:
  CANDIDATE_LANDED | NO_VIABLE_STATEMENT

If candidate landed:
  predicate class shape (1-2 sentences):
  meta-barrier statement shape (1-2 sentences):
  most plausible counterexample considered:
  proof-strategy preview class:
  recommendation: PROCEED to M2 | HOLD for revision

If no viable statement:
  failure file:
  local/global obstruction:
  shortest explanation:
  recommended next move: fp3b3_3 T1 retry priority

Scope violations:
  none | list
```

## 8. Work style

* Do not ask the operator questions.  If you cannot proceed, ship
  a no-viable-statement report with reasoning, not a question.
* Do not stop on `needs_review` — operator review is async on the
  artifact, not on a worker pause.
* Do not invent Lean modules or "useful" infrastructure beyond M1
  scope.  M1 is markdown-only.
* Do not extend forbidden scope.  If your candidate seems to
  require editing V2-A or the trust root, your class formalisation
  is wrong — rethink.
* Cite specific line numbers when you refer to existing Lean code.
  Vague references degrade the candidate's value.
* Pre-empt obvious objections in Section C.  An operator reviewer
  who can find a 5-minute counterexample your candidate misses
  will return the candidate for revision.
* If you must mark a section as "open question", do so explicitly
  with `[OPEN]` and a one-line description of what you'd need to
  resolve it.

The deliverable is research-grade exploration.  The operator
review evaluates whether the candidate is good enough to base M2
on, not whether it is the final answer.
