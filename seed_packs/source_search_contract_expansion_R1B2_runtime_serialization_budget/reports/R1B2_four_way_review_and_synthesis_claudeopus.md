# R1-B2 four-way parallel dispatch comparative review and synthesis — claudeopus

**Slot:** R1-B2 operator decision (comparative review of four parallel codex dispatches).
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `2a9e1e6`.

**Review subjects:**

| Version | PR | Commit | Worker | Report LOC | Filename |
| --- | --- | --- | --- | --- | --- |
| **V1** | #1283 | `6536f4c` | gpt55 | 548 | `R1B2_runtime_budget_gpt55.md` |
| V2 | #1286 | `6eeee02` | gpt55 | 379 | `R1B2_runtime_budget_gpt55.md` |
| V3 | #1284 | `1ff5ab6` | codex | 584 | `R1B2_runtime_budget_codex.md` |
| V4 | #1285 | `a868e9a` | gpt55 | 414 | `R1B2_runtime_budget_gpt55.md` |

All four PRs landed parallel `codex` dispatches of the same R1-B2 seed-pack task. All four have **identical** `README.md` (143 LOC) and `WORKER_PROMPT_R1B2.md` (181 LOC) seed-pack skeleton files; divergence is only in the report content. All four are markdown-only (no Lean code, no JSONL / spec / trust-root edits).

This is **operator-scoped review**. No Lean edits in this review. No JSONL / spec / known_guards / trust-root edits. No `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims. No R1-C implementation.

---

## 1. Verdict

```text
merged_V1 (PR #1283, 6536f4c) as canonical R1-B2 report
closed_V2 (PR #1286)  — compressed version of V1
closed_V3 (PR #1284)  — thoroughest signature audit, less actionable
closed_V4 (PR #1285)  — concrete module naming, less detailed structure design
```

**All four reports converge on the same diagnosis**, in unanimous agreement:

* `TreeCircuitWitnessCodec.verifiesDecidable` is **exponential in `n`** because it enumerates all `2^n` Boolean assignments via `Fintype.decidableForallFintype`.
* The same enumeration is **plausibly polynomial in `M(n)`** because `tableLen n = 2^n ⊆ problem.instanceBits n`, so the loop count is bounded by the ambient input length when `tableLen n ≤ M(n)`.
* `PrefixExtensionLanguage_in_NP` **cannot be honestly claimed** in the current repository because there is no bridge from staged budget predicates to pnp3 `NP_TM` (the concrete Turing-machine verifier interface).
* R1-C remains gated; opening it would inherit the fp3b8 wrapper-around-unexpanded-contract pattern.

**Strong unanimity is itself a signal.** Four independent codex workers, two different model handles, converged on the same load-bearing distinction (`poly(n)` vs `poly(M(n))`) and the same architectural blocker (missing `NP_TM` bridge). This is **the diagnosis**, not contested.

V1 was chosen as canonical for **actionability** — see §2 below. V2/V3/V4 closed with explanatory comments; their best unique content is synthesized in §3 of this review.

---

## 2. Why V1 (PR #1283) was chosen

V1 contains the **most concrete advancement-enabling content**:

### 2.1 §8 — concrete `TreeMCSPPrefixRuntimeBudget` structure design

V1 proposes an explicit Lean structure design that separates **arithmetic theorems** (real Lean `∃ c, ∀ n, ... ≤ M n^c + c` shapes) from **`Prop` placeholders** for fields that still need computational-model commitment:

```lean
structure TreeMCSPPrefixRuntimeBudget
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (M : Nat → Nat) : Type where
  tableLen_le_M : ∀ n, Pnp3.Models.Partial.tableLen n ≤ M n
  threshold_poly_in_M : ∃ c, ∀ n, threshold n ≤ M n ^ c + c
  witnessBits_poly_in_M : ∃ c, ∀ n, codec.witnessBits n ≤ M n ^ c + c
  decode_polynomial_time_in_M : Prop
  parser_polynomial_time_in_M : Prop
  circuit_eval_polynomial_time_in_size : Prop
  relation_polynomial_time_in_M : Prop
```

This is **directly usable as a Lean module template** for the next R1-B2 dispatch. V2/V3/V4 lack this concrete structure design.

### 2.2 §3 — concrete ambient-length convention

V1 proposes the explicit decomposition:

```text
M(n) = tagBits
     + nCodeBits(n)
     + iCodeBits(n)
     + problem.instanceBits n     -- = tableLen n = 2^n for tree-MCSP
     + problem.witnessBits n
     + padBits(n)
```

with the arithmetic obligation `tableLen n ≤ M(n)` immediate by construction. V1 also gives an explicit Lean signature:

```lean
def treeMCSPPrefixAmbientLength
    (witnessBits overhead padBits : Nat → Nat) (n : Nat) : Nat :=
  overhead n + Pnp3.Models.Partial.tableLen n + witnessBits n + padBits n

lemma tableLen_le_treeMCSPPrefixAmbientLength
    (witnessBits overhead padBits : Nat → Nat) (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength witnessBits overhead padBits n
```

This is **ready to drop into a Lean file**. V4 has the named record but not the full arithmetic lemma. V2/V3 don't have it.

### 2.3 §11 — concrete next-step proposal

V1 names "R1-B2a" with 4 specific sub-deliverables:
1. Concrete or parameterized `M(n)` with `tableLen_le_M` lemma.
2. Runtime-aware codec refinement with `witnessBits_poly_in_M`, `decode_polynomial_time_in_M`, circuit syntax-size bound.
3. Parser theorem list or concrete `parseTreeMCSPPrefix` for the selected serialization.
4. Decide whether direct TM verifier or small verified algorithm-cost layer compiles to `NP_TM`.

This is the **operational next-step plan**. V2/V4 have less detailed equivalents; V3 has a similar list but lacks the concrete structure design that would let item (1) be discharged.

---

## 3. Synthesis: best content from all 4 reports

Even though V2/V3/V4 are closed, each contributes unique value that I extract here for the operator's reference.

### 3.1 From V3 (codex, 584 LOC) — thorough signature audit

V3's §2 "Exact signatures inspected" (~215 LOC) is the **most thorough signature audit** of the existing interfaces. It reproduces verbatim signatures for:

* `PrefixInput`, `PrefixParser`, `PrefixExtendableInput`, `PrefixExtensionLanguage`
* `PrefixExtensionNPVerifierBudget` (all 9 fields)
* `treeMCSPPrefixParser`, `TreeMCSPPrefixParserObligations`, `treeMCSPSearchRelation_decidable_of_*`
* `TreeCircuitWitnessCodec`, `TreeCircuitWitnessCodec.verifies`, `TreeMCSPSearchWitnessEncoding.ofCodec`
* `SearchMCSPCompressionProblem`, `treeMCSPSearchProblem`
* `Pnp3.ComplexityInterfaces.NP_TM` and the canonical NP definition

**Operator note:** if a future Lean worker needs a one-stop reference for the existing surface, V3's §2 is the best source. Its closure does **not** discard this information — V3 is still readable on its branch `khanukov/create-r1-b2-seed-pack-skeleton-jbvbza` (or via PR #1284's diff).

### 3.2 From V4 (gpt55, 414 LOC) — concrete module path

V4's §11 proposes the explicit target module path:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

with two specific Lean records:

* `TreeMCSPPrefixAmbientLength` — captures `M`, `tableLen_le_M`, `witnessBits_le_M`
* `TreeMCSPPrefixRuntimeBudget` — captures runtime obligations as real fields (not `True` placeholders)

This naming proposal **complements V1's structure design**: V1 provides the field signatures, V4 provides the file path and record-name conventions.

### 3.3 From V2 (gpt55, 379 LOC) — compact verdict statement

V2's executive verdict (`Executive verdict` section, before any signature dive) is the **clearest one-paragraph statement** of the load-bearing distinction:

> `TreeCircuitWitnessCodec.verifiesDecidable` performs truth-table agreement by finite universal quantification over `BitVec n`, so the direct verifier is exponential in the target parameter `n`. For the tree-MCSP target, the instance component has length `problem.instanceBits n = tableLen n = 2^n`. Therefore the same truth-table scan can be polynomial in an ambient input length `M(n)` whenever the serialization convention proves `tableLen n ≤ M(n)` and the remaining work is polynomial in `M(n)`.

This framing is the cleanest summary of the R1-B2 finding. Quoted here for operator reference.

### 3.4 Common cross-report finding: the `NP_TM` bridge gap

All four reports independently identify the **architectural blocker**:

* pnp3 exposes `NP_TM` (a concrete Turing-machine verifier definition).
* pnp4 has staged `Prop`-valued runtime budget fields.
* **No compiler / adapter exists** from staged budget records to `NP_TM`.

The four reports differ slightly in how they characterize this gap:

| Report | Framing |
| --- | --- |
| V1 | "Local arithmetic facts can land; concrete computational model still required" |
| V2 | "Pnp3 `NP_TM` is the target; pnp4 has no TM-level parser/verifier or runtime compiler" |
| V3 | "Largest global blocker is the missing bridge from staged R1-B budget predicates to existing `NP_TM` verifier interface" |
| V4 | "Polynomial-time formalism status: global bridge to `NP_TM` missing" |

**Operator finding:** the `NP_TM` bridge is the architectural decision that future contract_expansion work must address, **regardless of which R1-B-cadence task is dispatched next**. R1-B2a-style work on arithmetic and budget structure does not bridge this gap; it only stages obligations more cleanly.

---

## 4. Honest meta-assessment

We now have **9 packs** in the contract_expansion + FP3b series:

```
V2-A / V2-A.1 / V2-B / V2-D  (filter design, closed via NOGO chain)
fp3b6 Family A               (STALLED, double-bind)
fp3b7 Family B               (RED-LIGHT, double-bind)
fp3b8 direct MCSP            (RED-LIGHT, wrapper-around-contract)
contract_expansion D0/D0.1   (INCONCLUSIVE → R1-A/B/B1 spawn)
R1-A C_DAG_Adapter           (LANDED, plumbing)
R1-B PrefixExtensionLanguage (LANDED, definition + staged budget)
R1-B1 PrefixExtensionLanguageNP (LANDED, codec-case Decidable)
R1-B2 (this slot)            (LANDED report; staged again, NP_TM bridge missing)
```

**The diminishing-returns pattern is now clearly visible.** Each pack has produced less marginal progress toward `ResearchGapWitness` than the previous:

| Pack | New positive content |
| --- | --- |
| R1-A | first Lean theorem-class result in track; pure plumbing |
| R1-B | language definition + 9-field staged budget; no NP claim |
| R1-B1 | codec-case `relation_decidable` real Lean theorem; 4 of 5 budget fields still staged |
| R1-B2 | **markdown only; no new Lean theorem**; reports converge on a known architectural blocker |

R1-B2 is the **first pack in this series that produced no new Lean theorem-class content**. The reports are good — they correctly diagnose the architectural gap — but the gap they identify (`NP_TM` bridge) is **not addressable by another R1-B-cadence dispatch**. It requires either:

1. **A polynomial-time formalism investment in pnp4** (2–4 weeks; create a polynomial-time-bounded function predicate + machinery to bridge it to pnp3 `NP_TM`); or
2. **Acceptance** that contract_expansion stops at decidability level.

**This is the same diagnosis I gave in the R1-B1 operator review §10.** R1-B2's reports independently confirmed it from four parallel angles. The architectural decision is no longer avoidable by dispatching more R1-B-cadence tasks.

---

## 5. Three honest paths forward

### Path A — Dispatch R1-B2a (small Lean module from V1+V4 synthesis)

**Scope:** Write `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean` containing:

1. `treeMCSPPrefixAmbientLength` definition (from V1 §3).
2. `tableLen_le_treeMCSPPrefixAmbientLength` lemma (from V1 §3).
3. `TreeMCSPPrefixAmbientLength` record (from V4 §11) wrapping the above with explicit `witnessBits_le_M` field.
4. `TreeMCSPPrefixRuntimeBudget` record (from V1 §8) with mixed arithmetic-theorem and `Prop`-placeholder fields.

**Authorized scope:** arithmetic and structure definitions only. No NP membership claim. No `Classical.choose`. No bridge to `NP_TM`. Either landed module or structured failure acceptable.

**Pros:**
- Discharges the most-tractable arithmetic content from V1.
- Provides Lean infrastructure that a future `NP_TM` bridge can consume.
- Small scope (likely 100–150 LOC); low cost.

**Cons:**
- Does **not** advance toward `ResearchGapWitness` measurably.
- Adds another infrastructure layer without addressing the architectural gap.
- Continues the diminishing-returns pattern.

**Pessimistic prior:** ~70% clean landing (arithmetic is straightforward); ~25% structured failure on naming/architecture choices; ~5% scope creep.

### Path B — Scoping decision on polynomial-time formalism

**Scope:** Operator-side markdown decision document: "Do we invest in a polynomial-time formalism for pnp4?". Survey existing Mathlib polynomial-time machinery (if any), assess fit with pnp4 `CircuitFamilyClass`, estimate 2–4 week roadmap.

**Pros:**
- Addresses the actual architectural blocker.
- Defers Lean work until the operator decides on the bigger investment.
- Honest about the gap.

**Cons:**
- Not advancement in the usual sense — it's a strategic decision document.
- May conclude "too expensive; stop the track".

**Pessimistic prior:** ~60% operator concludes "too expensive, stop the track"; ~30% operator decides to invest in polynomial-time formalism; ~10% INCONCLUSIVE (needs Mathlib expertise to scope).

### Path C — Stop / step back, document FP3b track meta-retrospective

**Scope:** Single markdown report covering the full 9-pack arc. Document what was learned (5 NoGos + 2 double-binds + interface infrastructure for contract_expansion) and what remains unsolved (architectural polynomial-time gap; no self-reduction in literature). Recommend acceptance.

**Pros:**
- Honest framing.
- Closes the loop on FP3b + contract_expansion as scientific artifacts.
- Preserves the kill-machine framework's lesson: many routes died informatively.
- Frees the operator to choose entirely different research directions.

**Cons:**
- Does not advance toward `ResearchGapWitness`.
- But neither does Path A or B in any direct sense.

**Pessimistic prior:** 100% clean landing (it's a retrospective).

---

## 6. Operator-recommended path

**My honest recommendation: a hybrid of Paths A and C.**

### 6.1 Tactical: dispatch the small Lean module (Path A)

Do dispatch R1-B2a as the synthesized module. Reasons:

* It's cheap and finishes the R1-B-cadence cycle cleanly.
* The V1+V4 synthesis is **ready to drop into Lean** — no further design work needed.
* Either outcome (clean landing or structured failure) leaves the codebase in a better-documented state for any future revisit.

### 6.2 Strategic: write the FP3b track meta-retrospective (Path C)

In parallel or after R1-B2a lands, write the meta-retrospective. This is the honest closure of the FP3b epoch. **Path B (polynomial-time formalism scoping) can wait** — it should only be opened if a future operator decides to revive the contract_expansion route.

### 6.3 Concrete proposed dispatch shape for R1-B2a

```text
seed_packs/source_search_contract_expansion_R1B2a_runtime_module/
  README.md, WORKER_PROMPT_R1B2a.md
  Allowed scope:
    - pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
    - lakefile.lean (one Glob.one line)
    - test surface registration (similar to R1-A and R1-B1 patterns)
  Required content:
    - treeMCSPPrefixAmbientLength def + tableLen_le lemma
    - TreeMCSPPrefixAmbientLength record
    - TreeMCSPPrefixRuntimeBudget record with V1 §8 field shape
    - At least one arithmetic field discharged (tableLen_le_M)
  Forbidden:
    - No NP membership claim
    - No Classical.choose
    - No bridge to NP_TM
    - No R1-C work
  Acceptance:
    - Outcome A: module + at least one arithmetic discharge + structured budget
    - Outcome B: structured failure with specific blocker
```

**Pessimistic prior on R1-B2a:** ~70% clean landing of arithmetic + structure. The remaining 30% would be informative.

### 6.4 Why NOT recommend `open_R1C_shared_DAG_extraction`

Opening R1-C now would inherit the fp3b8 wrapper-around-unexpanded-contract pattern. R1-B2's reports confirm the architectural gap (`NP_TM` bridge missing); R1-C cannot honestly produce `VerifiedNPDAGLowerBoundSource` with the gap unbridged.

### 6.5 Why NOT recommend `red_light_contract_expansion`

R1-B2a (Path A) is a cheap follow-up that finishes the R1-B-cadence cleanly. Hard red-light would discard the option to dispatch this small module.

---

## 7. Output summary

```
Task: R1-B2 four-way parallel-dispatch comparative review and synthesis
Handle: claudeopus
Branch: main
Versions reviewed:
  V1 = PR #1283, commit 6536f4c, gpt55, 548 LOC
  V2 = PR #1286, commit 6eeee02, gpt55, 379 LOC
  V3 = PR #1284, commit 1ff5ab6, codex, 584 LOC
  V4 = PR #1285, commit a868e9a, gpt55, 414 LOC
Review file: seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/reports/R1B2_four_way_review_and_synthesis_claudeopus.md
Verdict: merged_V1 as canonical; closed V2/V3/V4 with comments
Common diagnosis (all 4 unanimous):
  - verifiesDecidable is exponential in n, plausibly polynomial in M(n)
  - tableLen n = 2^n ⊆ instanceBits n; loop count linear in M(n) if tableLen n ≤ M(n)
  - PrefixExtensionLanguage_in_NP cannot be honestly claimed in current repo
  - Architectural blocker: no bridge from pnp4 staged budget predicates to pnp3 NP_TM
  - R1-C remains gated
Why V1 won:
  1. §8 concrete TreeMCSPPrefixRuntimeBudget structure design (Lean-ready)
  2. §3 explicit M(n) decomposition + arithmetic lemma signature
  3. §11 concrete R1-B2a next-step proposal with 4 sub-deliverables
V2/V3/V4 unique strengths preserved in synthesis:
  - V3: thoroughest signature audit (§2, 215 LOC) — best reference for future workers
  - V4: concrete module file path PrefixExtensionLanguageRuntime.lean + record names
  - V2: cleanest one-paragraph load-bearing distinction statement (executive verdict)
Honest meta-assessment:
  - 9 packs in contract_expansion + FP3b series; pattern of diminishing returns now clear
  - R1-B2 is the first pack in series with NO new Lean theorem-class content
  - Architectural NP_TM bridge gap not addressable by another R1-B-cadence dispatch
Recommended action: HYBRID of Path A + Path C
  Tactical: dispatch R1-B2a (small Lean module synthesized from V1+V4) — cheap closure
  Strategic: write FP3b track meta-retrospective — honest closure of the epoch
  Path B (polynomial-time formalism scoping) deferred unless future operator revives track
Pessimistic priors:
  R1-B2a clean landing: ~70%
  R1-C clean landing (if eventually attempted): <30% UNCHANGED — the literature does not contain the required PpolyDAG-size self-reduction in the right form
Actions taken:
  - V1 merged at 2a9e1e65
  - V2/V3/V4 closed with explanatory comments
Commands run:
  - git fetch / sync to main → 2a9e1e6
  - read all 4 reports (1925 LOC total)
  - mcp__github__merge_pull_request 1283
  - mcp__github__update_pull_request 1284, 1285, 1286 (state=closed)
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output
  - lake build / scripts/check.sh → NOT RUN (markdown-only synthesis; no Lean changes)
Scope violations: none
```
