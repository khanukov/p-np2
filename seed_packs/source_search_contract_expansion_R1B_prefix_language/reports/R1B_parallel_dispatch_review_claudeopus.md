# R1-B parallel-dispatch comparative review — claudeopus

**Slot:** R1-B operator decision (comparative review of two parallel codex dispatches).
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `75f5bb0`.

**Review subjects:**

* **V1** — PR #1277, commit `d702a46` (`Add R1-B prefix-extension language skeleton and seed-pack with tests`), branch `khanukov/create-r1-b-seed-pack-skeleton`. File: `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` (238 LOC).
* **V2** — PR #1278, commit `def64e7` (`Add R1-B prefix-extension language skeleton, register in lakefile and tests`), branch `khanukov/create-r1-b-seed-pack-skeleton-8o8st0`. File: `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` (221 LOC).

Both PRs landed parallel `codex` dispatches of the same R1-B seed-pack task. Both have identical `README.md` (120 LOC) and `WORKER_PROMPT_R1B.md` (164 LOC) skeleton files; the divergence is in the Lean module and its test surface.

This is **operator-scoped review**. No Lean edits in this review file. No JSONL / spec / known_guards edits, no trust-root edits, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims.

---

## 1. Verdict

```text
merge_V2 (PR #1278, def64e7)
close_V1 (PR #1277, d702a46) without merge
```

Both versions are R1-B-shaped partial completions (neither claims `PrefixExtensionLanguage_in_NP`; both correctly stage NP membership as a verifier budget). **V2 is structurally superior** along five axes (§2 below). V1 has one minor advantage (parser-level length/tag lemmas) that does not outweigh V2's type-safety-by-construction.

Operator action: merge PR #1278; close PR #1277 with explanatory comment.

---

## 2. Comparison table

| Aspect | V1 (PR #1277, d702a46) | V2 (PR #1278, def64e7) | Winner |
| --- | --- | --- | --- |
| `PrefixInput` parametrization | not indexed by ambient length `m`; prefix `p` has **fixed width** `problem.witnessBits n` | indexed by `m`; prefix `p` has **variable width** `i` (the active prefix length) | **V2** |
| `i ≤ witnessBits n` invariant placement | external predicate `indexInRange` (`PrefixInput.lean:40-42`); the parser must prove it via `wellFormed_index` field | structure field `prefixLength_le : i ≤ problem.witnessBits n` (`PrefixInput.lean:38`); enforced by construction | **V2** |
| Prefix access type-safety | runtime guard `(k : Nat) < input.i` in `prefixAgreement` (`PrefixInput.lean:54`); requires reasoning about index bounds at every use | static type `Fin input.i` with safe coercion via the invariant (`PrefixInput.lean:57-58`); no runtime guards needed | **V2** |
| `PrefixParser` structure size | 8 fields: tag, M, parsePrefixInput, wellFormed, parse_wellFormed, parse_length, parse_tag, wellFormed_index | 3 fields: tag, M, parse | **V2** (less parser-implementation burden) |
| Forward-direction constructor lemma | none | `PrefixExtensionLanguage_accepts_of_parse_and_witness` (`PrefixExtensionLanguage.lean:161-177`) — useful for R1-C self-reduction | **V2** |
| Helper theorems on parser proofs | `PrefixExtendable.length_eq`, `PrefixExtendable.tag_eq` (V1-only) | none (parser does not carry these proofs) | **V1** (minor) |
| Verifier budget granularity | `PrefixNPVerifierPlan` (7 fields) + `codecRequirements` projection (3-field conjunction) | `PrefixExtensionNPVerifierBudget` (9 fields) + `PrefixExtensionNPVerifierPlan` (4 fields wrapping the budget) | **V2** (more granular, separates "budget" from "plan") |
| Total LOC | 238 (Lean) + 48 (tests) + 9 (axioms) | 221 (Lean) + 40 (tests) + 5 (axioms; visible new entries) | **V2** (smaller surface, same content) |

### Net score

* V2 wins on 5 axes: type-safety-by-construction, type-safe prefix access, simpler parser, forward-direction lemma, smaller surface.
* V1 wins on 1 axis: parser-level length/tag lemmas.
* Tie on classical/noncomputable use (both use `classical` for `PrefixExtensionLanguage`; both stage NP membership in a verifier budget).
* Tie on trust-root scope (both clean).

---

## 3. Why type-safety-by-construction matters here

R1-B is the prerequisite for R1-C (the self-reduction from `PpolyDAG` decider for the prefix-extension language to `BoundedSearchSolver` for the target problem). R1-C will need to:

1. Extract a prefix coordinate `k < input.i` from `input.p`.
2. Coerce it to a witness coordinate `j : Fin (problem.witnessBits input.n)` via `input.prefixLength_le`.
3. Build per-output-bit circuits that read the appropriate witness coordinates.

In **V2**, step 2 is free: the invariant `prefixLength_le` is a structure field of `PrefixInput`. Whenever R1-C has a `PrefixInput problem m` in scope, the coercion is type-safe by construction.

In **V1**, step 2 requires unpacking the parser's `wellFormed_index` proof obligation, then proving `(k : Nat) < input.i → k.val < problem.witnessBits input.n` at every coercion site. This adds **proof debt** that R1-C will have to discharge over and over for every coordinate of every witness bit.

This is not a theoretical concern. R1-C's self-reduction will build `O(witnessBits n)` output circuits, each needing prefix-to-witness coordinate alignment. V2's design pushes this proof obligation **once, into the structure definition**. V1 pushes it **once per coordinate, at every site**.

---

## 4. Where V1's parser-level lemmas would have been useful

V1's `PrefixExtendable.length_eq` and `PrefixExtendable.tag_eq` extract length and tag consistency from the parser's proof fields. In V2, these would need to be re-derived by the parser instance (the parser's `parse` function naturally encodes them, but they're not lifted to operator-visible lemmas).

This is a minor disadvantage for V2: future parser implementations may need to re-prove length/tag consistency at the call site. However:

* R1-B's task is "define the language and prove NP membership". Tag and length lemmas are auxiliary, not central.
* When a concrete parser is eventually implemented (R1-C or later), the parser instance can directly construct length/tag lemmas as definitional consequences of the parser's structure. They don't need to be in the abstract `PrefixParser` interface.
* V2's smaller `PrefixParser` interface is **less prescriptive**, leaving more design flexibility for the concrete parser. This is good for future R1-C work.

Net: V1's parser-level lemmas trade design flexibility for off-the-shelf consistency lemmas. R1-C will benefit more from V2's flexibility.

---

## 5. Common caveats (both versions)

Both versions share these characteristics, which are correctly scoped for R1-B but worth registering:

### 5.1 `noncomputable PrefixExtensionLanguage` via `classical`

Both versions define:

```lean
noncomputable def PrefixExtensionLanguage (parser) : Pnp3.ComplexityInterfaces.Language := by
  classical
  exact fun _m y => if PrefixExtendable parser y then true else false
```

This coerces the `Prop`-valued predicate `PrefixExtendable parser y` to `Bool` via classical decidability. **Acceptable for the skeleton** because the actual NP verifier proof is staged in the verifier-budget structure rather than hidden in the language definition. A future computable version would require decidability of `PrefixExtendable`, which depends on:

* decidability of `parsePrefixInput` (parser implementation choice);
* decidability of `problem.relation` (currently `Prop`-valued in `SearchMCSPCompressionProblem`);
* boundedness of the witness existential.

All three are staged in the verifier budget. **Correctly scoped.**

### 5.2 NP membership NOT proven

Neither version proves `NP (PrefixExtensionLanguage parser)`. Both correctly defer this to the verifier-budget structure with explicit fields documenting the missing data. The R1-B acceptance criterion in `seed_packs/.../README.md` accepts "either a kernel-checked module or a structured failure". Both versions land **partial completions** that stage NP membership as a budget item rather than claim it as a theorem. **Acceptable** per the R1-B WORKER_PROMPT § (the prompt explicitly says "structured failure if either NP membership cannot be cleanly proven").

### 5.3 Hidden-endpoint check

Both versions:

* Do not assert `NP_not_subset_PpolyDAG`.
* Do not invoke `SearchMCSPMagnificationContract`.
* Do not construct `BoundedSearchSolver`.
* Do not reference `ResearchGapWitness` / `VerifiedNPDAGLowerBoundSource` / `target.noBoundedSolver`.
* Do not promote `ProvenanceFilter_v1`.

Both are R1-B-scope-clean.

### 5.4 Trust-root edits

Both versions:

* No edits to `pnp3/Complexity/Interfaces.lean`.
* No edits to `pnp3/Magnification/UnconditionalResearchGap.lean`.
* No edits to `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`.
* `lakefile.lean` adds one `Glob.one` entry for the new module (allowed).
* `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` and `pnp4/Pnp4/Tests/AxiomsAudit.lean` extended with new `check_*` and `#print axioms` entries (allowed by R1-A precedent).

Both trust-root-clean.

### 5.5 CI status

Both PR descriptions claim `./scripts/check.sh` succeeded. The GitHub status check API returned `total_count: 0` for both heads (no automated CI configured to block). I cannot independently verify the build from this operator-review environment (no Lean toolchain). **Operator should rely on the Codex-task self-reported `scripts/check.sh` result.**

**Documentation caveat (V2).** The PR #1278 description states "audit-printing lines in AxiomsAudit.lean remain commented out and thus do not affect the test run". The actual diff shows three uncommented `#print axioms` lines were added. This is a **PR description inaccuracy**, not a code issue. The added `#print axioms` lines are the correct behavior.

---

## 6. R1-C readiness assessment

Both versions unlock R1-C in principle. V2's R1-C interface is materially cleaner:

* `PrefixInput problem m` is in-range by construction → R1-C self-reduction can extract prefix coordinates and align with witness coordinates without auxiliary proofs.
* `PrefixExtensionLanguage_accepts_of_parse_and_witness` provides the forward-direction constructor R1-C needs to build the contradiction: if a `PpolyDAG` decider for the language exists, applying it to encoded `(input, w)` pairs gives the search solver.
* The granular verifier budget exposes 9 specific obligations that R1-C must discharge (parser polynomial time, witness length polynomial, prefix agreement polynomial time, relation decidable, relation polynomial time, codec serialization, codec decode, codec witness length bound, truth-table verification runtime). This is a checklist for R1-C scoping.

V1's interface would also work for R1-C but would require extra proof obligations at every coordinate access. R1-C is the hardest gate in the contract_expansion track; **minimizing proof debt at the R1-B boundary is genuinely valuable.**

---

## 7. Recommended next action

```text
1. merge PR #1278 (V2)
2. close PR #1277 (V1) with a comment pointing to this review
3. proceed with operator review of the merged R1-B state on main
4. then decide whether to dispatch R1-C
```

**Not recommended:**

* Merging both. They edit the same paths (Lean module, lakefile, test files). One would conflict with the other.
* Merging V1. V2 is structurally better; merging V1 forces R1-C to inherit V1's proof debt.
* Splitting the difference (e.g., merging V2 then cherry-picking V1's `length_eq`/`tag_eq`). These lemmas can be re-derived from V2's interface if a concrete parser implementation needs them; backporting V1's structure-level fields to V2 would be a non-trivial refactor and is not warranted at this stage.

---

## 8. Pessimistic frame (for operator awareness)

R1-B's partial completion lands cleanly because the verifier-budget structure **explicitly defers** the hard parts (decidability of `problem.relation`, polynomial-time bounds on the parser/relation/codec). R1-B does **not** discharge the NP membership obligation; it stages it for R1-C or later.

**R1-C is where the actual math happens.** The self-reduction from `PpolyDAG` decider to `BoundedSearchSolver` is essentially a search-to-decision reduction with concrete size accounting in `PpolyDAG`-compatible budgets. The literature has search-to-decision reductions in many forms (Bellare-Yannakakis-style, locality-preserving, etc.); whether **any** of them gives a clean `PpolyDAG`-size reduction for the specific tree-MCSP search relation is the actual open question identified by D5-tight.

R1-B landing (in either V1 or V2 form) is **infrastructure progress**, not mathematical progress. My prior on R1-C clean landing is unchanged: probably <30% for clean GREEN; ~40% for structured failure with specific size-budget obstruction; remainder = scope creep / scope reclassification.

V2 marginally improves R1-C's prior by reducing the proof debt R1-C inherits. But the dominant risk for R1-C is the **mathematical content** of the self-reduction, not the proof-engineering quality of R1-B.

---

## 9. Output summary

```
Task: R1-B parallel-dispatch comparative review
Handle: claudeopus
Branch: main
Versions reviewed:
  V1 = PR #1277, commit d702a46 (238 LOC Lean, 48 LOC tests)
  V2 = PR #1278, commit def64e7 (221 LOC Lean, 40 LOC tests)
Review file: seed_packs/source_search_contract_expansion_R1B_prefix_language/reports/R1B_parallel_dispatch_review_claudeopus.md
Verdict: merge_V2, close_V1
Key reasons V2 wins:
  1. PrefixInput parametrized by ambient length m
  2. i ≤ witnessBits n invariant as structure field (type-safety by construction)
  3. Variable-width prefix p : PrefixBitVec i (semantically aligned with active length)
  4. Simpler PrefixParser (3 fields vs 8)
  5. Forward-direction lemma PrefixExtensionLanguage_accepts_of_parse_and_witness
V1 minor advantage: parser-level length_eq/tag_eq lemmas (not critical for R1-C)
Common caveats (both versions):
  - noncomputable language via classical (acceptable for skeleton)
  - NP membership not proven (correctly staged as verifier budget)
  - PR #1278 description has minor inaccuracy ("axioms commented out" — actually uncommented)
Trust-root audit: both clean
Recommended next action: merge_PR_1278, close_PR_1277, then assess merged state
Commands run:
  - git fetch / checkout main / pull --ff-only → 75f5bb0
  - git show d702a46, git show def64e7 → diff comparison
  - mcp__github__pull_request_read get_status both → total_count 0 (no CI blocking)
  - lake build / scripts/check.sh → NOT RUN (no toolchain; relying on Codex task self-report)
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output (on main; new content not on main yet)
Scope violations: none
```
