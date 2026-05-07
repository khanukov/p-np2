# Review — `V2_A_gpt55`

Reviewer handle: `gpt55`

## 1. Verdict

**Verdict: `approve_with_changes`.**

This direction is **not** killed by NOGO-000007, because the proposed predicate is not support-cardinality-only: it inspects syntactic gate counts, syntactic depth, and positive OR/NOT occurrence once support has size at least two.  That is enough to justify proceeding to Phase 2's first theorem, `ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only`.

However, the Phase-1 non-vacuity paragraph should **not** be carried into Phase 2 as written.  It claims that parity, represented only with binary AND/OR/NOT through the expansion

```text
xor a b = (a ∧ ¬ b) ∨ (¬ a ∧ b)
```

has linearly many Boolean gates.  In the strict `FormulaCircuit` syntax this is a formula tree, not a DAG, and XOR composition duplicates subformulas.  A balanced parity construction over De Morgan gates is quadratic-size, not linear-size, so the advertised bound

```lean
booleanGateCount ≤ 16 * support + 16
```

is not plausibly true for all lengths.  Phase 2 may proceed only after replacing the parity non-vacuity target with a concrete linear-size mixed-gate full-support family.  My recommended replacement is the family

```text
seededPrefixAnd(n) =
  if n = 0 then true
  else if n = 1 then x₀
  else ((x₀ ∧ ¬x₁) ∨ (¬x₀ ∧ x₁)) ∧ x₂ ∧ ... ∧ xₙ₋₁.
```

This family is semantically simple but non-vacuity only needs a specific honest family that is not a bounded or sublinear hardwiring witness: it has full support for all `n ≥ 2`, unbounded support, positive OR/NOT counts for all `n ≥ 2`, and visibly linear gate count/depth.

## 2. NOGO-000007 self-test

**Result: NO — `ProvenanceFilter_v2_V2_A_gpt55` is not support-cardinality-only.**

The filter starts with the old unbounded-support condition, but the last three conjuncts are syntactic and can distinguish witnesses whose support-cardinality profiles are identical:

1. **Gate counts.**  The second conjunct bounds
   `booleanGateCount (w.family n)`, where `booleanGateCount` is the sum of syntactic NOT, AND, and OR counts.  Two length-`n` formulas can use the same support set, and hence have the same support cardinality, while one is a single conjunction and the other is a full truth-table expansion.  The filter can reject the latter by the `16 * support + 16` cap.
2. **Depth.**  The third conjunct bounds `FormulaCircuit.depth (w.family n)`.  This is also not determined by support cardinality: a balanced formula, a long chain, and a heavily padded formula may all mention exactly the same variables.
3. **OR/NOT presence.**  The fourth conjunct requires positive `orGateCount` and positive `notGateCount` whenever the support size is at least two.  This separates, for example, `x₀ ∧ x₁` from `(x₀ ∧ ¬x₁) ∨ (¬x₀ ∧ x₁)`: both have support cardinality two, but the prefix conjunction has zero OR and zero NOT gates while the XOR seed has both.

A Phase-2 proof of non-support-cardinality-only should exhibit two strict `InPpolyFormula` witnesses with the same support-cardinality profile, one satisfying the filter and one failing it.  A good witness pair is:

* accepting side: the replacement `seededPrefixAnd` full-support family above;
* rejecting side: a full-support monotone prefix-AND family `x₀ ∧ x₁ ∧ ... ∧ xₙ₋₁`, whose support profile is also `n` for all `n` but whose OR/NOT counts are zero for every `n ≥ 2`.

This directly demonstrates that the filter uses structural formula information beyond `n ↦ |support (family n)|`.

## 3. Non-vacuity assessment

**Sketch's named family:** parity.

**Assessment:** parity is concrete and named, but the stated gate-count justification is not plausible in the current syntax.  `FormulaCircuit` is a tree syntax with only `const`, `input`, `not`, `and`, and `or` constructors.  The standard XOR expansion duplicates its two input formulas.  Therefore an iterated or balanced parity-over-AND/OR/NOT implementation is not expected to satisfy a uniform linear Boolean-gate cap.  The depth claim is plausible, but the gate-count claim is the blocker.

**Phase-2 replacement family:** `seededPrefixAnd` as defined in the verdict.  It is concrete, full-support, and admits a straightforward proof strategy:

* support is all of `Fin n` for `n ≥ 2`, hence support cardinality is unbounded;
* Boolean gate count is linear: one XOR seed contributes a constant number of gates, each additional conjunct contributes one AND gate;
* depth is linear under a right- or left-associated conjunction chain, and therefore below `8 * support + 8`;
* OR and NOT counts are already positive in the XOR seed for every `n ≥ 2`.

## 4. Five-paragraph review

### 4.1 Excludes NOGO-000001

The paragraph is directionally sound but should be formalised in Phase 2 as a bounded-support exclusion lemma, not as a vague reference to overbroad provenance.  The current first conjunct rejects witnesses whose support cardinality is bounded across all lengths.  That is the relevant shape of the singleton/fixed-slice truth-table hardwiring obstruction behind NOGO-000001.  Phase 2 should avoid claiming that the filter refutes `OverbroadUniformProvenance` in all possible incarnations; instead, prove the concrete bounded-support theorem and connect it to the NOGO-000001 hardwiring witness shape if the existing interfaces expose enough structure.

### 4.2 Excludes NOGO-000004/000005

This paragraph is sound and is the strongest part of V2-A.  The prefix-AND adversary has unbounded sublinear support, so cardinality alone cannot exclude it.  But the Phase-1 filter requires positive OR and NOT counts whenever support cardinality is at least two.  The canonical prefix-AND syntax has no OR gates and no NOT gates, so it fails once `Nat.log2 (n + 1) ≥ 2`.  Phase 2 should prove this by showing the adversary witness would force `0 < orGateCount (...)` and/or `0 < notGateCount (...)` at such an `n`, contradicting the syntactic recursion for `prefixAnd`.

### 4.3 Excludes NOGO-000006

The idea is plausible but high-risk.  The `ttFormula` constructor is a full decision-tree expansion, so it should have exponentially many gates in the logarithmic width, while the filter allows only a linear function of width.  Phase 2 will need lower bounds on V2-A's `booleanGateCount` for `ttFormula`, or at least a lower bound on OR/AND count sufficient to exceed `16 * width + 16` for some large width.  Existing code already has an upper size bound for packaging; Phase 2 must not accidentally rely only on upper bounds.  If deriving a lower bound for every arbitrary all-essential payload is painful, the engineer should exploit the fixed recursive shape of `ttFormula`: the constructor adds one OR and two AND nodes at every decision-tree level independent of the payload semantics.

### 4.4 Non-vacuity

The paragraph names parity, which is good, but its key quantitative claim is wrong or at least not credible for the strict tree syntax.  Phase 2 should replace parity with `seededPrefixAnd`.  This is an `approve_with_changes` condition: do not spend Phase-2 effort trying to prove the false-looking linear parity gate bound unless the filter is first relaxed or the representation gains sharing/XOR gates, neither of which is allowed by this prompt.

### 4.5 Self-attack

The self-attack paragraph is honest and important.  V2-A is deliberately syntax-sensitive.  It excludes the concrete `ttFormula` syntax and the concrete `prefixAnd` syntax, but it does not exclude arbitrary all-essential functions that happen to have concise mixed-gate formulas.  That is acceptable for this seed pack if Phase 2's theorem names and statements are precise.  The Phase-2 engineer must not overclaim a semantic exclusion of all arbitrary payloads independent of representation.

## 5. Phase 2 readiness checklist

Phase 2 should produce exactly these new Lean files under
`pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`:

1. `Filter.lean` — re-state or import the V2-A filter and gate-count helpers from the sketch without changing the historical `Sketch.lean`.
2. `NotSupportCardinalityOnly.lean` — prove `ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only` by exhibiting same-support-profile witnesses separated by OR/NOT presence.
3. `ExcludesOverbroad.lean` — prove a bounded-support exclusion theorem for the NOGO-000001 hardwiring shape.
4. `ExcludesPrefixAnd.lean` — prove rejection of `FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2`.
5. `ExcludesArbitraryPayload.lean` — prove rejection of every `ArbitraryLogWidthTT.adversaryWitness_v_arbpayload F hF` using syntactic `ttFormula` gate-growth.
6. `NonVacuity.lean` — define `seededPrefixAnd` and prove `V2_A_admits_seededPrefixAnd`.
7. `Survivor.lean` — package non-support-cardinality-only, the three exclusions, and non-vacuity into a single integration theorem for review.

Allowed/forbidden scope should follow the seed-pack template: new V2-A files, lakefile wiring, optional smoke tests, one Phase-2 ledger append and critic report only after Phase 2 succeeds; no edits to the Phase-1 sketch, JSONL history, trust root, candidates, source theorems, gaps, or accepted filters.

## 6. Risks for Phase 2

* **Parity non-vacuity failure:** the original parity family likely violates the linear gate-count cap in tree syntax.  Use `seededPrefixAnd` instead.
* **Lower-bound burden for `ttFormula`:** existing artifacts emphasize support cardinality and upper size bounds.  V2-A needs lower bounds on its own gate counters for the concrete recursive `ttFormula` syntax.
* **Overbroad theorem ambiguity:** NOGO-000001 is about an overbroad provenance route and hardwiring witness shape, not necessarily a conveniently named strict `InPpolyFormula` witness with all needed support lemmas.  State the theorem at the strongest concrete level Lean supports without overclaiming.
* **Syntax sensitivity:** the filter does not semantically exclude concise adversarial payloads.  The formal statements must target the packaged `ttFormula`/`rename` witness from NOGO-000006.
* **Padding attacks:** a satisfying family can be made failing by adding redundant gates; conversely, a hardwiring family might be rewritten into a smaller mixed-gate syntax.  This does not refute the concrete exclusions but limits interpretation.
* **Kernel engineering:** proving same-support-cardinality witnesses for `¬ IsSupportCardinalityOnly` may require boilerplate `InPpolyFormula` packaging and polynomial bounds; keep witness families simple.
