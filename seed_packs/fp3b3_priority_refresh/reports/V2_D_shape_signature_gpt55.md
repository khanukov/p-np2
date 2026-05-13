# V2-D shape/provenance signature review

Route: V2-D shape/provenance signature  
Handle: gpt55  
Report path: `seed_packs/fp3b3_priority_refresh/reports/V2_D_shape_signature_gpt55.md`  
Verdict: reject_route  
NOGO-000008 stress-test result: attack adapts; tautological full-support padding changes V2-D status while preserving semantics  
NOGO-000009 stress-test result: normalize-then-filter self-defeats or collapses the only displayed provenance signal  
Non-vacuity assessment: the stated parity/XOR honest family is not established and appears false for the given exact occurrence signature  
Recommended next action: reject_route  
Commands run: `./scripts/check.sh` (hit coordinator HTTP connection reset at Step 12.e), `./scripts/check.sh` (passed), then `./scripts/check.sh` after wording-only cleanup (same Step 12.e coordinator reset recurred)  
Scope violations: none

## 1. Route definition

V2-D is currently a Phase-1/audit sketch, not a lower-bound theorem, not a promoted guard, and not a bridge to the main target.  The sketch defines one syntactic statistic, `FormulaCircuit.inputOccurrences`, which recursively counts how many times a distinguished ambient input coordinate occurs in the displayed formula tree.  It then defines `ProvenanceFilter_v2_V2_D_GPT55` on a strict `InPpolyFormula` witness by requiring:

1. for every positive length `n`, the displayed formula has full ambient support, i.e. support cardinality exactly `n`; and
2. for every positive length `n`, coordinate `0` occurs syntactically exactly once in `w.family n`.

The intended intuition is that full support rejects sublinear prefix-window hardwiring, while the read-once coordinate-0 signature is meant to detect provenance information beyond support cardinality.

Adversarial classification: **displayed-syntax-sensitive, not robustly semantic/provenance-sensitive**.

Reason:

- The predicate is evaluated directly on the concrete `FormulaCircuit` tree stored in an `InPpolyFormula` witness.
- The occurrence count ignores semantic equivalence of formulas: equivalent formulas with duplicated, eliminated, or padded occurrences can change the predicate value.
- The distinguished coordinate is hard-coded as ambient coordinate `0`, so harmless renamings or common formula encodings can change acceptance even when the computed language is unchanged.
- There is no canonical provenance object, no semantic quotient, no invariance under equivalence-preserving rewrites, and no proof that the displayed occurrence count is stable under ordinary formula transformations.

So V2-D does use information beyond support cardinality, but that information is still **raw displayed syntax**, not robust provenance.

## 2. NOGO-000008 stress test

**Result: the NOGO-000008 attack adapts.**

The direct V2-A rewrite `C ↦ C ∧ (x₀ ∨ ¬x₀)` is not the best attack against V2-D, because V2-D requires `inputOccurrences 0 = 1`; adding the seed on `x₀` would add two more displayed occurrences of coordinate `0` and usually make the exact-count clause fail.

However, V2-D's first conjunct creates a stronger opening: it demands full support.  Given the same sublinear-support hardwiring family underlying the Nat.log2 prefix-AND adversary, choose tautological padding over every missing ambient coordinate, not over coordinate `0`:

```text
C_n  ↦  C_n ∧ ⋀_{i ∉ support(C_n)} (x_i ∨ ¬x_i)
```

For the prefix-AND family at positive lengths:

- `C_n` computes the same hardwired prefix-window language as before.
- The padding is a conjunction of tautologies, so the Boolean function is unchanged.
- The displayed support becomes the full ambient set `{0, …, n-1}`.
- Coordinate `0` already appears once in the prefix conjunction when the prefix width is positive.
- The padding can avoid coordinate `0`, so `inputOccurrences 0` remains exactly `1`.
- The formula size stays linear or near-linear in `n`, hence remains harmless for `InPpolyFormula` packaging.

This is exactly the semantic failure mode recorded by NOGO-000008, with the seed generalized from one mixed tautology to a full-support tautology blanket.  V2-D would reject the unpadded prefix-window witness because support is sublinear, but it appears to accept a semantically identical padded witness whose only new information is tautological syntax.

Therefore V2-D does **not** prove that the underlying Boolean-function family is non-hardwired.  It only proves that one displayed representation lacks the required full-support/read-once shape.

## 3. NOGO-000009 stress test

A normalize-then-filter patch would likely self-defeat for V2-D as well.

To defeat the padding attack above, a normalizer must identify and delete tautological factors such as `(x_i ∨ ¬x_i)` and simplify `C ∧ true` back to `C`.  But if it does so, then the padded adversary normalizes back to the original sublinear-support prefix-window formula, which fails V2-D only because V2-D was using the displayed padding as evidence.  Conversely, if the normalizer refuses to delete those tautologies, NOGO-000008-style padding remains accepted.

More importantly, V2-D's only non-cardinality signal is the exact displayed occurrence count of coordinate `0`.  Any structural normalizer strong enough to remove tautological padding or to canonicalize common Boolean identities will also change occurrence counts in honest formulas.  The V2-A.1 barrier shows the same pattern: a context-uniform structural normalizer that eliminates the seed required to patch NOGO-000008 also eliminates the syntactic seed needed by the route's own accepted witness, causing the filter to reject its own non-vacuity example.

For V2-D, the analogous fork is:

- keep exact displayed occurrences untouched, and the route is representation-sensitive and padding-vulnerable;
- normalize displayed occurrences, and the predicate no longer has a stable honest read-once signature without a new semantic/canonical representation theorem.

Thus a normalize-then-filter patch is not a small repair.  It would require replacing the route with a semantic quotient or a proven canonical provenance invariant, which is outside the current V2-D sketch.

## 4. Non-vacuity

**Assessment: hold would be too generous; the stated non-vacuity story is currently not credible.**

The sketch claims that a standard parity/XOR family on all `n` inputs, encoded by the identity

```text
xor a b = (a ∧ ¬b) ∨ (¬a ∧ b)
```

has every input in support and coordinate `0` exactly once.

This claim appears false for the available `FormulaCircuit` basis (`const`, `input`, `not`, `and`, `or`):

- The displayed XOR identity contains `a` twice and `b` twice, once positively and once under negation.
- Folding parity from binary XORs duplicates previous subformulas further, so coordinate `0` is not read-once in the displayed formula.
- More conceptually, parity on more than one variable is not a read-once formula over the usual De Morgan tree basis; exact read-once occurrence is a very strong syntactic property.

V2-D may admit trivial full-support read-once families, for example an all-input conjunction or disjunction, but those are not meaningful honest lower-bound/provenance families.  They also illustrate the route's weakness: the filter can be satisfied by very simple syntax and by tautologically padded hardwiring, not by a robust provenance guarantee.

So the current non-vacuity claim should be treated as **unproved and likely wrong as written**.  Any future non-vacuity attempt would need to specify an actual `FormulaCircuit` family and prove the exact occurrence count, rather than relying on informal parity/XOR intuition.

## 5. Support-cardinality barrier

V2-D likely avoids the formal `IsSupportCardinalityOnly` predicate, but only in the weak syntactic sense.

It uses information beyond the support-cardinality profile: the exact displayed occurrence count of coordinate `0`.  Two witnesses can have the same support-cardinality profile at every length while differing on whether coordinate `0` occurs once, twice, or not at all.  Therefore V2-D is not merely a function of `n ↦ |support(w.family n)|`.

However, this does **not** rescue the route.  The additional information is not semantic provenance; it is just representation-dependent multiplicity in one chosen formula tree.  NOGO-000007 rules out support-cardinality-only filters, and V2-D steps outside that formal class, but NOGO-000008 then attacks the raw syntactic dependence directly.

## 6. Recommendation

**Recommendation: `reject_route`.**

Reasons:

1. V2-D is displayed-syntax-sensitive rather than semantic/provenance-sensitive.
2. A NOGO-000008-style harmless rewrite adapts by adding tautological full-support padding over missing variables while preserving the exact coordinate-0 count.
3. A normalize-then-filter patch faces the same NOGO-000009 self-defeat: either tautologies remain and the attack survives, or normalization deletes/changes the exact syntax that the route needs.
4. The stated parity/XOR non-vacuity example appears false for the concrete formula basis and exact occurrence-count predicate.
5. Although V2-D is not support-cardinality-only, the extra signal is too brittle to justify Phase-2 dispatch.

Recommended next action: archive V2-D as rejected for priority refresh purposes.  Any successor should abandon exact displayed occurrence counts and start from a semantic equivalence-class/canonical-provenance formulation with an explicit invariance theorem against tautological padding.
