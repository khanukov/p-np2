# V2-A natural-proofs audit — constructivity / largeness / usefulness

**Task:** V2-A natural-proofs audit  
**Handle:** gpt55  
**Seed pack target:** `fp3b3_1_v2a_natural_proofs_self_test`  
**Slot:** T2/T3 combined — constructivity / largeness / usefulness audit  
**Scope classification:** infrastructure / audit documentation only.  This report does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, introduces no lower-bound route theorem, and makes no P≠NP claim.

## 1. Verdict

**Verdict:** `representation_sensitive_escape_plausible`

V2-A is plainly **constructive as a predicate on displayed formula witnesses**: it checks support cardinality, Boolean-gate count, formula depth, and the presence of OR/NOT gates in the concrete `FormulaCircuit` stored in an `InPpolyFormula` record.

The Razborov-Rudich risk is therefore concentrated in **largeness and extensionality**.  The current evidence points away from a classical natural-proof property of Boolean functions and toward a **representation-sensitive syntactic provenance predicate**.  In particular, V2-A can reject a raw prefix-AND formula because it has no OR/NOT gates while accepting a semantically equivalent seeded version that conjoins the same prefix-AND with the tautological seed `(x₀ ∨ ¬x₀)`.

That is a plausible escape from the classical Natural Proofs barrier, because Razborov-Rudich natural properties are extensional properties of Boolean functions / truth tables.  But this is still only an audit conclusion: the repository should next make the representation-sensitivity theorem explicit and kernel-checked before treating the escape as a robust blocker-clearing fact.

## 2. Constructivity

**Constructivity result:** constructive as a predicate on formula witnesses.

V2-A is defined as a predicate

```lean
ProvenanceFilter_v2_V2_A_gpt55_phase2 {L : Language} (w : InPpolyFormula L) : Prop
```

on an explicit `InPpolyFormula` witness.  The filter has four visible conjuncts:

1. unbounded syntactic support cardinality;
2. `booleanGateCount (w.family n) ≤ 16 * |support| + 16` for every length;
3. `FormulaCircuit.depth (w.family n) ≤ 8 * |support| + 8` for every length;
4. if support cardinality is at least `2`, then both `orGateCount` and `notGateCount` are positive.

All of these inspect the finite formula tree `w.family n`.  For a fixed length `n` and a given formula witness, the checks are finite tree computations plus natural-number inequalities.  The code also proves syntactic helper theorems such as rename-invariance of AND/OR/NOT counts and exact gate counts for `ttFormula`, again by structural inspection of formulas.

Important nuance: this is **not** constructivity as an efficient truth-table predicate over all `2^n` Boolean functions.  It is constructivity relative to a supplied witness representation.  If one is handed the formula tree, the predicate is straightforwardly decidable/checkable by traversing that tree.  If one is handed only the truth table of the Boolean function, V2-A is not presented as a truth-table-only algorithm.

Specific constructivity observations:

- `booleanGateCount` is syntactic: it sums `notGateCount`, `andGateCount`, and `orGateCount` on the formula tree.
- `FormulaCircuit.depth` is syntactic: it depends on the displayed parse tree, not on the computed Boolean function.
- support cardinality is syntactic in this formalization: it is the support of the displayed formula, not a minimized essential-variable set of the underlying Boolean function.
- OR/NOT presence is syntactic: adding a tautological OR/NOT seed can change V2-A status without changing the represented Boolean function.

Conclusion: V2-A satisfies a strong witness-level constructivity property, but that fact alone does not make it a natural proof.  Classical naturality would require a constructive **large property of Boolean functions** that is useful against small circuits.

## 3. Usefulness

**Usefulness result:** useful against currently formalized hardwiring witnesses; not shown useful against all small circuits.

V2-A's formal survivor surface is useful in the narrow audit sense: it rejects the known formalized hardwiring/provenance failures that motivated this seed pack, while admitting at least one non-vacuity witness.

Required NOGO interactions:

- **NOGO-000001:** the single-slice / overbroad-uniform-provenance hardwiring pattern is covered only through the bounded-support route.  The operator review states that this covers the canonical witness shape, but not every possible `OverbroadUniformProvenance` instance.  So V2-A is useful against the known bounded-support manifestation, not a complete semantic refutation of all overbroad provenance.
- **NOGO-000004 / NOGO-000005:** V2-A rejects the canonical Nat.log2-window prefix-AND witness.  The proof uses the OR/NOT gate-mix requirement: at a small length with support size at least two, the concrete prefix-AND syntax has `orGateCount = 0`, contradicting the filter.  NOGO-000005 is the scope correction: this is a prefix-AND-specialized exclusion, not a theorem about all semantically equivalent rewritings.
- **NOGO-000006:** V2-A rejects the arbitrary all-essential log-width `ttFormula` payload witness.  The key proof is gate-count based: at ambient length `64`, the payload width is `6`, the concrete truth-table formula has Boolean-gate count `252`, and the V2-A linear gate cap allows only `16*6 + 16 = 112`.
- **NOGO-000007:** V2-A dodges the support-cardinality-only barrier.  It is not merely a predicate of the support-cardinality profile, because it also checks gate labels/counts and can distinguish formulas with the same support-cardinality profile.

This is real audit usefulness, but it is **not** Razborov-Rudich usefulness against all small circuits.  The current theorems do not say: for every polynomial-size circuit family computing a Boolean function, that function lacks the V2-A property.  Instead, they say: specific displayed `InPpolyFormula` witnesses fail the V2-A predicate.  That is a materially weaker and more representation-sensitive form of usefulness.

Therefore V2-A should not be reported as useful against `P/poly`, `PpolyDAG`, or all small circuits.  It is useful against the currently formalized hardwiring witnesses and against the support-cardinality-only failure mode.

## 4. Largeness

**Largeness result:** likely **not** a large property of Boolean functions as currently formulated; it is a property of formula representations.  Formal largeness remains unproved either way.

The critical question is whether V2-A defines a large set of Boolean functions, or instead a set of accepted **representations** of functions.  The current definition points strongly to the second interpretation.

Concrete evidence of representation sensitivity:

1. The filter directly inspects formula syntax: `booleanGateCount`, `FormulaCircuit.depth`, `orGateCount`, `notGateCount`, and `FormulaCircuit.support (w.family n)`.
2. The prefix-AND exclusion rejects the concrete `prefixAnd` syntax because it has no OR gates and no NOT gates.
3. The non-vacuity witness `seededPrefixAndFamily` starts from the same full-prefix conjunction and conjoins a tautological seed `(x₀ ∨ ¬x₀)`.  This changes the displayed syntax by adding OR/NOT gates while preserving the computed function of the prefix conjunction.
4. `NotSupportCardinalityOnly.lean` proves a related but weaker separation: V2-A is not determined solely by support-cardinality profile.  It exhibits an accepted seeded witness and a rejected full-prefix canonical witness with the same support-cardinality profile.

The strongest informal example is:

- raw full-prefix AND: rejected, because the displayed formula has no OR gate when support size is at least two;
- seeded full-prefix AND: accepted, because the displayed formula has the same support profile and small depth/gate count, but now contains OR and NOT through a tautological seed.

These formulas compute the same Boolean function at positive lengths if the seed is exactly `(x₀ ∨ ¬x₀)`: conjoining with a tautology does not change the function.  The current V2-A files do not appear to contain a named theorem stating this extensional equality and status separation in one package.  For promotion beyond audit-only use, that theorem should be proved explicitly.

Largeness in Razborov-Rudich is about a property holding for a large fraction of Boolean functions, typically viewed extensionally via truth tables.  V2-A currently gives no counting theorem of that kind.  Worse, because acceptance can change under tautological syntactic rewrites, the natural object being counted would be formula witnesses, not Boolean functions.  Counting formula witnesses is not the same as largeness of a Boolean-function property.

Conclusion: V2-A's current shape plausibly escapes largeness because it is not extensional.  However, if a future version quotient-normalizes formulas or otherwise turns V2-A into a truth-table property, the natural-proofs risk would become much more severe and a real largeness/usefulness analysis would be required.

## 5. Extensionality test

**Extensionality result:** **NO**.

V2-A does **not** appear to depend only on truth tables.  It depends on the displayed formula representation stored in an `InPpolyFormula` witness.

Reasoning:

- OR/NOT presence can be changed by adding a tautological seed.
- Gate counts and formula depth can be changed by rewriting a formula into an equivalent formula.
- The prefix-AND witness is rejected because of the concrete AND-only syntax, while a seeded variant with a tautological OR/NOT gadget is admitted.

This non-extensionality helps escape the classical Natural Proofs barrier because Razborov-Rudich natural proofs concern constructive, large, useful **properties of Boolean functions**.  A syntactic provenance predicate on witnesses is not automatically such a property.  If two equivalent formulas can receive different V2-A statuses, then V2-A is not a well-defined property of the Boolean function's truth table.

Caveat: this is an escape from the classical natural-proof template, not a lower-bound result.  Non-extensionality can also make a filter fragile: an adversary may rewrite a hardwiring witness into an accepted syntactic form.  Escaping naturality by representation sensitivity is therefore not enough; V2-A still needs adversarial rewrite robustness before any accepted promotion.

## 6. Barrier interaction

### Natural Proofs

**Status:** `does_not_apply` to V2-A as currently formulated; `uncertain` for any future lower-bound use.

As an audit predicate, V2-A is not a proof of a circuit lower bound and not a property of Boolean functions.  Its strongest current escape is non-extensionality: it inspects formula witnesses rather than truth tables.  Therefore the classical Natural Proofs barrier does not directly apply to the current artifact.  However, if V2-A is later converted into an extensional property or used as a lower-bound step with constructivity + largeness + usefulness against small circuits, the barrier becomes dangerous.  Before any accepted promotion, the repository should require a kernel-checked representation-sensitivity theorem and an explicit statement that the downstream route does not silently quotient V2-A into an extensional large property.

### Relativization

**Status:** `uncertain`.

The current V2-A predicate is not an oracle-machine argument and does not claim an oracle-invariant separation.  The repository's relativization interface is abstract: it defines a statement scheme as relativizing when it is invariant across oracle types, and a bypass witness requires two oracle worlds separating the scheme.  No such scheme or bypass witness is provided for V2-A.  Thus relativization does not directly apply to the audit predicate, but there is also no proof that any future V2-A-based route would be non-relativizing.  The honest status is uncertain for downstream lower-bound use.

### Algebrization

**Status:** `uncertain`.

Similarly, V2-A currently does not manipulate algebraic oracles and does not provide an algebrization-bypass witness.  The repository's algebrization interface is intentionally abstract and only provides the invariance/bypass pattern.  Since V2-A is a syntactic formula-witness predicate, the algebrization barrier is not directly triggered by the present report.  But no argument shows that a future V2-A-to-lower-bound route would avoid algebrization.  The appropriate status is uncertain.

## 7. Recommended next action

**Recommended next action:** `prove representation-sensitivity theorem first`

Before adversarial robustness or accepted-promotion blockers, the next best artifact is a small theorem packaging the key escape claim:

> There exist two formula witnesses computing the same language/function family such that V2-A accepts one and rejects the other.

A good target would use the raw full-prefix conjunction and the seeded full-prefix conjunction.  The theorem should explicitly prove both:

1. extensional equality of the evaluated languages/functions; and
2. different V2-A status.

Only after that theorem lands should the project start an adversarial robustness seed pack.  The current audit strongly suggests representation sensitivity, but a named theorem would prevent later reviewers from relying on an informal reading of the code.

## Commands run

- `pwd && rg --files -g 'AGENTS.md' -g 'RESEARCH_CONSTITUTION.md' -g 'known_guards.toml' -g '*.lean' -g '*.md' -g 'nogolog.jsonl' | sed -n '1,120p'`
- `find .. -name AGENTS.md -print`
- `cat AGENTS.md && sed -n '1,220p' RESEARCH_CONSTITUTION.md && sed -n '1,220p' spec/known_guards.toml`
- Python JSONL read of `outputs/nogolog.jsonl` for `NOGO-000001` through `NOGO-000007`
- `rg -n 'NOGO-000004|NOGO-000005' outputs/nogolog.jsonl -C 0`
- `sed` / `nl -ba` reads of the required V2-A, barrier, and operator-review files
- `./scripts/check.sh`

## Scope violations

none
