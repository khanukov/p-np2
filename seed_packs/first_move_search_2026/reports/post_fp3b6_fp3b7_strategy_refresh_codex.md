# Post-FP3b6 / FP3b7 strategy refresh — codex

Task: post-FP3b strategy refresh  
Handle: `codex`  
Progress classification: Infrastructure / research-governance strategy. This report is markdown-only and does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.

## 1. Executive verdict

```text
return_to_research_gap_source_search
```

The FP3b provenance-filter route should stop as a provenance-filter programme.  The next useful move is not another renamed support/syntax/provenance filter.  The next D0 should return to the main source-theorem search and ask whether a direct meta-complexity / MCSP source obligation can be stated without passing through FP3b-style provenance predicates.

I would not reopen fp3b6 budget repair as the default next move, and I would not launch another almost-natural provenance family.  Both latest families produced useful audit lessons, but neither currently supplies a credible bridge to `ResearchGapWitness.dagSeparation`.

## 2. What fp3b6 taught us

Family A, the distinguisher-matrix / fingerprint-provenance route, had genuine local content but failed as a magnification-ready source route.

* **D3′-A local anti-collapse was real.**  The fp3b6 route did exhibit a meaningful local theorem: if a fingerprint stays inside the explicit log-width payload window, the arbitrary all-essential truth-table payload obstruction cannot simply collapse the predicate in the same way as earlier support-cardinality-only filters.
* **D3′-C showed the budget cliff is sharp.**  The converse sharpness result made the local theorem honest: once the fingerprint is allowed to see the full relevant window, the anti-collapse argument no longer has slack.  This is not a loose proof artifact; it is the design boundary.
* **D5-tight and D6 showed AM-style fingerprints exceed the log-window budget.**  The Atserias--Müller-style theorem-level footprints extracted in D5-tight require polynomial or sampled-polynomial scale such as `n^{γ+ε}` or `n^{2γ+ε} log n`, not `O(log n)`.  D6 then reconciled this with D3′-C: the local hiding theorem lives below exactly the window that visible AM-style magnification wants to exceed.
* **Therefore matrix/fingerprint provenance in that form is local-only, not magnification-ready.**  The route does not refute matrix methods, distinguishers, or hardness magnification in general.  It refutes the specific hope that fp3b6's log-window payload hiding can be bolted onto visible AM-style fingerprints and still produce a `PpolyDAG`-useful source theorem.

The pessimistic lesson is that fp3b6 found a real local invariant but placed it in the wrong budget regime for mainline magnification.

## 3. What fp3b7 taught us

Family B, the almost-natural provenance route, passed several local safety checks by becoming too narrow to be useful.

* **Non-largeness passed.**  The `AlmostNaturalProvenance_BC` shape is sparse, promise-local, and low-description enough that it does not obviously define a large property over the full Boolean-function universe.
* **Non-circularity passed as written.**  Membership is described by public structured-index, lift, and certificate checks rather than by directly asserting the target lower bound.
* **Hardwiring rejection passed under strict accounting.**  Arbitrary all-essential log-width `ttFormula` payloads are rejected unless they belong to the public structured payload class or explicitly pay their truth-table information in the certificate.
* **Usefulness toward `PpolyDAG` failed / is likely too weak.**  The accepted objects are sparse, structured, and promise-local.  No credible non-circular route was identified from that narrow accepted class to `NP_not_subset_PpolyDAG`.
* **Broadening usefulness risks circularity or natural proofs.**  If the class is widened enough to hit the needed lower-bound target, the design appears to fall into one of two bad patterns: it either becomes large/constructive/useful in a natural-proof-shaped way, or it hides the desired lower bound inside `PayloadClass`, a promise tag, a pseudorandomness condition, or another circular hardness assumption.

The pessimistic lesson is that fp3b7 avoided the old traps by giving up the leverage needed for the repository target.

## 4. What FP3b route as a whole established

FP3b should be treated as a productive audit route, not as an active mainline source route.  It established the following scientific artifacts.

* **NOGO-000006 — arbitrary all-essential log-width `ttFormula` payload obstruction.**  A filter that accepts by log-width support behavior alone can admit arbitrary all-essential truth-table payloads renamed into the ambient variables.
* **NOGO-000007 — support-cardinality-only meta-barrier.**  Any support-cardinality-only provenance filter that accepts an honest sublinear-support witness also accepts a canonical hardwiring twin with the same support-cardinality profile.
* **NOGO-000008 — tautological rewrite attack against syntactic V2-A.**  Displayed syntax constraints such as gate counts, OR/NOT presence, and similar syntactic markers can be defeated by semantically redundant tautological rewrites.
* **NOGO-000009 — normalize-then-filter self-defeat.**  The natural syntactic-normalisation patch for V2-A destroys the filter's own non-vacuity witness while trying to remove the tautological seed attack.
* **fp3b6 D3′-A / D3′-C local theorem pair.**  The pair identified a genuine but sharply budget-limited local anti-collapse fact for matrix/fingerprint provenance.
* **fp3b7 RED-light lesson.**  Almost-natural sparse/promise provenance can be locally safe against support, syntax, and hardwiring traps, but the safety is bought by losing visible usefulness for `PpolyDAG`.

Together these artifacts give a strong negative map: support-only, syntax-only, normalize-then-filter, log-window fingerprint hiding, and sparse almost-natural provenance should not be relaunched as mainline FP3b by cosmetic renaming.

## 5. Remaining viable families

I see at most two families worth keeping on the strategic menu.  Only the first should receive the next D0 by default.

### Family 1 — Direct meta-complexity / MCSP source interface, not provenance filters

* **Core idea.**  Stop asking whether a formula/DAG witness has acceptable provenance.  Instead ask whether a direct `SearchMCSPWeakLowerBound`-shaped source theorem can be stated, audited, and eventually connected to `VerifiedNPDAGLowerBoundSource` without an intermediate `ProvenanceFilter` predicate.  The D0 should focus on the interface: what is the smallest non-circular MCSP/search-to-decision/Kolmogorov-randomness statement whose conclusion is recognizably upstream of the repository's existing compression-magnification frontier?
* **Why it is not support-cardinality-only.**  The object of study is not the number of input coordinates used by a witness.  It is a source-level meta-complexity statement about complexity of truth tables, search hardness, or direct MCSP lower-bound behavior.
* **Why it is not displayed-syntax-only.**  The intended predicate must be extensional or semantic at the truth-table / complexity-measure level, not a condition on displayed formula gate shapes.
* **Why it does not immediately become natural-proof-shaped.**  This is the main danger.  The only plausible safety route is to keep the D0 focused on a non-large, search/source, or promise-specific statement already aligned with `SearchMCSPWeakLowerBound`, not a large constructive property of random Boolean functions.  The D0 must explicitly test largeness, constructivity, and usefulness rather than assume safety.
* **How it might produce `ResearchGapWitness.dagSeparation`.**  It could do so only through the documented mainline chain: a credible `SearchMCSPWeakLowerBound` source would feed into `VerifiedNPDAGLowerBoundSource`, which then targets `NP_not_subset_PpolyDAG`.  This is the only listed family with a direct conceptual path to an existing source obligation.
* **Immediate NoGo/barrier risk.**  Natural-proofs risk is high if the statement becomes a large constructive property.  Relativization/algebrization risk remains unresolved unless the source theorem explicitly uses non-relativizing/non-algebrizing ingredients.  It can also become circular if the MCSP hardness statement merely repackages the desired DAG lower bound.
* **One D0-style seed-pack question.**  Can we formulate a non-circular, non-large `SearchMCSPWeakLowerBound` candidate whose statement is smaller and closer to `VerifiedNPDAGLowerBoundSource` than any FP3b provenance predicate, and whose first self-attack does not reduce to natural proofs, relativization, algebrization, or hidden `PpolyDAG` hardness?

### Family 2 — Proof-complexity / bounded-arithmetic bridge

* **Core idea.**  Investigate whether feasible interpolation, proof-complexity lower bounds, bounded arithmetic, or EF/Frege barriers can supply a source theorem whose failure would be visible as a `PpolyDAG` separation or as a direct obstruction to proving small circuits.
* **Why it is not support-cardinality-only.**  The central data are proof systems, reflection principles, interpolation maps, or bounded-arithmetic theories, not witness support profiles.
* **Why it is not displayed-syntax-only.**  A serious version would reason about semantic proof strength, feasible witnessing, or proof-size lower bounds rather than displayed formula syntax.
* **Why it does not immediately become natural-proof-shaped.**  It may avoid the standard shape if the useful object is a proof-theoretic obstruction or reflection principle rather than a large constructive property of Boolean functions.  However, if translated into a broad efficiently checkable lower-bound property, it can still become natural-proof-shaped.
* **How it might produce `ResearchGapWitness.dagSeparation`.**  The plausible path is indirect: a proof-complexity lower bound or feasible interpolation theorem might imply circuit lower bounds for an NP language, which could then be routed toward `NP_not_subset_PpolyDAG`.  This bridge is currently speculative and likely longer than the direct MCSP interface.
* **Immediate NoGo/barrier risk.**  The risk is not NOGO-000006/000007 directly; it is that the bridge becomes either too weak, proof-system-specific, or blocked by known bounded-arithmetic unprovability phenomena.  Another risk is producing only meta-unprovability rather than an actual source theorem.
* **One D0-style seed-pack question.**  Is there a bounded-arithmetic or feasible-interpolation statement with a concise source-theorem shape whose conclusion implies an NP-language lower bound against `PpolyDAG`, rather than merely explaining why such lower bounds are hard to prove?

### Family 3 — Formal barrier theorem for FP3b-style filters

* **Core idea.**  Stop searching for another FP3b filter and instead formalize a class-level impossibility theorem covering the already-failed FP3b-style designs: support-only filters, displayed-syntax filters, normalize-then-filter patches, log-window fingerprint hiding, and sparse almost-natural promise certificates.
* **Why it is not support-cardinality-only.**  The theorem would classify a family of filter mechanisms, not use support cardinality as the accepted positive criterion.
* **Why it is not displayed-syntax-only.**  The theorem should be stated over an abstract class of filter strategies, including semantic/accounting predicates where possible, not just gate-shape checks.
* **Why it does not immediately become natural-proof-shaped.**  It is a negative barrier theorem about a design class, not a useful property used to separate hard functions from easy ones.
* **How it might produce `ResearchGapWitness.dagSeparation`.**  It probably will not.  Its value is governance: it prevents further wasted FP3b launches and clarifies why the route should return to source-theorem search.  Therefore it is not the best next mainline move.
* **Immediate NoGo/barrier risk.**  The main risk is overformalizing a vague class and producing either a theorem too narrow to matter or a theorem so broad that it silently assumes the conclusion.  It also risks consuming effort on closure rather than source discovery.
* **One D0-style seed-pack question.**  Can the fp3b6/fp3b7 double-bind be stated as a kernel-checkable class theorem without weakening NoGoLog discipline or smuggling in literature-level AM parameter assumptions as axioms?

## 6. Best next seed pack

Recommended seed pack name:

```text
seed_packs/fp3b8_mcsp_direct_source_D0/
```

Do not create the seed pack yet.  The only recommended slot is:

```text
D0 — Direct MCSP source-interface feasibility audit
```

D0 question:

> Can a non-circular, non-large `SearchMCSPWeakLowerBound` candidate be stated directly, without any FP3b provenance filter, such that its audited conclusion is visibly upstream of `VerifiedNPDAGLowerBoundSource` and not merely a renamed support-cardinality, displayed-syntax, or almost-natural promise predicate?

This avoids fp3b6 because it does not rely on a log-window fingerprint budget that must later accommodate AM-style footprints.  It avoids fp3b7 because it does not try to buy safety by accepting only sparse structured promise payloads; usefulness toward the existing source obligation is part of the D0 question itself.

## 7. NoGoLog recommendation

```text
yes, but only after Lean formal class theorem
```

NOGO-000010 and NOGO-000011 should eventually be filed only if a class-level theorem is formalized with discipline comparable to NOGO-000006 through NOGO-000009.

* For fp3b6, a markdown-level strategic double-bind is not the same as a kernel-checked theorem about all relevant fingerprint-budget repair attempts.
* For fp3b7, the current RED-light is a strategic usefulness failure, not a formal theorem that every almost-natural/promise/certificate variant fails.

Until such theorems exist, the closures should remain markdown closures and audit references.  Expanding NoGoLog to markdown-only entries would weaken the ledger's current meaning.

## 8. Final recommendation

Stop the FP3b provenance-filter route as an active mainline route.

Open exactly one D0 next, and make it the direct MCSP source-interface feasibility audit:

```text
seed_packs/fp3b8_mcsp_direct_source_D0/
D0 — Direct MCSP source-interface feasibility audit
```

First question to ask:

> Can the repository state a concise, non-circular, non-large `SearchMCSPWeakLowerBound` candidate whose path to `VerifiedNPDAGLowerBoundSource` is clearer than every FP3b provenance-filter path, and whose first self-attack survives NOGO-000006 through NOGO-000009 plus the relativization, natural-proofs, and algebrization barrier interfaces?

If the answer is no, the correct next move is not fp3b9.  It is to return fully to the broader `ResearchGap` source theorem search and stop spending mainline cycles on provenance filters.

## Scope confirmation

Scope violations: none.

This report created only:

```text
seed_packs/first_move_search_2026/reports/post_fp3b6_fp3b7_strategy_refresh_codex.md
```

It creates no Lean code, no lakefile changes, no JSONL edits, no `outputs/attempts` edits, no spec edits, no known-guards edits, no trust-root edits, no seed-pack skeleton, no `ProvenanceFilter` promotion, no `SourceTheorem`, no `gap_from`, no `ResearchGapWitness`, no endpoint, and no `P≠NP` claim.
