# fp3b7-D0.1 B/C hybrid predicate specification — gpt55

Slot: `fp3b7-D0.1`
Handle: `gpt55`
Progress classification: Infrastructure / markdown-only predicate audit.  This report does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, does not create or promote a `ProvenanceFilter`, and does not claim a `P != NP` endpoint.

## 1. Executive verdict

**INCONCLUSIVE_needs_more_design**

This report specifies exactly one candidate predicate family:

```text
AlmostNaturalProvenance_BC
= Sparse Structured-Payload Promise with Payload-Independent Provenance Certificate.
```

The predicate is intentionally narrow.  It can make the three requested paper-level safety lemmas credible:

1. **Non-largeness:** credible, because the accepted semantic targets form a doubly-exponentially tiny subset of all `n`-bit-input Boolean functions and are also sparse inside each logarithmic hardwiring slice.
2. **Non-circularity:** credible, because promise membership is defined by explicit low-parameter algebraic / combinatorial payload families and representation-invariant lift data, not by circuit lower bounds or absence of small witnesses.
3. **Hardwiring rejection:** credible against the NOGO-000006 arbitrary all-essential log-width truth-table payloads, because an arbitrary payload is accepted only if it already lies in the public structured payload class; otherwise the full payload truth table must be inserted into the certificate and exceeds the certificate-cost and payload-independence rules.

However, the same restrictions that make the predicate safe also make its **usefulness toward `PpolyDAG` unclear and probably weak**.  At this D0.1 level it should not open a full fp3b7 Round 1.  The missing piece is finite and explicit: a non-circular theorem showing that this sparse promise class contains an `NP` language family whose exclusion from `PpolyDAG` follows from the predicate rather than from a hidden hardness assumption.

## 2. Formal-ish predicate sketch

### 2.1 Ambient universe

For each ambient input length `n`, let

```text
BoolFun(n) := ({0,1}^n -> {0,1})
UniverseSize(n) := |BoolFun(n)| = 2^(2^n).
```

A witness `w_n` semantically denotes a Boolean function

```text
⟦w_n⟧ : {0,1}^n -> {0,1}.
```

The predicate is semantic in `⟦w_n⟧`, not in the displayed formula, circuit, DAG, gate order, or syntactic normal form used to present `w_n`.

### 2.2 Public structured payload class

Fix once and for all a public family of structured payload classes

```text
PayloadClass(ell) ⊆ ({0,1}^ell -> {0,1})
```

with the following parameters.

- `ell = ell(n) ≤ ceil(log2(n + 1))` for the hardwiring-relevant slice.
- `|PayloadClass(ell)| ≤ 2^(a * ell^b)` for fixed constants `a,b` with `ell^b = o(2^ell)`.
- Membership in `PayloadClass(ell)` is defined by an explicit low-parameter non-hardness condition, for example: “there exists a public index `i` of length at most `a * ell^b` such that `p = EvalPayload_ell(i)`”, where `EvalPayload` is a fixed algebraic/combinatorial evaluator.
- The definition must not mention any of: “not computable by small circuits”, “not in `PpolyDAG`”, “has no small witness”, “requires large formula size”, or an equivalent lower-bound phrase.

Examples of allowed payload evaluators at this level are low-degree polynomial threshold templates, bounded-rank algebraic forms, small-orbit group-invariant templates, or fixed-recursion combinatorial templates.  These are examples only; the predicate family below is the single object, and the report does not branch into multiple candidate predicates.

### 2.3 Sparse target ensemble `T_n`

A target in `T_n` is a semantic lift of a structured payload into the ambient `n` variables.  A lift datum is

```text
LiftDatum_n := (ell, pi, rho, tau)
```

where:

- `ell ≤ ceil(log2(n + 1))`;
- `pi : [ell] -> [n]` is an injective coordinate map selecting the payload window;
- `rho` is a public representation-invariant wrapper schema chosen from a fixed family of size `2^(polylog n)`;
- `tau` is a public promise tag, also from a fixed family of size `2^(polylog n)`, describing semantic side conditions such as symmetry, orbit restriction, or input-domain promise.

For `p ∈ PayloadClass(ell)`, define

```text
Lift_n(LiftDatum_n, p) : {0,1}^n -> {0,1}
```

by evaluating `p` on the selected coordinates and combining it with the wrapper schema `rho` on the promised domain specified by `tau`.  The target ensemble is

```text
T_n := { Lift_n(d, p) | d ∈ LiftDatum_n, p ∈ PayloadClass(ell(d)) }.
```

The density target is

```text
|T_n| ≤ 2^(polylog n),
```

or at worst `2^(n^o(1))`, never `2^(Ω(2^n))`.  More importantly for NOGO-000006, inside any fixed logarithmic payload window and wrapper skeleton, the number of accepted payload truth tables is at most `2^(a * ell^b)`, while the number of arbitrary payloads is `2^(2^ell)`.

### 2.4 Witness `w`

A witness is a presented object `w_n` together with its semantic denotation `⟦w_n⟧`.  The presentation may be a formula, circuit, DAG, table, or other representation, but the predicate may inspect the presentation only through the semantic equality relation below and the external certificate.

### 2.5 Certificate `Cert_n`

A certificate is a tuple

```text
Cert_n := (d, i, q, proof_payload, proof_lift, proof_promise, cost_receipt)
```

where:

- `d ∈ LiftDatum_n`;
- `i` is an index of length at most `a * ell(d)^b`;
- `q := EvalPayload_ell(d)(i)` is the structured payload denoted by `i`;
- `proof_payload` certifies `q ∈ PayloadClass(ell(d))` using only the public evaluator and index `i`;
- `proof_lift` certifies semantic equality `⟦w_n⟧ = Lift_n(d, q)` on the promised domain;
- `proof_promise` certifies the promise tag `tau` in `d` using the public promise definition;
- `cost_receipt` records the size of `d`, `i`, and the proof objects under the cost measure below.

The certificate is allowed to identify a structured payload by a short public index.  It is not allowed to carry an arbitrary `2^ell`-bit truth table for the payload unless that length is charged explicitly.

### 2.6 Representation-invariance relation

Define a relation

```text
RepEq_n(w, w') : Prop := ∀ x ∈ PromiseDomain(tau), ⟦w⟧(x) = ⟦w'⟧(x),
```

with the convention that if `tau` is the total-domain tag then this is ordinary extensional equality on `{0,1}^n`.

The accepted predicate must satisfy:

```text
RepEq_n(w, w')
∧ AlmostNaturalProvenance_BC(w, Cert_n)
→ AlmostNaturalProvenance_BC(w', Cert_n)
```

provided the same `Cert_n` proves the same semantic lift on the same promise domain.  Thus tautological rewrites, gate reordering, associativity rewrites, bottom-up normalisation, and alternative formula presentations do not change acceptance.

### 2.7 Payload-independence condition

Payload-independence is the critical B/C hybrid condition.  For a fixed lift skeleton `d` and length `ell`, write an arbitrary log-width hardwired payload as

```text
h : {0,1}^ell -> {0,1}.
```

A certificate `Cert_n` is payload-independent relative to `d` if every non-public bit in `Cert_n` is recoverable from:

```text
(n, d, i, public evaluator descriptions, public promise descriptions)
```

and not from oracle access to the full truth table of `h`, except through the short structured index `i` when `h = EvalPayload_ell(i)`.

Equivalently, for arbitrary payload families `h`, a certificate may depend on `h` only by proving that `h` is one of the public structured payloads and by naming its short index.  If `h` is not in `PayloadClass(ell)`, the only way to force equality with `Lift_n(d,h)` is to include payload-specific truth-table information, and that information is charged as `2^ell` bits.

### 2.8 Cost measure

Let

```text
Cost(Cert_n) := |d| + |i| + |proof_payload| + |proof_lift| + |proof_promise| + |cost_receipt| + PayloadBits(Cert_n).
```

Here `PayloadBits(Cert_n)` is the number of arbitrary payload truth-table bits used by the certificate outside the public structured index mechanism.  The acceptance threshold is

```text
Cost(Cert_n) ≤ C(n) := K * (log(n + 2))^r
```

for fixed constants `K,r` chosen before seeing the payload family.  For the NOGO-000006 regime `ell = ceil(log2(n + 1))`, an arbitrary payload truth table has length `2^ell = Θ(n)`, so explicitly charging it violates the polylogarithmic certificate budget.

### 2.9 Accepted predicate

The single candidate predicate is:

```text
AlmostNaturalProvenance_BC(w_n, Cert_n) holds iff:

1. Cert_n parses as (d, i, q, proof_payload, proof_lift, proof_promise, cost_receipt);
2. q = EvalPayload_ell(d)(i);
3. proof_payload verifies q ∈ PayloadClass(ell(d));
4. proof_promise verifies that tau(d) defines the active promise domain;
5. proof_lift verifies ⟦w_n⟧ = Lift_n(d,q) on that promise domain;
6. Cert_n is representation-invariant under RepEq_n;
7. Cert_n is payload-independent relative to d;
8. Cost(Cert_n) ≤ K * (log(n + 2))^r.
```

The usefulness claim, if any, is explicitly restricted to the promise ensemble `T_n`.  The predicate does not classify all Boolean functions, does not claim largeness in `BoolFun(n)`, and does not assert a lower bound for arbitrary functions outside `T_n`.

## 3. Non-largeness lemma, paper-level

**Lemma 1 — Non-largeness of `AlmostNaturalProvenance_BC`.**  For every sufficiently large `n`, the number of Boolean functions accepted by `AlmostNaturalProvenance_BC` is at most `2^(polylog n)` or, under the weaker parameter allowance, at most `2^(n^o(1))`.  In particular, its density in the full Boolean-function universe is

```text
|Accepted_n| / |BoolFun(n)|
≤ 2^(polylog n) / 2^(2^n)
= 2^(-2^n + polylog n),
```

so it is not large in the Razborov--Rudich sense.

**Mechanism.**  Acceptance implies membership in `T_n`.  The number of lift data is at most `2^(polylog n)`, and for each logarithmic payload length the number of public structured payloads is at most `2^(a * ell^b) = 2^(polylog n)`.  Therefore the total number of semantic functions that can be accepted is bounded by the number of lift data times the number of public payload indices.  This is tiny compared with `2^(2^n)`.

This proof does not use the forbidden mechanism “hard functions are rare.”  It uses only explicit sparsity of the promise ensemble and the certificate-index budget.

## 4. Non-circularity lemma, paper-level

**Lemma 2 — Non-circularity of promise and certificate membership.**  Membership in the `AlmostNaturalProvenance_BC` promise/certificate class does not encode the desired circuit lower bound, because the definitions of `PayloadClass`, `LiftDatum`, `PromiseDomain`, `RepEq`, `Cost`, and `PayloadBits` are syntactic-semantic resource definitions that avoid lower-bound language.

**Required definitional discipline.**  The predicate is permitted to say:

- `p = EvalPayload_ell(i)` for a public evaluator and short index;
- `⟦w_n⟧ = Lift_n(d,p)` on a stated promise domain;
- `Cost(Cert_n) ≤ K(log n)^r`;
- the certificate does not use arbitrary payload truth-table bits except through an explicitly charged field.

The predicate is forbidden to say or paraphrase:

- `⟦w_n⟧` is not computable by small circuits;
- `⟦w_n⟧` is not in `PpolyDAG`;
- no small witness exists;
- every small circuit fails on some input;
- the payload is hard, pseudorandom against circuits, or lower-bound-certified unless that statement is replaced by an independently defined public evaluator / promise condition.

**Proof idea.**  A future formalization can parse and verify the certificate without invoking `PpolyDAG`, `NP_not_subset_PpolyDAG`, circuit lower-bound predicates, or nonexistence of circuits.  All membership checks are positive checks: public index evaluation, semantic lift equality on the promise domain, representation-invariant equality, and accounting of certificate bits.

This lemma is credible only under the strict reading above.  If a future version defines `PayloadClass` by saying that its members are “functions outside small DAGs,” “truth tables without small witnesses,” or equivalent hardness phrases, then this lemma fails and the verdict must become **RED-light_family_B**.

## 5. Hardwiring rejection lemma, paper-level

**Lemma 3 — Rejection of arbitrary all-essential log-width truth-table payloads.**  Let `ell(n) = ceil(log2(n + 1))`, and let

```text
h_n : {0,1}^ell(n) -> {0,1}
```

be an arbitrary all-essential payload of the NOGO-000006 kind, hardwired into an ambient `n`-variable formula by a fixed injection and wrapper skeleton.  Then `Lift_n(d,h_n)` can satisfy `AlmostNaturalProvenance_BC` only in one of the following two cases:

1. `h_n ∈ PayloadClass(ell(n))` and has a short public index `i`; or
2. the certificate explicitly carries enough payload-specific truth-table information to identify `h_n`, in which case `PayloadBits(Cert_n) ≥ 2^ell(n) = Θ(n)` and `Cost(Cert_n) > K(log n)^r` for sufficiently large `n`.

Thus arbitrary all-essential log-width truth-table payloads cannot satisfy the predicate unless their payload-specific truth-table information is explicitly charged.

**Where the arbitrary payload fails.**

- **Promise membership:** a generic all-essential payload is not in the public structured class `PayloadClass(ell)`.  Since `PayloadClass(ell)` has size `2^(a * ell^b)` and the full payload universe has size `2^(2^ell)`, almost all payloads fail membership.
- **Payload-independence:** a certificate tailored to the arbitrary truth table of `h_n` violates payload-independence unless the dependence is exposed through `PayloadBits(Cert_n)`.
- **Certificate cost:** once exposed, the arbitrary truth table costs `2^ell = Θ(n)` bits in the NOGO-000006 log-width regime, exceeding the polylogarithmic cost threshold.
- **Representation-invariance:** tautological rewrites of the same hardwired function do not help.  Acceptance depends on semantic membership in `T_n` plus a payload-independent certificate, not on displayed gate shapes.
- **Distribution/promise mismatch:** the predicate's usefulness domain is `T_n`; an arbitrary payload hardwiring lies outside that promise unless it is one of the public structured payloads.

This directly targets the NOGO-000006 obstruction: support size `ell = O(log n)` by itself no longer suffices for acceptance.

## 6. Support-cardinality / syntax / normalisation cross-check

### NOGO-000007 support-cardinality-only: **addressed**

Reason: `AlmostNaturalProvenance_BC` is not a function of support cardinality.  Two witnesses with the same support profile can differ on whether the selected payload is in `PayloadClass(ell)`, whether a payload-independent certificate exists, and whether `PayloadBits` exceeds the cost threshold.  A canonical hardwiring twin with the same support size is rejected unless its payload belongs to the sparse structured class or pays for the arbitrary truth table.

### NOGO-000008 tautological rewrite: **addressed**

Reason: acceptance is representation-invariant under semantic equality on the promise domain.  Adding a redundant gate such as `(x_0 OR NOT x_0)` changes displayed syntax but does not change `⟦w_n⟧`, `T_n` membership, the public payload index, or the certificate cost.  A rewrite therefore cannot turn a non-structured arbitrary payload into a structured payload.

### NOGO-000009 normalise-then-filter: **addressed**

Reason: the predicate does not use a context-uniform bottom-up structural normaliser followed by a syntactic mixed-gate filter.  It uses semantic lift equality and certificate accounting.  Normalisation may be used as an implementation aid for a presentation, but it is not the mathematical acceptance criterion and cannot be the reason a witness gains or loses the required OR/NOT/displayed-shape feature.

Residual risk: all three answers become **not addressed** if a future implementation replaces semantic lift equality and payload accounting with displayed syntax, support-cardinality thresholds, or normalise-then-syntax filtering.

## 7. Razborov--Rudich analysis

### Constructivity

The predicate can be constructive relative to the public evaluator and certificate verifier.  Given `(w_n, Cert_n)`, checking the certificate may be efficient or at least explicitly costed.  This is useful for a formal provenance filter but creates natural-proofs risk if combined with largeness and broad usefulness.

### Largeness

Largeness is deliberately false.  The accepted family is bounded by the number of sparse promise targets and short certificates, at most `2^(polylog n)` or `2^(n^o(1))`, inside a universe of size `2^(2^n)`.  The predicate is therefore **almost-natural but non-large**, not a classical large natural property.

### Usefulness

Usefulness is the weak leg.  The only non-circular usefulness statement currently available is promise-local:

```text
If a target family lies in T_n and has an accepted payload-independent provenance certificate,
then the route may reason about that target inside the T_n / promise ensemble.
```

That does not yet imply a worst-case lower bound against `PpolyDAG` and does not produce an `NP` language outside `PpolyDAG`.

### Classification

The predicate is:

```text
almost-natural but non-large;
not natural-proof-shaped in the full Boolean-function universe;
constructive relative to certificates;
unclear / likely too weak for repository-level usefulness.
```

It avoids the Razborov--Rudich triad by failing largeness.  It does not provide a natural-proofs bypass witness for a final lower-bound proof, and it does not address relativization or algebrization beyond the fact that those barrier interfaces remain unclaimed.

## 8. Usefulness toward `PpolyDAG`

The repository goal would require a bridge of the following strength:

```text
ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG
```

For `AlmostNaturalProvenance_BC` to matter, usefulness would need to say something like:

```text
There exists an NP language L and infinitely many / all relevant lengths n
such that the length-n truth-table slice of L belongs to T_n with accepted
payload-independent provenance, and every PpolyDAG family fails to compute L.
```

The present predicate does not supply this.  It only defines a sparse promise class and rejects arbitrary payload hardwiring.  Because `T_n` is intentionally low-description and sparse, the route faces a serious usefulness hazard:

- If `PayloadClass` is explicit and easily evaluable, accepted targets may themselves have small circuits or small DAGs, making them poor lower-bound candidates.
- If `PayloadClass` is made hard enough to contain an `NP` language outside `PpolyDAG`, the hardness may have been smuggled into the promise definition, violating non-circularity.
- If usefulness is stated only distributionally or only inside `T_n`, it remains a side track and does not imply `NP_not_subset_PpolyDAG`.

Answer:

```text
only_distributional_side_track
```

A plausible path to `PpolyDAG` has not been shown.  The predicate may be useful as an audit object for rejecting known hardwiring attacks, but it is not yet a mainline lower-bound source.

## 9. Structural double-bind search

The candidate exposes a sharp double-bind.

### Bind A — cheap enough to verify vs. too easy to compute

If the public payload index and lift certificate are cheap enough to verify and produce, then the accepted target may be cheap enough to compute.  In that regime the predicate is safe from hardwiring but useless for separating `NP` from `PpolyDAG`.

### Bind B — restrictive enough to reject hardwiring vs. too sparse for usefulness

The sparse promise class rejects arbitrary log-width truth-table payloads by admitting only `2^(a * ell^b)` payloads out of `2^(2^ell)`.  But the same sparsity means the predicate says nothing about almost every Boolean function and has no automatic route to a worst-case `NP` lower bound.

### Bind C — hard enough to be useful vs. circular

If `PayloadClass` is strengthened until it contains a meaningful `NP`-hard or `PpolyDAG`-separating target, the strengthened promise risks saying, in disguised form, that the target has no small circuits or no small DAG witnesses.  That would collapse the non-circularity lemma and force **RED-light_family_B**.

### Bind D — semantic enough to avoid syntax attacks vs. natural-proof pressure

The semantic, representation-invariant design avoids NOGO-000008 and NOGO-000009.  If it were expanded from sparse `T_n` to a broad efficiently decidable semantic property of many truth tables, it would regain largeness and become natural-proof-shaped.  Keeping it non-large avoids Razborov--Rudich but weakens usefulness.

Net result: the predicate survives the local NoGo/barrier chain as a specification, but the double-bind blocks any responsible claim of mainline progress.

## 10. Recommended next action

```text
run_second_D0_1_review
```

The next review should not open full fp3b7 Round 1.  It should challenge exactly one missing bridge:

```text
Can this sparse structured-payload promise class contain a non-circular NP target
whose accepted provenance can imply a PpolyDAG lower bound?
```

If the answer requires defining `PayloadClass` by lower-bound language, then the family should be marked **RED-light_family_B**.  If the answer remains only distributional or promise-local, fp3b7 should be treated as a side track rather than mainline progress toward `P != NP`.
