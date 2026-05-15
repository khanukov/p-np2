# fp3b7-D0.1 second review — AlmostNaturalProvenance_BC

Slot: `fp3b7-D0.1-second-review`
Handle: `gpt55`
Progress classification: Infrastructure / markdown-only independent review.  This report does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, does not promote a `ProvenanceFilter`, and does not claim any endpoint.

## 1. Executive verdict

```text
RED_light_family_B
```

The D0.1 predicate is a useful audit specification, but it is **not worth opening into full fp3b7 Round 1** as a route toward the repository target.

My review is adversarial but not dismissive:

- **Non-largeness:** passed, conditional on the D0.1 size caps for payloads, lift data, wrappers, and promise tags being kept fixed and explicit.
- **Non-circularity:** passed for the written predicate, because it deliberately defines membership by positive structured-index and lift checks rather than by circuit lower-bound language.
- **Hardwiring rejection:** passed with an implementation caveat: it works only if the payload-independence and cost accounting charge every payload-dependent bit in the lift datum, wrapper, promise tag, and proof objects.
- **Usefulness toward `PpolyDAG`: failed / likely too weak.**  The same design choices that make the predicate safe make accepted targets low-description and promise-local.  No credible non-circular mechanism is given by which this sparse structured-payload class could contain an `NP` target and imply `NP_not_subset_PpolyDAG`.

The central answer is therefore:

```text
Core question: Can this sparse structured-payload promise class contain a
non-circular NP target whose accepted provenance can imply a PpolyDAG lower bound?

Review answer: not credibly, without either making the target easy or hiding the
lower bound in PayloadClass / promise membership.
```

## 2. Summary of `AlmostNaturalProvenance_BC`

D0.1 specifies one predicate family:

```text
AlmostNaturalProvenance_BC
= Sparse Structured-Payload Promise with Payload-Independent Provenance Certificate.
```

In my own words, the objects are as follows.

### Target ensemble `T_n`

For ambient input length `n`, the full semantic universe is

```text
BoolFun(n) = ({0,1}^n -> {0,1}),
|BoolFun(n)| = 2^(2^n).
```

The predicate does not range over all of `BoolFun(n)`.  It accepts only functions lying in a sparse target ensemble

```text
T_n = { Lift_n(d, p) | d in LiftDatum_n, p in PayloadClass(ell(d)) }.
```

The intended size is at most `2^(polylog n)` or at worst `2^(n^o(1))`.

### Payload class

For `ell <= ceil(log2(n + 1))`, `PayloadClass(ell)` is a public, low-parameter, structured set of Boolean payloads

```text
PayloadClass(ell) ⊆ ({0,1}^ell -> {0,1})
```

with cardinality at most `2^(a * ell^b)`, where this is tiny compared with the full payload universe `2^(2^ell)`.  Membership is by a short public index `i` and evaluator `EvalPayload_ell(i)`, not by saying the payload is hard.

### Lift datum

A lift datum is

```text
d = (ell, pi, rho, tau)
```

where `pi` selects an `ell`-coordinate window inside `[n]`, `rho` is a public wrapper schema, and `tau` is a public promise tag.  The crucial safety requirement is that `rho` and `tau` come from fixed small public families and cannot smuggle the arbitrary payload truth table.

### Certificate

A certificate is

```text
Cert_n = (d, i, q, proof_payload, proof_lift, proof_promise, cost_receipt)
```

where `q = EvalPayload_ell(i)`, the payload proof checks `q ∈ PayloadClass(ell)`, the lift proof checks semantic equality between the witness and `Lift_n(d,q)` on the promised domain, and the cost receipt records all certificate resources.

### Payload-independence

A certificate is payload-independent when its non-public bits are recoverable from public data and the short structured index, not from arbitrary oracle access to the payload truth table.  If the payload is not in `PayloadClass(ell)`, any certificate that identifies it must explicitly carry payload-specific truth-table information.

### Cost measure

The D0.1 cost measure is

```text
Cost(Cert_n)
  = |d| + |i| + |proof_payload| + |proof_lift|
    + |proof_promise| + |cost_receipt| + PayloadBits(Cert_n),
```

with threshold

```text
Cost(Cert_n) <= K * (log(n + 2))^r.
```

Since a log-width arbitrary payload has truth table length `2^ell = Θ(n)`, explicitly carrying it exceeds the polylogarithmic cost threshold.

### Accepted predicate

`AlmostNaturalProvenance_BC(w_n, Cert_n)` accepts exactly when the certificate parses, names a structured payload, proves promise/lift membership semantically, is invariant under representation changes, is payload-independent, and fits the polylogarithmic cost budget.  Usefulness is restricted to `T_n`; the predicate does not claim to classify all Boolean functions.

## 3. Non-largeness review

Verdict:

```text
passed
```

The D0.1 non-largeness argument works at the paper level, subject to preserving the stated parameter caps.

### Accepted set size bound

Acceptance implies membership in `T_n`.  Therefore

```text
|Accepted_n| <= |LiftDatum_n| * max_ell |PayloadClass(ell)|,
```

up to possible collisions in `Lift_n`, which can only reduce the count.

For `ell <= O(log n)`, the coordinate map count is not dangerous:

```text
# injections [ell] -> [n] <= n^ell <= 2^(O((log n)^2)).
```

If wrappers and promise tags are each capped by `2^(polylog n)` and payload indices by `2^(polylog n)`, then `|Accepted_n| <= 2^(polylog n)`.

### Dependence on `PayloadClass` size

The argument depends essentially on

```text
|PayloadClass(ell)| <= 2^(a * ell^b) << 2^(2^ell).
```

If future work lets `PayloadClass(ell)` approach the full truth-table universe or allows a universal interpreter whose index length is `Θ(2^ell)`, the non-largeness proof collapses for the hardwiring slice.  D0.1 does not do that.

### Wrappers / lift data large-class risk

The dangerous channel is not `pi`; it is `rho` and `tau`.  If a wrapper schema or promise tag can carry arbitrary advice of length `Θ(n)` or select an arbitrary subset of `{0,1}^n`, then the lift side can reintroduce largeness.  D0.1 prevents this by requiring fixed public wrapper/promise families of size `2^(polylog n)`.  This constraint must be treated as part of the predicate, not as an optional implementation detail.

### Measurement universe

Largeness is correctly measured in the full Boolean-function universe `BoolFun(n)`, not merely inside the promise class.  Inside `T_n` the predicate may be large or even total; that is irrelevant to Razborov--Rudich largeness over all truth tables.  The escape is genuine non-largeness, not a relabeling of the sample space.

## 4. Non-circularity review

Verdict:

```text
passed
```

The written predicate avoids the obvious circular phrases.  It defines promise/certificate membership by:

- public structured payload indices;
- semantic lift equality;
- promise-domain membership;
- representation invariance;
- payload-independence;
- explicit certificate cost accounting.

It does **not** define membership by saying:

- not computable by small circuits;
- not in `PpolyDAG`;
- has no small witness;
- every small circuit fails;
- pseudorandom against small circuits;
- requires large formula/DAG;
- hard for a circuit class.

The review pass is narrow.  It says only that the D0.1 predicate definition is not circular.  It does not say that the predicate can later become useful without circularity.  That later step is exactly where I expect failure: any attempt to make `PayloadClass` contain a meaningful `NP` target outside `PpolyDAG` appears likely to introduce one of the forbidden lower-bound phrases, directly or under a pseudorandomness/hardness synonym.

## 5. Hardwiring rejection review

Verdict:

```text
passed
```

The hardwiring rejection works against the NOGO-000006 family if the D0.1 accounting rules are enforced literally.

### Is `PayloadClass` small enough?

Yes.  For `ell = O(log n)`, the full payload universe has size

```text
2^(2^ell) = 2^(Θ(n)),
```

while the accepted public payload class has size at most

```text
2^(a * ell^b) = 2^(polylog n).
```

Thus a generic all-essential truth-table payload is not in `PayloadClass(ell)`.

### Is payload-independence well-defined enough?

For a markdown-level review, yes, but it is the least formal part of the design.  The intended condition is not merely “the certificate is short”; it is “the certificate's non-public bits are not functions of the arbitrary payload truth table except through a public short index.”  A future formalization would need a precise dependency / oracle-use model.

For the decision here, the condition is strong enough to reject the known NOGO-000006 attack because an arbitrary payload has no public short index.

### Could an adversary encode payload through lift datum / wrapper / promise tag?

Only if D0.1's caps are weakened.  This is the main implementation caveat.

- If `rho` can be an arbitrary wrapper with `Θ(n)` advice bits, the payload can move into `rho`.
- If `tau` can specify an arbitrary promise subset with payload-dependent membership, the payload can move into `tau`.
- If `proof_lift` can contain arbitrary per-input exceptions without charging them, the payload can move into the proof.

D0.1 rejects these channels by bounding `d`, requiring public wrapper/promise families, and including `PayloadBits(Cert_n)` in `Cost(Cert_n)`.  Therefore the hardwiring review passes only with the explicit condition:

```text
Every payload-dependent bit in d, rho, tau, proof_lift, proof_promise,
and cost_receipt must either come from the public short index i or be charged
as PayloadBits(Cert_n).
```

### Does representation-invariance reintroduce adaptivity?

No.  Representation-invariance removes displayed-syntax dependence; it does not by itself create a new certificate.  An adversary may change the formula presentation, but the semantic target still needs either a structured payload index or an explicitly charged arbitrary payload.  Tautological rewriting does not manufacture a public index.

## 6. NOGO cross-check

### NOGO-000006 — arbitrary all-essential log-width payload

```text
addressed
```

The arbitrary payload no longer passes just because it has logarithmic support.  It must either lie in the sparse public payload class or pay `Θ(n)` payload bits, violating the polylog certificate threshold.

### NOGO-000007 — support-cardinality-only meta-barrier

```text
addressed
```

The predicate is not determined by support cardinality.  Two witnesses with the same support can differ by structured-payload membership, payload-independent certificate existence, and charged payload bits.

### NOGO-000008 — tautological rewrite attack

```text
addressed
```

The predicate is semantic/representation-invariant rather than displayed-gate-count-sensitive.  Adding a tautological seed changes syntax but not membership in `T_n` or the certificate's payload dependence.

### NOGO-000009 — normalise-then-filter self-defeat

```text
addressed
```

The predicate is not a structural normaliser followed by a syntactic mixed-gate filter.  Normalisation is not the acceptance criterion.  The V2-A normalisation self-defeat pattern therefore does not directly apply.

### Residual NOGO caveat

All four answers are conditional on not weakening the D0.1 accounting.  In particular, allowing `rho`, `tau`, or proof objects to carry uncharged arbitrary truth-table advice would reopen NOGO-000006 immediately.

## 7. Razborov--Rudich / Natural Proofs review

### Constructivity

The predicate is constructive relative to the certificate verifier.  Given `w_n` and `Cert_n`, the checker can in principle verify public-index payload membership, lift equality on the promised domain, representation invariance obligations, and cost accounting.  If lift equality is made fully semantic over `{0,1}^n`, the check may be expensive; if it is made efficiently checkable by structure, then accepted targets become even more low-description.

### Largeness

The predicate is non-large enough to escape the classical Razborov--Rudich triad.  Its accepted set is tiny in `BoolFun(n)`, assuming the D0.1 caps are respected.  This is the strongest part of the design.

### Usefulness

Usefulness is the fatal weakness.  The predicate is useful only inside `T_n`, and `T_n` is designed to be sparse and low-description.  That is exactly what blocks largeness, but it also deprives the predicate of a visible route to `NP_not_subset_PpolyDAG`.

### Tradeoff

The tradeoff is:

```text
Make T_n small and payload-independent  -> RR/largeness and hardwiring are controlled,
                                           but accepted targets look too structured/easy.

Make T_n rich enough to contain a hard NP target -> usefulness improves,
                                                    but either largeness returns or the
                                                    promise starts encoding hardness.
```

So the predicate is constructive enough to check and non-large enough to avoid RR, but not useful enough to matter for the repository target.

## 8. Usefulness toward `PpolyDAG`

Verdict:

```text
likely_too_weak
```

`AlmostNaturalProvenance_BC` does not plausibly help produce

```text
ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG
```

without hiding a lower bound inside `PayloadClass` or promise membership.

### Why accepted targets may have small circuits/DAGs

The accepted target has a short description:

```text
(d, i) with |d| + |i| = polylog(n),
```

plus public evaluators and public wrappers.  If `EvalPayload`, `Lift_n`, `rho`, and `tau` are efficiently evaluable, then each accepted function is not merely low-density as a set of truth tables; it is also operationally easy to compute from its short index.  That strongly suggests accepted targets have small nonuniform circuits/DAGs obtained by hardwiring `(d,i)` and implementing the public evaluator/wrapper.

This is not a formal upper bound yet, but it is the adversarial default: a polylog-indexed public evaluator normally gives a small nonuniform algorithm for every accepted target.  Such targets cannot be the source of `NP_not_subset_PpolyDAG` unless some evaluator or promise check is itself hard in a way not captured by the certificate.

### Why making the target hard risks circularity

To get an `NP` language outside `PpolyDAG`, future work would need a lemma of the form:

```text
There exists an NP language L such that for infinitely many/all n,
L_n ∈ T_n with accepted payload-independent provenance, and no PpolyDAG
family computes L.
```

But D0.1 supplies no independent source for the final clause.  If the future proof tries to obtain it by defining `PayloadClass` as a class of pseudorandom, circuit-hard, DAG-hard, lower-bound-certified, or no-small-witness payloads, then non-circularity fails.  If it keeps `PayloadClass` as a public low-parameter evaluator, then the accepted functions look nonuniformly easy.

### Why this is not merely “unclear”

At D0, uncertainty was reasonable because the predicate had not been specified.  After D0.1, the specification is concrete enough to expose the double-bind.  Safety is achieved precisely by restricting to a sparse, short-indexed, payload-independent class.  That restriction is not an accidental missing bridge; it is the core design.  It makes the route a good hardwiring-audit toy and a poor `PpolyDAG` lower-bound source.

Therefore the usefulness verdict is `likely_too_weak`, not `plausible_path_exists` and not merely `only_distributional_side_track`.

## 9. Structural double-bind review

The strongest double-bind is:

```text
Either the certificate is genuinely cheap and payload-independent,
or the target may be useful for lower bounds, but not both.
```

More explicitly:

1. **Cheap certificate implies low-description target.**  If `(d,i)` and the proofs are polylogarithmic and public evaluators are usable, then the accepted function is specified by a tiny nonuniform advice string.  The adversarial expectation is that such a function has small `PpolyDAG` implementations.

2. **Restrictive certificate rejects hardwiring but also rejects arbitrary useful targets.**  The predicate successfully rejects generic all-essential log-width payloads, but it does so by admitting only a tiny structured subset.  A generic hard `NP` slice has no reason to land in that subset.

3. **Semantic + constructive + broadly useful would reawaken natural proofs.**  If the predicate were broadened from sparse `T_n` to a broad efficiently checkable semantic property useful against `PpolyDAG`, it would move back toward the Razborov--Rudich triad.

4. **Non-large means no automatic worst-case leverage.**  Non-largeness is the RR escape hatch, but it also means the predicate says nothing about almost every Boolean function.  A worst-case `NP` lower bound needs a separate target-location theorem, and no non-circular candidate for that theorem is visible.

5. **Payload-independence blocks the very evidence a hard target would seem to need.**  A meaningful hard target would typically need target-specific information.  The predicate either refuses that information as payload-dependent or charges it, exceeding the budget.  If the information is compressed into a public short index, the target again looks easy/nonuniformly computable.

This is a structural failure, not a request for more parameter tuning.

## 10. Final recommendation

```text
B. RED_light_fp3b7
```

I recommend **not** opening full fp3b7 Round 1 for `AlmostNaturalProvenance_BC`.

Reason by gate:

- Non-largeness: passed.
- Non-circularity: passed for the written predicate.
- Hardwiring rejection: passed with strict accounting.
- Usefulness path to `PpolyDAG`: failed / likely too weak.

A full Round 1 would spend effort formalizing a predicate that is safe mainly because it is too narrow.  That is not mainline progress toward `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, or `ResearchGapWitness.dagSeparation`.

### NoGo or archive?

Do **not** file a formal NoGoLog entry yet.  This review is markdown-level and does not provide a Lean formalized meta-barrier analogous to NOGO-000007 or NOGO-000009.  The correct action is to archive fp3b7 Family B as a red-lighted design path unless an operator explicitly wants a later formal NoGo slot.

If a future NoGo is desired, the candidate statement should target the double-bind:

```text
For short-index public payload/lift evaluators, accepted targets admit small
nonuniform DAGs; if the evaluator/promise is strengthened to avoid that, the
strengthening either becomes nonconstructive/unusable or encodes the lower bound.
```

That is a possible future audit theorem, but it is not needed to reject full Round 1 now.
