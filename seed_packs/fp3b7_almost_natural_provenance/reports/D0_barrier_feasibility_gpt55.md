# fp3b7-D0 barrier feasibility report — almost-natural provenance / Family B

Slot: `fp3b7-D0`
Handle: `gpt55`
Progress classification: Infrastructure / markdown-only feasibility audit. This report does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, does not promote a provenance filter, and does not claim an endpoint.

## 1. What is almost-natural provenance?

Almost-natural provenance is a candidate provenance-filter route that tries to use a semantic property of how a lower-bound witness is obtained, while deliberately breaking at least one member of the Razborov--Rudich triad: constructivity, largeness, or usefulness against the full target class.

The intended object is not a property of displayed formula syntax. It is also not just a property of the support-cardinality profile. The candidate filter should ask whether an alleged hardwiring/provenance witness has a low-complexity, representation-invariant explanation relative to a restricted distribution, promise set, sparse target ensemble, or witness-generation process. In short:

```text
Almost-natural provenance = semantic provenance evidence
                            + explicit charge for witness-generation resources
                            + restriction to a non-large ensemble/promise/distribution
                            + no collapse to displayed syntax or support size alone.
```

The route is meant to occupy the gap left after the fp3b6 Family-A stall. In fp3b6, the local anti-collapse statement was valid only when the fingerprint footprint fit into the logarithmic hardwiring window, while Atserias--Müller-style magnification footprints exceeded that window. Family B therefore should not merely tune `m`, `k`, or `ρ`; it must change what is charged and what ensemble the usefulness statement ranges over.

Negative boundary conditions:

- It must not be support-cardinality-only, because NOGO-000007 says any such filter admitting an honest sublinear-support witness admits a hardwiring twin with the same support profile.
- It must not be displayed-syntax-only, because NOGO-000008 says tautological rewrites can preserve the Boolean function while adding the forbidden/required displayed gate shapes.
- It must not be normalise-then-syntax-filter, because NOGO-000009 says the structural normalisation patch destroys the filter's own non-vacuity witness in the V2-A pattern.
- It must not be an unrestricted semantic quotient over all Boolean functions with an efficient decision procedure and broad usefulness, because that is exactly the shape that risks becoming a natural proof.

A viable almost-natural predicate would therefore be semantic but deliberately non-large, or useful only on a promise/sparse ensemble, or constructive only with an expensive/nonuniform witness charge that is not available for arbitrary hardwired payloads.

## 2. Candidate semantic predicates

Candidate A — distribution-restricted usefulness.

- Shape: the predicate accepts a witness only relative to an explicit distribution family `D_n` over inputs/functions/witness instances. Usefulness means separating the target family from low-cost circuits on `D_n`, not over all truth tables.
- What it charges: description length of `D_n`, sampler/evaluator cost, witness-generation cost under the distribution, and advantage/farness under `D_n`.
- Intended escape: not large over all Boolean functions; it is only meaningful on a specified distributional slice.
- Main risk: if `D_n` is broad enough to exclude arbitrary hardwiring, it may become large or natural-shaped; if `D_n` is narrow enough to stay non-large, usefulness may be too weak for any `PpolyDAG` bridge.

Candidate B — promise-set / sparse-target usefulness.

- Shape: the predicate is evaluated only on a sparse or promise-defined target ensemble `T_n`, such as functions/languages satisfying an externally specified semantic promise. The filter does not classify all Boolean functions.
- What it charges: promise membership evidence, density of `T_n`, radius of the promise, and the cost of verifying that a witness is within the promised ensemble.
- Intended escape: largeness is blocked because the target set is intentionally sparse or promise-limited.
- Main risk: the promise may do all the work. If the promise already encodes non-membership in low-cost circuits, the lower bound is hidden inside the definition rather than proved.

Candidate C — witness-dependent but representation-invariant provenance.

- Shape: the predicate depends on a semantic witness relation rather than formula syntax. Equivalent formulas presenting the same Boolean function and the same semantic witness status are treated identically, but the witness relation is not all-functions extensional in the natural-proof sense; it includes an external provenance certificate.
- What it charges: certificate length, certificate verification cost, dependence/independence of the certificate from payload-specific truth-table bits, and invariance under semantic equivalence of representations.
- Intended escape: avoids NOGO-000008 because tautological rewrites do not change semantic witness status; avoids NOGO-000009 because no bottom-up syntactic normaliser is the decision procedure.
- Main risk: if the certificate can be tailored after seeing an arbitrary payload, NOGO-000006 returns; if tailoring is forbidden, proving non-tailoring may require a hidden lower bound or an unformalized independence notion.

Candidate D — cost-charged non-large semantic fingerprint.

- Shape: the predicate accepts only if a semantic fingerprint exists whose construction and query process have a charged cost lower than the cost of merely hardwiring the relevant truth table. The charge is not support-cardinality; it includes sampled-coordinate description length, construction uniformity, matrix/fingerprint description complexity, and payload independence.
- What it charges: fingerprint construction cost, sampled-coordinate description length, query fan-in, matrix description length, payload-independence evidence, and verification cost.
- Intended escape: it directly addresses the fp3b6 lesson by charging the footprint/provenance that D3′-A treated too coarsely.
- Main risk: if the charge is low enough to admit Atserias--Müller-scale objects, it may also inspect the whole logarithmic payload window; if it is strict enough to block hardwiring, it may reject the useful magnification witnesses.

## 3. Natural parameter regime

Candidate A — distribution-restricted usefulness.

- Input length: ambient length `n`, with an auxiliary distribution seed length preferably `polylog(n)` or explicitly charged if larger.
- Witness size/cost: sampler plus verifier should be at most polynomial time for constructivity, but any nonuniform advice in the sampler must be charged.
- Density/sparsity of target family: not dense in the full truth-table universe; density is measured only inside the distributional support.
- Distributional support: could be polynomial-size, quasipolynomial-size, or efficiently samplable. Full support over all `2^n` inputs risks natural-proof largeness.
- Promise radius: advantage/farness should be measured under `D_n`; a full Hamming-ball radius over all truth tables risks becoming a large semantic property.
- Circuit/formula cost: usefulness would need to talk about `PpolyDAG`-scale adversaries eventually, but D0 cannot show that distributional usefulness lifts to worst-case DAG lower bounds.
- Polynomial-size hardwiring compatibility: compatible only if arbitrary payload hardwiring is not admitted by the distribution witness; otherwise NOGO-000006 remains.

Candidate B — promise-set / sparse-target usefulness.

- Input length: `n` for the ambient function, plus a promise index or sparse-ensemble descriptor.
- Witness size/cost: promise membership proof must be smaller than a truth-table payload and cannot simply be a certificate of hardness.
- Density/sparsity of target family: deliberately sparse; this is the intended non-largeness mechanism.
- Distributional support: optional, but if present it must be part of the promise rather than an after-the-fact syntactic filter.
- Promise radius: should be narrow enough to avoid largeness, but not so narrow that usefulness is vacuous.
- Circuit/formula cost: must not define `T_n` by excluding small circuits, or the route becomes circular.
- Polynomial-size hardwiring compatibility: promising in principle, because arbitrary all-essential log-width payloads need not satisfy the promise; but this must be proved semantically, not by support size.

Candidate C — witness-dependent representation-invariant provenance.

- Input length: ambient length `n`; witness certificate may have its own length `c(n)`.
- Witness size/cost: `c(n)` should be polynomially bounded for constructivity, but too small/structured to encode an arbitrary log-width truth table unless that encoding is explicitly charged.
- Density/sparsity of target family: depends on the certificate relation. If many random functions have certificates, largeness returns; if few do, usefulness becomes harder.
- Distributional support: not essential, but a restricted ensemble may be needed to keep the property non-large.
- Promise radius: semantic equivalence should be exact for rewrites; farness/radius enters only through the certificate relation.
- Circuit/formula cost: eventual target is `PpolyDAG`, but the D0 evidence only supports an audit predicate, not a lower-bound bridge.
- Polynomial-size hardwiring compatibility: the key constraint is certificate non-adaptivity to payload bits. Without that, arbitrary log-width payloads may be certifiable.

Candidate D — cost-charged non-large semantic fingerprint.

- Input length: ambient `n`; fingerprint output length, sampled length, and matrix dimensions must be separately tracked.
- Witness size/cost: charge the full provenance cost: matrix/fingerprint description, sampled-coordinate generation, query fan-in, and verification.
- Density/sparsity of target family: non-large if restricted to fingerprints with cheap independent provenance, not to all functions satisfying a truth-table property.
- Distributional support: may be a sampled fingerprint ensemble rather than all coordinates.
- Promise radius: must avoid the fp3b6 mismatch where the useful AM radii/footprints exceed the log-window anti-collapse budget.
- Circuit/formula cost: the construction should remain polynomial-size, but the report has no evidence that useful AM-scale witnesses survive a cost charge strong enough to reject hardwiring.
- Polynomial-size hardwiring compatibility: this is the central tension. Arbitrary truth-table hardwiring stays polynomial only in a logarithmic window; any fingerprint allowed to read that whole window defeats the old hiding argument.

## 4. Structural double-bind search

The strongest apparent double-bind is common to all four candidate families:

```text
To exclude arbitrary log-width hardwiring, the predicate must notice semantic
provenance beyond support size and displayed syntax.

But if that semantic predicate is constructive, useful against broad low-cost
circuits, and applies to a non-negligible fraction of functions, it becomes
natural-proof-shaped.

If it is narrowed enough to avoid largeness, the route may no longer imply a
useful lower-bound bridge against PpolyDAG.
```

Candidate-specific double-binds:

- Candidate A: useful distributional predicates want broad support and efficient testing; those features move toward largeness/constructivity. Restricting the distribution blocks largeness but may only prove an average-case or promise statement with no worst-case DAG consequence.
- Candidate B: sparse promise predicates can be non-large, but the promise risks encoding the desired hardness. If promise membership is easy and non-circular, usefulness is unclear; if usefulness is clear, the promise may be doing lower-bound work by definition.
- Candidate C: representation-invariant certificates avoid tautological rewrites, but payload-independent certificate discipline is the load-bearing part. If certificates are allowed to depend on payload-specific truth-table bits, the NOGO-000006 adversary can probably manufacture certificates. If certificates cannot depend on those bits, the proof of independence may be as hard as the lower bound.
- Candidate D: cost-charged fingerprints are the closest continuation of fp3b6, but they inherit a sharper form of the fp3b6 double-bind. A charge permissive enough for AM-scale fingerprints likely lets the fingerprint inspect the whole logarithmic hardwiring window; a charge strict enough to preserve hiding likely rejects the useful fingerprints.

Pessimistic conclusion: Family B does not currently have a clean fp3b6-style numerical contradiction, but it has a barrier triad double-bind. The route survives only if a restricted semantic predicate can give enough usefulness for the eventual `PpolyDAG` bridge while proving non-largeness and non-circularity in a way that does not merely restate hardness.

## 5. NOGO-000006/7/8/9 cross-check

NOGO-000006 — arbitrary all-essential log-width payload: partially addressed.

- Reason: Candidates B, C, and D have plausible mechanisms to reject arbitrary log-width payloads: promise membership, payload-independent certificates, or charged fingerprint provenance. However, none currently includes a formal non-adaptivity or non-circularity theorem. Candidate A is especially vulnerable if the distribution can be chosen after seeing the payload or has support broad enough to include arbitrary payload behavior.

NOGO-000007 — support-cardinality-only meta-barrier: addressed at the design-sketch level.

- Reason: none of the candidate predicates is allowed to depend only on support cardinality. Each charges distribution, promise, certificate, semantic provenance, matrix/fingerprint description, or payload independence. This does not prove success, but it avoids the exact support-profile collapse of NOGO-000007.

NOGO-000008 — tautological rewrite attack: partially addressed.

- Reason: Candidates A, B, C, and D are intended to be semantic or witness-semantic rather than displayed-syntax filters, so conjoining `(x_0 OR NOT x_0)` should not by itself change acceptance. The weakness is Candidate C/D certificate handling: if the certificate format includes representation artifacts, rewrite fragility can return through the witness language even if the Boolean function is unchanged.

NOGO-000009 — normalise-then-filter self-defeat: partially addressed.

- Reason: the route does not propose a structural normaliser composed with a syntactic filter, so the exact V2-A.1 normalisation meta-barrier does not apply directly. But a semantic quotient over all Boolean functions can self-defeat in a different way by becoming a natural-proof property; and any attempt to preprocess certificates by a canonical normal form could reintroduce normalisation fragility.

Overall NOGO cross-check result: no candidate is immediately killed by the exact NOGO-000007/8/9 patterns, but NOGO-000006 remains only partially addressed, and NOGO-000008/9 can return if implementation leaks back into representation-sensitive certificates or canonical syntactic preprocessing.

## 6. Razborov–Rudich / Natural Proofs analysis

Constructivity.

- Candidate A is likely constructive if the distribution sampler and predicate verifier are efficient. That is useful operationally but dangerous for the natural-proofs triad.
- Candidate B can be constructive if promise membership is efficiently checkable. If membership is not efficiently checkable, the route may avoid constructivity but becomes hard to use as a formal provenance filter.
- Candidate C is constructive only relative to certificate verification. This may be acceptable if certificate production is charged separately, but certificate verification alone can still provide the constructive property.
- Candidate D is likely constructive if the fingerprint and cost accounting are explicit and efficiently checkable.

Largeness.

- The intended escape is to fail largeness. Candidate B is strongest here because a sparse promise-set can be intentionally non-large. Candidate A may fail largeness only if its distributional support is narrow or nonuniformly restricted. Candidate C/D fail largeness only if few functions have low-cost independent certificates/fingerprints.
- The danger is that an unrestricted semantic quotient over all Boolean functions with many acceptable witnesses becomes large. Semanticity alone is not safety; it may be the path back into natural proofs.

Usefulness.

- All candidates need usefulness strong enough to matter for low-cost circuits, eventually `PpolyDAG`. This is currently the least supported leg.
- If usefulness is stated only inside a promise/distribution, it may not imply the required worst-case lower-bound source. If usefulness is broadened to all low-cost circuits/functions, it may combine with constructivity and largeness.

Does Family B re-enter the natural-proofs barrier?

- Yes, for the unrestricted semantic-quotient version: constructive + broadly useful + semantically large is natural-proof-shaped. That version should be treated as killed for this repository's purposes unless a concrete anti-largeness theorem is supplied.
- Not necessarily, for sparse/promise/cost-charged versions: largeness can be structurally blocked if the predicate ranges only over a restricted ensemble or requires rare low-cost independent provenance. But that does not prove the route works; it transfers the burden to showing usefulness without secretly reintroducing largeness or circular hardness.

Does that kill Family B?

- It kills the naive version. It does not conclusively kill the restricted promise/cost-charged versions, but they are not yet green-lightable. The missing object is a non-large usefulness theorem that is neither representation-sensitive nor circular.

## 7. Relativization / algebrization quick check

The current Family-B sketches do not state any non-relativizing or non-algebrizing step. A distribution, promise, certificate, or cost-charge predicate can be formulated in an oracle-parametric way unless the design explicitly uses a non-relativizing ingredient.

Therefore no bypass should be claimed. At D0 level, the honest status is:

- Relativization: uncertain / no bypass witness. The route has not identified two oracle worlds or an oracle-sensitive step analogous to a `RelativizationBypassWitness`.
- Algebrization: uncertain / no bypass witness. The route has not identified an algebraic-oracle-sensitive step analogous to an `AlgebrizationBypassWitness`.

This does not by itself refute the route, because the D0 task is a provenance-filter feasibility check rather than a final lower-bound proof. But it prevents any claim that Family B has cleared the classical oracle barriers.

## 8. Relation to fp3b5 strategic audit

Answer: unclear, needs another feasibility pass.

fp3b5 ranked Family B below Family A because the distinguisher-matrix route had a more concrete magnification interface. The fp3b6 stall changes the comparison: Family A's visible parameter regime now has a documented log-window/fingerprint-footprint double-bind, so its expected value is lower than it was in fp3b5.

However, this does not automatically make Family B the best remaining route. Family B trades the fp3b6 numerical double-bind for a natural-proofs/provenance double-bind: semantic enough to avoid rewrite attacks may be natural enough to trigger Razborov--Rudich; non-large enough to avoid Razborov--Rudich may be too weak for `PpolyDAG`; cost-charged enough to reject hardwiring may hide the lower bound in the definition.

Thus fp3b6's stall justifies investigating Family B, but D0 does not justify opening a full Round 1 yet.

## 9. Verdict

INCONCLUSIVE

## 10. Recommended next action

Minimum missing evidence before a full Round 1 could be responsibly designed:

1. Pick exactly one strongest predicate family, preferably Candidate B/C hybrid: a sparse promise-set or restricted ensemble with a representation-invariant, payload-independent provenance certificate.
2. Write a short mathematical specification, still markdown-only, proving three non-formal lemmas on paper:
   - non-largeness: the accepted set is not large in the full Boolean-function universe;
   - non-circularity: promise/certificate membership does not encode the desired circuit lower bound;
   - hardwiring rejection: arbitrary all-essential log-width truth-table payloads cannot satisfy the promise/certificate relation unless their payload-specific information is explicitly charged.
3. Separately state what kind of usefulness is expected and whether it can plausibly bridge to `PpolyDAG`. If the usefulness remains only distributional/promise-local, the route should be treated as side-track or RED-light for mainline purposes.
4. Do not open a full Round 1 until those three paper lemmas exist. If the next pass cannot state them without embedding hardness in the definition, fp3b7 should be RED-lighted.
