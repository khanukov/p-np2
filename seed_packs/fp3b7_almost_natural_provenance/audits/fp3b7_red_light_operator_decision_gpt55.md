# fp3b7 RED-light operator decision — almost-natural provenance

Handle: `gpt55`
Decision type: markdown-only operator closure decision.
Progress classification: Infrastructure / research-governance audit.  This decision does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, does not add a candidate package, and does not introduce any endpoint.

## 1. Executive decision

```text
fp3b7 status: RED-LIGHT / not expanded
Full Round 1: not authorised
NOGO entry: not filed yet
Lean code: none
```

`fp3b7_almost_natural_provenance` is closed as a red-lighted Family-B design path after D0, D0.1, and D0.1-second-review.  The seed pack remains as an audit record only.  It is not mainline progress toward the repository target and must not be cited as a `PpolyDAG` lower-bound source.

## 2. Why RED-light

The review sequence is:

```text
D0                   = INCONCLUSIVE
D0.1                 = INCONCLUSIVE_needs_more_design
D0.1 second review   = RED_light_family_B
```

The D0 report found that naive almost-natural provenance ideas were not ready for full Round 1.  It requested one concrete B/C hybrid predicate and three paper-level safety checks before any expansion.

D0.1 specified that predicate as:

```text
AlmostNaturalProvenance_BC
= Sparse Structured-Payload Promise with Payload-Independent Provenance Certificate.
```

D0.1 made the local safety case credible under strict accounting:

- the accepted class is **non-large** in the full Boolean-function universe;
- the predicate is **non-circular as written**, because membership is by positive structured-index / lift / certificate checks rather than lower-bound language;
- arbitrary all-essential log-width `ttFormula` payloads from NOGO-000006 are rejected unless they lie in the public structured payload class or explicitly pay their truth-table bits in the certificate.

The second review accepted those local safety points but found the route strategically too weak:

- accepted targets are sparse, low-description, and promise-local;
- no credible non-circular path was identified from `AlmostNaturalProvenance_BC` to `NP_not_subset_PpolyDAG`;
- making the predicate useful appears to force one of two failures:
  - broadening the property until it becomes natural-proof-shaped; or
  - encoding the desired lower bound inside `PayloadClass`, the promise tag, pseudorandomness language, or another hidden hardness condition.

Therefore fp3b7 is red-lighted not because the predicate fails every barrier check, but because the checks it passes are achieved by making the accepted class too narrow to support the repository's required `PpolyDAG` lower-bound endpoint.

## 3. What remains valid

The following documents remain valid audit artifacts:

- `seed_packs/fp3b7_almost_natural_provenance/README.md` as the seed-pack skeleton and final status pointer;
- `seed_packs/fp3b7_almost_natural_provenance/reports/D0_barrier_feasibility_gpt55.md` as the initial barrier-feasibility audit;
- `seed_packs/fp3b7_almost_natural_provenance/reports/D0_1_bc_hybrid_spec_gpt55.md` as the concrete B/C hybrid predicate specification;
- `seed_packs/fp3b7_almost_natural_provenance/reports/D0_1_second_review_gpt55.md` as the independent adversarial second review.

These artifacts are useful for future route selection because they document why sparse/promise almost-natural provenance can avoid known hardwiring and syntax barriers locally while still failing the usefulness requirement for `PpolyDAG`.

## 4. Why no NoGoLog entry now

No NoGoLog entry is filed in this decision.

Reason:

- there is no kernel-checked formal witness for a class-level fp3b7 impossibility theorem;
- the present conclusion is a markdown-level strategic red-light, not a Lean formalized meta-barrier;
- the active NoGoLog entries NOGO-000006 through NOGO-000009 remain the relevant formal hardwiring / support-cardinality / syntax / normalisation barriers, but they do not themselves formally prove the fp3b7 double-bind.

A future formal NoGo could target the double-bind identified by D0.1-second-review:

```text
cheap certificate => small nonuniform DAG;
useful hard target => circular promise / hidden lower bound.
```

Such a future NoGo would need a precise formal class of short-index public payload/lift evaluators and a theorem showing either small nonuniform realizability for accepted targets or circularity / nonconstructivity when the class is strengthened.

## 5. What not to do

The following are not authorised for fp3b7:

- no full fp3b7 Round 1;
- no Lean work under fp3b7;
- no `ProvenanceFilter` promotion;
- no FP-4;
- no `SourceTheorem`;
- no `gap_from`;
- no `ResearchGapWitness`;
- no endpoint;
- no `P≠NP` claim.

Do not reopen fp3b7 by renaming `AlmostNaturalProvenance_BC` or by moving the same promise/certificate double-bind into a new wrapper without an explicit operator decision.

## 6. Next strategic options

Exactly four options remain on the strategic menu:

A. **first_move_search refresh** — search for a genuinely new family.

B. **formalize a class-level NoGo for fp3b7 double-bind** — only if the operator wants a kernel-checked closure theorem for the short-index/payload-independent class.

C. **revisit `fp3b6_budget_repair` only if explicitly authorised** — any such revisit must pre-pin a semantic predicate and explain why it avoids the fp3b6 log-window / fingerprint-footprint bind.

D. **stop FP3b route and return to main ResearchGap source theorem search** — refocus effort on source obligations that can plausibly reduce `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
