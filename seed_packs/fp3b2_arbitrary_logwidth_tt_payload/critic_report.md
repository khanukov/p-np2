# Critic report — fp3b2_arbitrary_logwidth_tt_payload / T6

Audit-only seed-pack route.  This report evaluates the T6 integration theorem
that formalizes arbitrary all-essential log-width `ttFormula` payloads against
`FP3Attempt.InSupportFunctionalDiversity`.  It does not evaluate a candidate
package, source theorem, gap bridge, or final endpoint.

## Attack 1: Hidden-payload attack

- **status:** `no break found`
- **summary:** I checked whether the result smuggles the payload through an implicit channel such as a typeclass, instance, fact wrapper, opaque constant, or hidden source assumption.  The T6 theorem quantifies explicitly over `F : PayloadFamily` and `hF : AllEssentialPayload F`; the only payload dependence is passed through these visible arguments.
- **evidence:**
    - `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean` imports only the T1--T5 route, the existing S8/S9 reducers, and the audit probe surface.
    - The proof uses the explicit T4 support-card theorem and the T5 witness record; it does not add `class`, `instance`, `Fact` payloads, `opaque`, `axiom`, `sorry`, or `admit`.

## Attack 2: Hardwiring attack

- **status:** `no break found`
- **summary:** This attack is the intended obstruction, not a refutation of the report.  The formal artifact shows that arbitrary all-essential log-width truth-table hardwiring satisfies the support-diversity filter, so a support-cardinality-only filter is dead in the full arbitrary-payload setting.
- **evidence:**
    - The headline theorem is `arbitraryLogWidthTT_satisfies_diversity`, proving `FP3Attempt.InSupportFunctionalDiversity (adversaryWitness_v_arbpayload F hF)` for arbitrary all-essential payload families.
    - The result supersedes the scope-corrected prefix-AND obstruction NOGO-000005 by replacing the special `prefixAnd` payload with arbitrary `F n : Bitstring (widthFn n) → Bool` under `AllEssentialPayload F`.

## Attack 3: KnownGuards-factorization attack

- **status:** `no break found`
- **summary:** I checked whether the theorem only rephrases an existing guard or accidentally promotes a KnownGuards factorization as a new positive route.  It does neither: it records a negative audit obstruction against support-cardinality filtering and does not define or promote any provenance filter.
- **evidence:**
    - The theorem composes `adversary_support_unbounded`, `adversary_support_below_n_io`, `logWidth_unbounded`, and `logWidth_lt_self` with the exact support-card identity.
    - `ProvenanceFilter_v2` remains not started; this report recommends starting its design only after this obstruction, and still without FP-4, `SourceTheorem`, or `gap_from` work.

## Attack 4: Natural-proof / relativization / algebrization barrier audit

- **status:** `attack not applicable`
- **summary:** The artifact is not a lower-bound proof attempt and makes no claim of escaping natural-proof, relativization, or algebrization barriers.  It is a kernel-checked counterexample shape for an audit filter.
- **evidence:**
    - The Lean theorem stays in `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean` and proves only a support-diversity property of a polynomial-size formula witness.
    - No `ResearchGapWitness`, `SourceTheorem`, `NP_not_subset_PpolyDAG`, or `P_ne_NP` endpoint is introduced.

## Attack 5: Collapse-not-contradiction audit

- **status:** `no break found`
- **summary:** I checked whether the result mistakes a collapse-style construction for a contradiction or final lower bound.  The report states the correct interpretation: the filter admits the hardwired family, so the filter is insufficient; no complexity collapse or contradiction is claimed.
- **evidence:**
    - The conclusion is an inclusion in `FP3Attempt.InSupportFunctionalDiversity`, not a refutation of `PpolyFormula`, `PpolyDAG`, or any NP containment.
    - The NoGoLog upgrade is classified as `failure_class = hardwiring` and `method_family = ac0_locality_support`, preserving the audit-obstruction semantics.

## Attack 6: Vacuity / source-theorem rephrasing audit

- **status:** `no break found`
- **summary:** The theorem is not vacuous: the all-essential hypothesis is consumed through the T4 exact support-cardinality lemma, and the witness is the concrete T5 `InPpolyFormula` record.  It is also not a source-theorem rephrasing because it has no final endpoint or bridge.
- **evidence:**
    - T4 proves `(support (adversaryFamily_v_arbpayload F n)).card = widthFn n` from `AllEssentialPayload F`; T6 uses that identity in both diversity reducers.
    - Key conclusion: arbitrary all-essential log-width `ttFormula` payload satisfies `InSupportFunctionalDiversity`; therefore support-cardinality-only filtering fails even for the full arbitrary-payload setting.

## Verdict

- **critic_status:** `pass`
- **next_recommended_action:** Start FP-3b.3 ProvenanceFilter_v2 design; still no FP-4, SourceTheorem, gap_from, or final endpoint.
