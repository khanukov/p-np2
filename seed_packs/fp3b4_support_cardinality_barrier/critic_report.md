# Critic report — fp3b4 support-cardinality barrier

This report evaluates the audit-only T6 integration for
`seed_packs/fp3b4_support_cardinality_barrier/`.  The reviewed artifact is not a
candidate package and does not claim a lower-bound endpoint; it formalizes a
local meta-barrier for support-cardinality-only FP-N provenance filters.

## Attack 1: Hidden-payload attack

- **status:** `no break found`
- **summary:** I checked whether the T6 theorem hides mathematical content in typeclasses, instances, opaque constants, or implicit payload channels. The Lean module is fully explicit: it imports the T5 barrier and the existing FP3 audit predicate, then proves two ordinary theorems with no new hidden channel.
- **evidence:**
    - `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean:39` states the support-cardinality-only theorem directly for `@FP3Attempt.InSupportFunctionalDiversity`.
    - `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean:89` states the hardwiring-twin theorem with explicit `hHonest` and `hSubLinear` hypotheses.
    - Repository scans include `rg -n "\\bsorry\\b|\\badmit\\b" -g"*.lean" pnp3 pnp4`; no proof-hole matches are introduced by this T6 work.

## Attack 2: Hardwiring attack

- **status:** `no break found`
- **summary:** The hardwiring attack is the intended obstruction rather than a defect. T6 shows that this support-cardinality filter admits a canonical hardwiring twin whenever it admits an honest sublinear-support witness.
- **evidence:**
    - `any_honest_sublinear_support_witness_has_hardwiring_twin` applies T5 to `@FP3Attempt.InSupportFunctionalDiversity`, so the hardwiring conclusion is exactly the audited outcome.
    - The proof depends on `canonicalHardwiringWitness`, not on a lower-bound bridge or on any final endpoint.
    - The NoGoLog entry for NOGO-000007 records this as `failure_class = "hardwiring"` and explicitly limits the conclusion to FP-N filter design.

## Attack 3: KnownGuards-factorization attack

- **status:** `no break found`
- **summary:** I checked whether the theorem merely factors through a known guard or a special hardwired family instead of proving the claimed parametric barrier. The T5 theorem remains parametric in `Filter`; T6 only supplies the independent proof that the concrete FP3 filter is support-cardinality-only.
- **evidence:**
    - `support_cardinality_barrier` quantifies over an arbitrary `Filter : ∀ {L : Language}, InPpolyFormula L → Prop` and requires only `IsSupportCardinalityOnly Filter`.
    - `inSupportFunctionalDiversity_is_support_cardinality_only` proves that the FP3 filter satisfies this T4 invariant by transporting the two defining support-cardinality conjuncts.
    - No edit promotes `ProvenanceFilter_v1`, designs `ProvenanceFilter_v2`, or adds a new KnownGuards item.

## Attack 4: Natural-proof / relativization / algebrization barrier audit

- **status:** `attack not applicable`
- **summary:** The reviewed artifact is a local audit meta-theorem about syntactic support-cardinality filters, not a lower-bound proof. It does not assert constructivity/largeness/usefulness, relativizing separation, or an algebrizing lower-bound route.
- **evidence:**
    - The module comment states that no `SourceTheorem`, no `gap_from_*` bridge, no `ResearchGapWitness`, and no final P-vs-NP endpoint is introduced.
    - The result lives under `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/`, an audit-route namespace rather than a mainline lower-bound namespace.
    - The theorem conclusion is membership in `FP3Attempt.InSupportFunctionalDiversity` for a canonical witness, not a circuit lower bound.

## Attack 5: Collapse-not-contradiction audit

- **status:** `no break found`
- **summary:** I checked whether the integration converts a collapse consequence or a heuristic impossibility into a contradiction. It does not mention PH collapse, `NP_not_subset_PpolyDAG`, `P_ne_NP`, or any contradiction endpoint.
- **evidence:**
    - The T6 theorem concludes only `FP3Attempt.InSupportFunctionalDiversity (canonicalHardwiringWitness ...)`.
    - The NoGoLog text frames the result as a hardwiring obstruction for support-cardinality-only filter candidates.
    - No trust-root definition or final result module is edited.

## Attack 6: Vacuity / source-theorem rephrasing audit

- **status:** `no break found`
- **summary:** I checked whether the theorem proves the canonical witness predicate vacuously or by rephrasing a source theorem. The proof uses the non-vacuous assumption `hHonest`; without that premise the T5 transport has no source membership to move.
- **evidence:**
    - `any_honest_sublinear_support_witness_has_hardwiring_twin` takes `hHonest : FP3Attempt.InSupportFunctionalDiversity w_honest` and passes it directly to `support_cardinality_barrier`.
    - There is no theorem named `SourceTheorem_*`, no `gap_from_*` bridge, and no candidate directory added.
    - The critic checked that the result is conditional on an honest sublinear-support witness and does not assert unconditional hardwiring membership for every profile.

## Verdict

- **critic_status:** `pass`
- **next_recommended_action:** Treat support-cardinality-only FP-N filters as ruled out; future filter design must inspect structure beyond support cardinality.
