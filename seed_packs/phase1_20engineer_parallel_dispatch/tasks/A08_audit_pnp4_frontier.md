# A08: Audit `pnp4/Pnp4/Frontier/`

**Engineer:** A08 | **Phase:** 0 | **Estimated:** 1 week | **Difficulty:** medium | **Type:** markdown-only

## Goal

Audit `pnp4/Pnp4/Frontier/` including all `ContractExpansion/` modules. Map how AC⁰[p] / MCSP / compression magnification connects to bridge requirements and to the contract_expansion track.

## Files

```
pnp4/Pnp4/Frontier/CompressionMagnification.lean
pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean
pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean
pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean
pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A08_pnp4_frontier_<handle>.md`

### Required sections

1. **Executive summary**: is the pnp4 Frontier complete for source-theorem production?
2. **File-by-file audit**.
3. **Critical theorem map**:
   - `SearchMCSPMagnification`: the magnification contract surface.
   - `PvsNPBridgeRequirements`: the `VerifiedNPDAGLowerBoundSource` structure.
   - `CompressionMagnification`: compression-style magnification.
   - `SearchMCSPConcreteTargets`: tree-MCSP target instance.
4. **ContractExpansion track audit**:
   - R1-A `C_DAG_Adapter`: alignment status.
   - R1-B `PrefixExtensionLanguage`: language definition + NP budget.
   - R1-B1 `PrefixExtensionLanguageNP`: codec-case `Decidable`.
   - R1-B2a `PrefixExtensionLanguageRuntime`: runtime budget.
   - What's staged as `Prop`, what's discharged.
5. **Gap to `ResearchGapWitness`**: precisely what's missing.
6. **Cross-track integration**: how do `AlgorithmsToLowerBounds/` (A07) feed into Frontier; how does pnp3 `_Partial.lean` (A01) integrate?
7. **Phase 1+ recommendations**.
8. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] All 8 listed files audited.
- [ ] Bridge map: `AC⁰[p] LB → magnification contract → `VerifiedNPDAGLowerBoundSource` → `ResearchGapWitness` — diagram with what's proven vs staged at each arrow.
- [ ] At least 4 Phase 1+ recommendations.

## Scope

### Allowed
- Reading `pnp4/Pnp4/Frontier/*` + dependencies.

### Forbidden
- Universal.

## Output
Universal template.
