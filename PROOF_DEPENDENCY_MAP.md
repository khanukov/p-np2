# Proof Dependency Map (Active `pnp3/` Tree)

Last updated: 2026-02-19

## Final theorem path (current)

```lean
P_ne_NP_final
  -> P_ne_NP_final_asymptotic
  -> P_ne_NP_from_partial_formulas
  -> NP_not_subset_Ppoly_from_partial_formulas
  -> OPS_trigger_formulas_partial
  -> OPS_trigger_general_contra_partial
  -> LB_GeneralFromLocal_partial
  -> LB_LocalCircuits_core_partial
  -> antiChecker_exists_testset_local_partial
  -> no_bounded_atlas_on_testset_of_large_family
```

`P_ne_NP_from_partial_formulas` then combines:
- `NP_not_subset_Ppoly_from_partial_formulas`
- `P_ne_NP_of_nonuniform_separation`
- `P_subset_Ppoly_proof`

## External gaps actually on the final theorem cone

From `pnp3/Tests/AxiomsAudit.lean`:
- `P_ne_NP_final` depends on
  `[propext, Classical.choice, Quot.sound, ThirdPartyFacts.localizedFamilyWitness_partial]`.
- `P_ne_NP_final_asymptotic` depends on the same list.
- Intermediate nodes (`P_ne_NP_from_partial_formulas`,
  `NP_not_subset_Ppoly_from_partial_formulas`,
  `OPS_trigger_formulas_partial`,
  `OPS_trigger_general_contra_partial`,
  `LB_GeneralFromLocal_partial`,
  `LB_LocalCircuits_core_partial`,
  `LB_Formulas_core_partial`) depend only on
  `[propext, Classical.choice, Quot.sound]`.

So the only project-specific external gap on the final theorem cone is:
- `ThirdPartyFacts.localizedFamilyWitness_partial`
  (`pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`)

## External axioms outside current final-theorem cone

None in the active `pnp3/` tree.

## Witness-backed (non-axiom) external inputs

- `ThirdPartyFacts.partial_shrinkage_for_AC0`
- `ThirdPartyFacts.shrinkage_for_localCircuit`

Both are theorems requiring external witness objects (`FamilyIsAC0` /
`FamilyIsLocalCircuit`) and are tracked separately from explicit axioms.

## Reproducible audit commands

```bash
lake env lean pnp3/Tests/AxiomsAudit.lean
bash scripts/check.sh
```
