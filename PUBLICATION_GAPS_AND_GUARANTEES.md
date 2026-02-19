# Publication Gaps And Guarantees

Last updated: 2026-02-19

This document is the publication-facing contract for what is proven in Lean and
what is still external.

## Machine-checked guarantees

- Active tree `pnp3/` builds successfully: `lake build`.
- No `sorry`/`admit` placeholders in `pnp3/*.lean`.
- Axiom inventory is pinned and CI-checked.
- Axiom dependency profile of critical theorems is pinned and CI-checked via
  `pnp3/Tests/AxiomsAudit.lean`.

## Narrow project-specific gaps (explicit)

Active explicit axioms in `pnp3/`:

1. `ThirdPartyFacts.PartialMCSP_profile_is_NP_Hard_rpoly`
2. `ThirdPartyFacts.PartialMCSP_is_NP_Hard`
3. `ThirdPartyFacts.localizedFamilyWitness_partial`

Locations:
- `pnp3/ThirdPartyFacts/Hirahara2022.lean`
- `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`

## Final-theorem dependency profile (audited)

From `#print axioms`:

- `P_ne_NP_final` and `P_ne_NP_final_asymptotic` depend on
  `[propext, Classical.choice, Quot.sound, ThirdPartyFacts.localizedFamilyWitness_partial]`.
- Core bridge/lower-bound nodes in the same chain depend only on
  `[propext, Classical.choice, Quot.sound]`.

This means the final theorem cone has one project-specific external gap:
`localizedFamilyWitness_partial`.

## Non-axiom external witness interfaces

Theorems:
- `ThirdPartyFacts.partial_shrinkage_for_AC0`
- `ThirdPartyFacts.shrinkage_for_localCircuit`

These are theorem statements with external witness parameters (`FamilyIsAC0`,
`FamilyIsLocalCircuit`) and are tracked separately from explicit axioms.

## Reproducibility commands

```bash
lake build
bash scripts/check.sh
lake env lean pnp3/Tests/AxiomsAudit.lean
```
