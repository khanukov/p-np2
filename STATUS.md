# Project Status (current)

This file is the authoritative status snapshot.

## Date

- 2026-02-23

## Active result

- Pipeline: `PNP3` (`SAL -> Covering-Power -> anti-checker -> magnification`)
- Strategic target class: **AC0 only**
- Main final module: `pnp3/Magnification/FinalResult.lean`
- Active AC0 hooks in `FinalResult.lean`:
  - `NP_not_subset_AC0_final`
  - `NP_not_subset_AC0_final_with_provider`
  - `NP_not_subset_AC0_final_of_engine`
  - `NP_not_subset_AC0_final_with_provider_of_tmWitnesses`
  - `NP_not_subset_AC0_final_of_engine_of_tmWitnesses`
  - `NP_not_subset_AC0_at_param_with_provider`
  - `NP_not_subset_AC0_at_param_of_engine`
  - `NP_not_subset_AC0_at_param_with_provider_of_tmWitness`
  - `NP_not_subset_AC0_at_param_of_engine_of_tmWitness`
  - `strictGapNPFamily_of_tmWitnesses`

## Verified code hygiene

- Active `axiom` declarations in `pnp3/`: **0**
- Active `sorry`/`admit` in `pnp3/`: **0**
- `lake build` and `./scripts/check.sh` pass on current tree

## Closed items

1. I-1 closed (localized bridge)
- `pnp3/ThirdPartyFacts/PpolyFormula.lean` now has `trivialFormulaizer` and
  `gapPartialMCSP_realization_trivial`.
- Bridge usage is wired through trivial realization variants in
  `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`.

2. I-3 closed at contract/automation layer
- `HalfTableCertificateBound` is wired from certificate providers.
- Auto wrapper exists: `locality_lift_partial_of_certificate_auto`.
- Main certificate route no longer needs manually threaded `hCardHalf`.

3. I-4 fully closed on AC0 path
- Constructive common-CCDT multi-switching chain is wired end-to-end for
  explicit CNF/AC0 families (`stage1_6_complete_*_common*`).
- New bridge module:
  `pnp3/Magnification/AC0LocalityBridge.lean`.
- **I-4 (Multi-Switching + Locality Provider) конструктивно закрыт в текущем
  AC0-scope через модуль `AC0LocalityBridge`**.
- Active common route has no external `henc_small` hypotheses.
- Partial anti-checker cleanup: legacy `..._of_false` wrappers were removed;
  active `large-Y` and testset interfaces no longer extract witnesses via
  `False.elim`.

## Complexity-interface integrity (updated)

- Canonical NP is TM-faithful in code:
  - `NP := NP_TM`
  - `NP_strict := NP_TM`
- Partial-MCSP NP API is TM-only and constructive-by-witness:
  - `gapPartialMCSP_in_NP` / `gapPartialMCSP_Asymptotic_in_NP` are aliases to `NP_TM`
  - explicit witness packages are required (`GapPartialMCSP_TMWitness`,
    `GapPartialMCSP_Asymptotic_TMWitness`)
- Legacy Lean-level verifier scaffolding for NP evidence is removed in
  `Model_PartialMCSP` to prevent vacuous NP interpretations.

## Scope boundary (intentional)

1. No global conversion `Ppoly -> AC0` (intentional)
- We consciously do **not** formalize a general conversion
  `PpolyFormula -> AC0`.
- Our hardness-magnification formalization is targeted specifically at
  lower bounds against `AC^0` families.

2. Non-AC0 wrappers stay separate
- Bridges needed for unconditional `P != NP` over full `P/poly`
  (`NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`) are tracked as a
  separate layer and are not part of the AC0-closed core claim.

## Final theorem interpretation

- AC0-focused fully machine-checked claim is the active target.
- We intentionally do not claim a global `P/poly -> AC0` transport theorem.
- Final `P != NP` wrappers are conditional and require an explicit bridge
  `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.
- Naming rule: theorem names containing `...PpolyFormula_final...` in
  `pnp3/Magnification/FinalResult.lean` denote AC0-route
  formula-separation wrappers, not standalone global non-uniform claims.

## Conditional Final Contract (`P != NP`)

- Canonical assumption bundle in code:
  `pnp3/Magnification/FinalResult.lean`:
  `ConditionalPneNpFinalContract`.
- Required fields are:
  1. `hasDefaultStructuredLocalityProviderPartial`
  2. `AsymptoticFormulaTrackHypothesis`
  3. `StrictGapNPFamily`
  4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`
- Contract-based theorem:
  `P_ne_NP_final_of_contract`.

## Next priority order

1. Keep all active reporting and theorem interfaces AC0-centric.
2. Preserve strict separation between AC0 core and non-AC0 bridge layers.
3. Add non-AC0 wrappers only as explicitly labeled optional modules.
