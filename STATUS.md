# Project Status (current)

This file is the authoritative status snapshot.

## Date

- 2026-02-26

## Active result

- Pipeline: `PNP3` (`SAL -> Covering-Power -> anti-checker -> magnification`)
- Strategic target class: **AC0 only**
- Main final module: `pnp3/Magnification/FinalResult.lean`
- Active constructive-semantic hooks in `FinalResult.lean`:
  - `NP_not_subset_PpolyFormula_from_params_semantic`
  - `NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy`
  - `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic`
  - `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy`
  - `NP_not_subset_PpolyFormula_final`
  - `P_ne_NP_final`
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

4. Step-C vacuity issue (audit) resolved architecturally
- Step-C core is now grounded in `AC0SyntacticEasyFamily` with explicit
  family-level data packages (`AC0EasyFamilyDataPartial`).
- Added legal compression interface:
  `AC0CompressionHypothesis` in
  `pnp3/LowerBounds/AntiChecker_Partial.lean`.
- `syntacticEasy` routes no longer thread ad-hoc `hCard/cardAt`; they now
  consume the compression hypothesis directly.
- Final Step-C internalization now stores syntactic payload directly in
  `SmallAC0Solver_Partial` (`circuit`, `decide_eq`, `easyData`), so closed
  contradiction routes no longer depend on legacy `..._of_hypotheses` bridges.

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

## I-5 interface progress (depth-aware)

- Added explicit depth-bounded strict class in
  `pnp3/Complexity/Interfaces.lean`:
  - `InPpolyFormulaDepth`
  - `PpolyFormulaDepth`
  - `NP_not_subset_PpolyFormulaDepth`
  - constructive bridge contract `Ppoly_to_PpolyFormulaDepth`
  - derived separation bridge
    `NP_not_subset_Ppoly_of_Ppoly_to_PpolyFormulaDepth`
  - strict/light bridge lemmas for depth-bounded separation.
- Added depth-aware conditional final wrappers in
  `pnp3/Magnification/FinalResult.lean`:
  - `P_ne_NP_final_depth_with_provider`
  - `P_ne_NP_final_depth_with_provider_of_bridge` (canonical lift)
  - `P_ne_NP_final_depth`
  - `P_ne_NP_final_depth_of_bridge` (canonical lift)
  - `ConditionalPneNpDepthFinalContract`
  - `ConditionalPneNpDepthBridgeFinalContract` (canonical lift contract)
  - `P_ne_NP_final_of_depth_contract`
  - `P_ne_NP_final_of_depth_bridge_contract`

## Legacy cleanup (2026-02-26)

- Removed legacy `allFunctions/default_multiSwitching` public entrypoints from
  `pnp3/Magnification/FinalResult.lean`.
- Active final API is now centered on semantic/syntactic-easy hypotheses and
  constructive provider wiring.
- Legacy all-functions witness layer remains only in lower-level compatibility
  modules (`AntiChecker_Partial` / `LB_Formulas_Core_Partial`) and is no longer
  the public final-route surface.

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

## Step-C semantic API (2026-02-26)

- Added a non-vacuous semantic API in parallel to legacy Step-C interfaces:
  - `solverFunctionFamily`, `SolverAC0WitnessPartial`,
    `SolverAC0MultiSwitchingWitnessPartial`
    in `pnp3/LowerBounds/AntiChecker_Partial.lean`.
  - `StepCCoreSemanticHypothesisPartial`,
    `LB_Formulas_core_partial_semantic`
    in `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean`.
  - `AC0StatementPartial_semantic`,
    `AC0BoundedStatementPartial_semantic`,
    `FormulaLowerBoundHypothesisPartial_semantic`
    in `pnp3/Magnification/PipelineStatements_Partial.lean`.
- Full `lake build` passes after the change.
- Active bridge entrypoints now require an explicit
  `FormulaLowerBoundHypothesisPartial p δ` argument instead of auto-deriving
  it from the legacy `allFunctionsFamily` route:
  - `NP_not_subset_PpolyFormula_from_partial_formulas`
  - `NP_not_subset_PpolyReal_from_partial_formulas`
- Legacy `allFunctions/default_multiSwitching` public final entrypoints were
  removed from `pnp3/Magnification/FinalResult.lean`.
- Lower-level compatibility definitions remain in `AntiChecker_Partial` /
  `LB_Formulas_Core_Partial` as a temporary safety layer.
- Added end-to-end semantic bridge/final route (no `allFunctionsFamily` in the
  new contracts):
  - `StructuredLocalityProviderPartial_semantic`
  - `OPS_trigger_formulas_partial_of_provider_formula_separation_semantic`
  - `NP_not_subset_PpolyFormula_from_partial_formulas_semantic`
  - `NP_not_subset_PpolyFormula_from_params_semantic`
  - `AsymptoticFormulaTrackHypothesis_semantic`
  - `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic`

## Step-C counting kernel hardening (2026-02-26)

- Added explicit family-level counting core in
  `pnp3/LowerBounds/AntiChecker_Partial.lean`:
  - `AC0EasyFamilyDataPartial`
  - `noSmallAC0Solver_partial_of_family_card`
  - `AC0EasyFamily`
  - `ac0EasyFamily_card_lower`
  - `noSmallAC0Solver_partial_of_easyFamilyData`
- Added corresponding core wrapper in
  `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean`:
  - `LB_Formulas_core_partial_of_easyFamilyData`
- Updated semantic Step-C interfaces to family-level easy-data form:
  - `StepCCoreSemanticHypothesisPartial`
  - `AC0StatementPartial_semantic`
  - `AC0BoundedStatementPartial_semantic`
- Interpretation:
  the contradiction is now expressed over an explicit family `F` with AC0
  witness and cardinal lower bound (`|F|`), i.e. in counting form; not only
  via solver-singleton witness interfaces.
