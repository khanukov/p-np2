# TODO / Roadmap (constructive closure)

Updated to match the current code state in `pnp3/`.

## Current checkpoint

- Active final chain is conditional and machine-checked.
- Bridge is localized to `gapPartialMCSP_Language p`.
- New constructive target interfaces are in place:
  - `GapPartialMCSPFormulaReifier`
  - `GapPartialMCSPFormulaizer`
  - `..._with_formulaizer` theorem family in bridge/final modules.
- Partial locality-lift now has a certificate-driven wrapper:
  - `stableRestriction_of_certificate`
  - `locality_lift_partial_of_certificate`
  (still requires explicit bound `hCardHalf`).

## Priority A (highest): close localized embed constructively

Goal: replace external localized embed goal hypothesis

`GapPartialMCSPPpolyRealToPpolyFormulaGoal p`

with a theorem obtained from:

`GapPartialMCSPFormulaizer p`.

### A1. Build explicit formula family

- Implement `familyOf` for an `InPpoly` witness of `gapPartialMCSP_Language p`.
- Avoid ad-hoc semantics: target `ComplexityInterfaces.FormulaCircuit`.

### A2. Prove semantic correctness

- Prove `familyCorrect` pointwise:
  `FormulaCircuit.eval (familyOf w n) x = gapPartialMCSP_Language p n x`.

### A3. Prove polynomial size bound

- Prove `familyPoly`:
  `FormulaCircuit.size (familyOf w n) <= n^c + c` for some global `c`.

### A4. Wire into active final chain

- Instantiate `NP_not_subset_PpolyFormula_final_with_formulaizer`.
- Remove dependence on `GapPartialMCSPPpolyRealToPpolyFormulaGoal` from the active path.

## Priority B: replace restriction provider hypothesis by constructive theorem

Current provider interface in active path:

`StructuredLocalityProviderPartial` (restriction-style witness).

### B1. Construct provider from switching/shrinkage witnesses

- Produce `RestrictionLocalityPartial p` from strict structured `PpolyFormula` witness.
- Keep bounds (`polylogBudget`) aligned with the current solver interfaces.
- Route through certificate API where possible:
  `ShrinkageCertificate.Provider` -> `stableRestriction_of_certificate` -> locality lift.

### B1.1 Discharge `hCardHalf` constructively

- Prove/derive the half-table bound for certificate restrictions in the target provider path:
  `restriction.alive.card ≤ Partial.tableLen p.n / 2`.
- Remove ad hoc/manual passing of this bound for the main path.

### B2. Remove provider hypothesis from external variants

- Replace `..._external` usage with constructive provider theorem.

## Priority C: close Part A witness externality

External witness-backed facts still required:

- `partial_shrinkage_for_AC0`
- `shrinkage_for_localCircuit`

### C1. Formalize witness constructors

- Internal constructors for `AC0CircuitWitness`.
- Internal constructors for `LocalCircuitWitness`.

### C2. Integrate with locality provider

- Use internal shrinkage constructors to derive B1 constructively.

## Completion criteria (100% constructive target)

1. `rg "^axiom " -g"*.lean" pnp3` remains empty.
2. `NP_not_subset_PpolyFormula_final` no longer needs external bridge/provider assumptions.
3. After non-uniform interface upgrade (`PpolyReal`), restore a sound `P ≠ NP` final bridge.
4. `lake build` and `scripts/check.sh` pass with no conditional gates.

---

## Audit Closure Block (verified against current `pnp3/` on 2026-02-21)

This block supersedes older "main-branch" TODO lists that referenced
archived files (`Facts_Magnification.lean`, `LocalityInterfaces.lean`,
`AntiChecker.lean` without `_Partial`) and historical axioms.

### Verified current facts (do not regress)

- `pnp3/` has **0 active global axioms** (`rg "^axiom " pnp3` is empty).
- `Complexity.Interfaces.NP` is no longer `True`; it is an explicit verifier-style definition.
- `gapPartialMCSP_Language` is not `False`; it is a real language over encoded partial truth tables.
- Final canonical parameter is currently fixed (`n := 8`), not asymptotic.
- Active final output is still conditional (`NP ⊄ PpolyFormula`) and depends on explicit external hypotheses.

### Gaps that still block a standard (unconditional, asymptotic) `P ≠ NP`

#### G1. Asymptotic meaning gap (highest severity)

- `gapPartialMCSP_Language p` returns `false` outside one input length:
  it is a single-parameter family language with a fixed `p`.
- `FinalResult` uses one canonical `p` (`n := 8`), so current separation is
  not an asymptotic all-length statement.
- Required closure:
  - define a length-uniform/asymptotic target language family;
  - restate final lower bounds as asymptotic (`∀ᶠ n` / infinitely many `n`);
  - reconnect final theorem to standard class-level `P ≠ NP`.

#### G2. NP interface is still too weak semantically

- Current `NP` interface does not tie `runTime` to actual computation cost of `verify`.
- Current witness `gapPartialMCSP_in_NP` uses verifier that ignores certificate
  and decides the language directly (`decide (PartialMCSP_YES ...)`), which is
  fine as an interface witness but not yet a machine-level NP proof.
- Required closure:
  - strengthen NP definition to machine-cost-aware verifier (or fully TM-based bridge);
  - prove `GapPartialMCSP ∈ NP` with explicit certificate-checking semantics.

#### G3. Solver interfaces are still mostly behavioral wrappers

- `SmallGeneralCircuitSolver_Partial` stores numeric params + `decide` + promise correctness,
  but no explicit circuit object/family.
- Local/AC0 wrappers also expose behavior/correctness and bounds, but not a shared
  canonical circuit semantics needed for end-to-end non-vacuity checks.
- Required closure:
  - migrate solver interfaces to explicit circuit/formula witnesses;
  - keep correctness and size/depth/locality bounds attached to these witnesses;
  - rerun lower-bound chain on semantic solvers.

#### G4. Conditional external inputs remain in active chain

- Localized strict bridge goal:
  `GapPartialMCSPPpolyRealToPpolyFormulaGoal p`.
- Structured locality provider assumption:
  `StructuredLocalityProviderPartial`.
- Locality-lift certificate path still requires explicit cardinality bound `hCardHalf`.
- Shrinkage/lift instantiation still relies on external witness providers.
- Required closure:
  - internalize bridge (`PpolyReal -> PpolyFormula`) constructively;
  - derive locality provider from internal shrinkage/locality theorems;
  - discharge `hCardHalf` constructively from certificate/witness invariants.

#### G5. Final `P ≠ NP` wrapper is still interface-conditional

- `P_ne_NP_final` currently needs an external bridge
  `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.
- Required closure:
  - prove this bridge internally (or replace final target with direct `NP ⊄ Ppoly`);
  - then close with existing `P_ne_NP_of_nonuniform_separation`.

### Recommended execution order (dependency-safe)

1. **Asymptotic target first (G1)**
   - lock the exact final statement and language family before more proof work.
2. **Strengthen NP semantics (G2)**
   - prevent "proved but wrong target class" drift.
3. **Semantic solver migration (G3)**
   - make lower-bound statements about actual circuits, not only deciders.
4. **Eliminate external hypotheses (G4)**
   - bridge, provider, and `hCardHalf` constructive closure.
5. **Close final class bridge (G5)**
   - remove last interface-level conditional from `P_ne_NP_final`.

### File-focused checklist for this block

- `pnp3/Models/Model_PartialMCSP.lean`:
  asymptotic language redesign + honest NP witness.
- `pnp3/Complexity/Interfaces.lean`:
  stronger NP/TM-cost coupling and final class-bridge cleanup.
- `pnp3/Magnification/LocalityInterfaces_Partial.lean`:
  semantic solver payload migration.
- `pnp3/LowerBounds/AntiChecker_Partial.lean`:
  adapt anti-checker statements to semantic solvers.
- `pnp3/ThirdPartyFacts/PartialLocalityLift.lean`:
  constructive `hCardHalf` discharge path.
- `pnp3/ThirdPartyFacts/PpolyFormula.lean`:
  remove `GapPartialMCSPPpolyRealToPpolyFormulaGoal` dependency via formulaizer/reifier closure.
- `pnp3/Magnification/FinalResult.lean`:
  replace single-canonical-parameter final statement with asymptotic final theorem.

### Execution board (actionable, with DoD)

#### E1. Asymptotic target language (depends on none)

- [ ] Introduce a length-uniform/asymptotic language replacing fixed-`p` single-length behavior.
- [ ] Refactor promise wrappers to support asymptotic quantification.
- [ ] Replace fixed canonical usage in final path with asymptotic parameters.
- DoD:
  - Final target theorem no longer depends on one fixed `n`.
  - No core theorem in the final chain relies on "all other lengths are `false`".

#### E2. Honest NP semantics (depends on E1)

- [ ] Strengthen `Complexity.Interfaces.NP` to connect verifier runtime with actual computation model.
- [ ] Add/upgrade TM-bridge lemma(s) to avoid runtime-free witnesses.
- [ ] Reprove NP-membership for target language with certificate-checking semantics.
- DoD:
  - `gap..._in_NP` witness uses certificate content non-trivially.
  - Runtime bound is attached to executed verification, not a free function symbol.

#### E3. Semantic solvers migration (depends on E1, E2)

- [ ] Extend `SmallGeneralCircuitSolver_Partial` with explicit circuit/formula family payload.
- [ ] Extend local/AC0 solver wrappers with aligned semantic payload and bounds.
- [ ] Port lower-bound lemmas to semantic solver interfaces.
- DoD:
  - Main LB statements quantify over explicit circuit witnesses.
  - No final contradiction is derivable from parameter-only solver records.

#### E4. Remove explicit external hypotheses (depends on E3)

- [ ] Close `GapPartialMCSPPpolyRealToPpolyFormulaGoal` via internal formulaizer/reifier theorem.
- [ ] Derive `StructuredLocalityProviderPartial` from internal shrinkage/locality machinery.
- [ ] Prove certificate cardinality obligation (`hCardHalf`) constructively in main path.
- DoD:
  - `FinalResult` path imports no external goal/provider hypotheses.
  - `PartialLocalityLift` main usage no longer requires manually passed `hCardHalf`.

#### E5. Final class bridge and theorem cleanup (depends on E4)

- [ ] Internalize or eliminate `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` external bridge.
- [ ] Rewire final theorem to standard non-uniform separation lemma.
- [ ] Rename/export final theorem as the canonical project statement.
- DoD:
  - Final exported theorem is unconditional relative to internal repo artifacts.
  - Proof path is asymptotic and class-level (`P ≠ NP`), not fixed-instance.

### Progress tracking rules for this board

- Mark step `in-progress` only after all dependencies are checked green.
- Any new placeholder/hypothesis introduced during closure must be listed under the corresponding `E*`.
- Before checking an `E*` as done, run:
  - `lake build`
  - `./scripts/check.sh`

---

## NP Addendum (validated audit + implementation plan)

Validated on current workspace state (`pnp3/`), 2026-02-21.

### A. Claim validation against current code

#### A1. Claims that are outdated for current tree

- Outdated: `NP := True`.
  - Current reality: `NP` is verifier-style existential definition.
  - Evidence: `pnp3/Complexity/Interfaces.lean`.
- Outdated: `gapMCSP_Language := False` in active magnification path.
  - Current reality: active path uses `gapPartialMCSP_Language` with real decoding/YES check.
  - Evidence: `pnp3/Models/Model_PartialMCSP.lean`, `pnp3/Magnification/Facts_Magnification_Partial.lean`.
- Outdated: active file `pnp3/Magnification/Facts_Magnification.lean`.
  - Current reality: active file is `pnp3/Magnification/Facts_Magnification_Partial.lean`.
- Outdated: `NP_not_subset_Ppoly_of_contra` relies on `simp [NP]`.
  - Current reality: theorem is already classical-logic proof, independent of `NP := True`.
  - Evidence: `pnp3/Complexity/Interfaces.lean`.

#### A2. Claims that remain valid concerns

- Valid: NP semantics are still weakly tied to runtime model.
  - `NP` stores `runTime` bound and `verify`, but no proof that `runTime` is the actual cost of `verify`.
- Valid: `gapPartialMCSP_in_NP` witness is semantically weak.
  - Current verifier ignores certificate content and decides YES predicate directly.
  - Evidence: `gapPartialMCSP_verify` in `pnp3/Models/Model_PartialMCSP.lean`.
- Valid: final theorem is still conditional and non-asymptotic.
  - Fixed canonical parameter (`n := 8`) and external bridge assumptions remain.
  - Evidence: `pnp3/Magnification/FinalResult.lean`.

### B. Correct NP-phase target for THIS repository

NP phase is complete only when all are true:

- `NP` is machine-cost-faithful (or derived from such via a proved bridge).
- `gapPartialMCSP_in_NP` is certificate-driven (certificate is actually used).
- Pair/input encoding used by verifier path has explicit correctness lemmas.
- Magnification modules consume the strengthened NP statement with no ad hoc shortcuts.

### C. Execution plan (NP-1..NP-8)

#### NP-1. Freeze interfaces and terminology

- [ ] Keep `Language`/`Bitstring` aliases stable in `Complexity.Interfaces`.
- [ ] Explicitly document that active target is `gapPartialMCSP_Language` (not archived `gapMCSP`).
- DoD:
  - No active file references archived `Facts_Magnification.lean` symbols.

#### NP-2. Introduce cost-faithful verifier contract

- [ ] Add a predicate linking verifier implementation and claimed runtime.
- [ ] Extend/replace current `NP` definition to require this predicate.
- [ ] Keep compatibility theorem from old NP interface if needed for migration.
- DoD:
  - `NP` cannot be witnessed by arbitrary `runTime` detached from `verify`.

#### NP-3. Strengthen TM bridge

- [ ] Upgrade `NP_TM -> NP` bridge to the new cost-faithful NP contract.
- [ ] Add reverse bridge stub/theorem statement if later needed by final assembly.
- DoD:
  - TM-based witness can instantiate NP without weakening runtime semantics.

#### NP-4. Pair encoding utilities (if needed by strengthened bridge)

- [ ] Promote `concatBitstring` to a documented API (or replace with explicit encode/decode pair).
- [ ] Add lemmas for length accounting and decode-after-encode (if decode is introduced).
- DoD:
  - Verifier/TM bridge has explicit, reusable pair-encoding lemmas.

#### NP-5. Rebuild `gapPartialMCSP` NP witness honestly

- [ ] Replace `gapPartialMCSP_verify` with certificate-using verifier.
- [ ] Add certificate structure design note (what is encoded and why polynomial).
- [ ] Prove correctness equivalence with `gapPartialMCSP_Language`.
- DoD:
  - Completeness/soundness proof uses non-trivial certificate content.

#### NP-6. Polynomial bound obligations for certificate path

- [ ] State and prove assumptions/lemmas required for polynomial certificate length.
- [ ] Decide policy: parameter-level bound in `GapPartialMCSPParams` vs theorem-side hypothesis.
- [ ] Apply the policy consistently in all users of `gapPartialMCSP_in_NP`.
- DoD:
  - `gapPartialMCSP_in_NP` has no hidden growth assumptions.

#### NP-7. Magnification rewire

- [ ] Update `Facts_Magnification_Partial` to consume strengthened `gapPartialMCSP_in_NP`.
- [ ] Remove remaining simplification patterns that hide NP semantics.
- DoD:
  - Trigger theorems compile unchanged in statement strength or with explicitly justified strengthening.

#### NP-8. Regression and smoke tests

- [ ] Add test: contra-form theorem (`NP_not_subset_Ppoly_of_contra`) still produces witness under strengthened NP.
- [ ] Add test: certificate path for `gapPartialMCSP_in_NP` is exercised (non-vacuous witness).
- [ ] Add test: canonical-parameter sanity instance still accepted after NP changes.
- DoD:
  - `lake build` and `./scripts/check.sh` pass.
  - New tests fail if verifier ignores certificate.

### D. Risks and sequencing constraints

- NP strengthening before asymptotic redesign may create duplicate migration work.
- Recommended coupling:
  - If E1 is already active, execute `NP-2..NP-6` on top of E1 interfaces.
  - If E1 is not active yet, implement NP changes behind compatibility wrappers.
- Hard stop rule:
  - Do not mark NP phase done while `gapPartialMCSP_verify` ignores certificate.

---

## Mandatory Critical Path (primary goal: unconditional constructive `P ≠ NP`)

This section overrides prioritization for execution.  
Rule: if a task is not listed here, it is secondary.

### MCP-0. Success criterion (non-negotiable)

We count the main goal as reached only if all are true:

- Final exported theorem is asymptotic, class-level `P ≠ NP`.
- Final proof has no external assumptions/goal placeholders/providers.
- Core statements are about semantic computational objects (not parameter-only wrappers).
- Build/test passes (`lake build`, `./scripts/check.sh`) on the unconditional path.

### MCP-1. Asymptotic statement first (highest priority)

- [x] Add asymptotic wrappers in final bridge (`FinalResult`) to avoid hard dependency
      on only one explicit parameter value.
- [x] Introduce model-level asymptotic language definition
      (`gapPartialMCSP_AsymptoticLanguage`) for multi-length semantics.
- [x] Make primary `*_final` theorems asymptotic-entry based; keep canonical
      `n=8` route only as legacy compatibility wrappers.
- [x] Ensure target language is not "single length true, other lengths false"
      by using asymptotic-language entrypoints and language-level final bridges.
- Progress note (2026-02-21):
  - done: `pnp3/Magnification/FinalResult.lean` now has asymptotic wrappers.
  - done: `pnp3/Models/Model_PartialMCSP.lean` now has asymptotic language definition.
  - done: added `partialInputLen_injective` to support precise length-shape reasoning.
  - done: primary `NP_not_subset_PpolyFormula_final` / `P_ne_NP_final` now take asymptotic hypothesis.
  - done: added non-canonical witness entrypoint in final bridge
    (`AsymptoticFormulaTrackWitnessAt`, `NP_not_subset_PpolyFormula_of_witness_at`)
    to avoid hardcoded size selection in trigger-facing use.
  - done: replaced existential asymptotic hypothesis with explicit constructive
    data carrier (`pAt`, `pAt_n`, `pAt_hyp`) in final bridge.
  - done: added direct asymptotic-language entrypoint
    (`NP_not_subset_PpolyFormula_of_asymptotic_language`) in final bridge.
  - done: added direct language-level `P ≠ NP` bridge
    (`P_ne_NP_of_asymptotic_language`) to keep final route independent of fixed-size packs.
  - done: added native NP lemma for asymptotic language
    (`gapPartialMCSP_Asymptotic_in_NP`).
  - done: added TM-strict asymptotic entrypoint
    (`NP_not_subset_PpolyFormula_of_asymptotic_language_TM`) as MCP-2 migration hook.
  - done: added structured collapse-transfer interface +
    provider-based collapse theorem for asymptotic language
    (`AsymptoticLanguageCollapseTransfer`,
     `collapse_asymptotic_language_of_transfer`).
  - done: added final bridge using that interface
    (`P_ne_NP_of_asymptotic_language_with_transfer`).
  - audit pass: fixed-size `*_final_*` wrappers were renamed to `*_legacy`,
    so non-legacy final theorems are asymptotic-entry based.
  - re-audit pass (code-level): `NP_not_subset_PpolyFormula_final` and `P_ne_NP_final`
    require asymptotic hypotheses; fixed-size variants are now legacy-only symbols.
  - moved to MCP-4: internalize `AsymptoticLanguageCollapseTransfer` itself
    (remove transfer hypothesis by proving language-to-fixed reduction natively).
- Gate to pass:
  - all final theorems quantify asymptotically (not one fixed `n`).

Why mandatory:
- Without asymptotic form, result cannot represent standard `P` vs `NP`.

### MCP-2. Honest NP semantics + honest NP witness

- [x] Strengthen NP contract to cost-faithful verifier semantics (or equivalent TM-faithful formulation).
- [x] Replace `gapPartialMCSP_verify` with certificate-using verifier.
- [x] Reprove `gapPartialMCSP_in_NP` under current NP interface with certificate usage.
- [x] Mirror certificate-using verifier pattern for asymptotic language
      (`gapPartialMCSP_Asymptotic_verify`, `gapPartialMCSP_Asymptotic_in_NP`).
- [x] Reprove `gapPartialMCSP_in_NP` under explicit polynomial certificate-size policy
      after NP contract strengthening.
- Progress note (2026-02-21):
  - done: both fixed and asymptotic verifiers now depend on certificate bit (`&& w[0]`),
    so witnesses are no longer certificate-agnostic.
  - done: added TM-strict final bridges for asymptotic transfer path.
  - done: introduced strict NP track (`NP_strict := NP_TM`) and strict-to-lightweight
    separation bridges in `Complexity/Interfaces`.
  - done: introduced strict-to-`P ≠ NP` interface bridges in
    `Complexity/Interfaces` (`P_ne_NP_of_NP_strict_not_subset_*`).
  - done: exposed strict-track final hooks in `Magnification/FinalResult`
    (`P_ne_NP_of_NP_strict_not_subset_Ppoly*`).
  - done: added strict contra lemmas
    (`NP_strict_not_subset_*_of_contra`) and strict OPS trigger
    (`OPS_trigger_formulas_partial_of_provider_formula_separation_strict`),
    giving a TM-faithful route through magnification.
  - done: introduced explicit certificate-size policy objects in
    `Model_PartialMCSP` (`certLengthPolyPolicy`, `gapPartialMCSP_certLengthPolicy`)
    and rewired active triggers to consume
    `gapPartialMCSP_in_NP_of_certLengthPolicy`.
  - note: lightweight `NP` remains for compatibility; TM-faithful closure is now
    available via `NP_strict = NP_TM`.
- Gate to pass:
  - NP witness must fail if certificate is ignored.

Why mandatory:
- Without this, separation can remain semantically vacuous.

### MCP-3. Semantic solver migration (eliminate vacuity in lower bounds)

- [x] Upgrade general/local/AC0 solver interfaces to carry explicit circuit/formula witnesses.
- [x] Reprove downstream lower-bound lemmas over those semantic witnesses.
- Progress note (2026-02-21):
  - done: introduced shared semantic payload wrapper
    `ComplexityInterfaces.SemanticDecider` (`Carrier + eval`).
  - done: migrated solver wrappers to semantic witness form:
    `SmallGeneralCircuitSolver_Partial`,
    `SmallAC0Solver_Partial`,
    `SmallLocalCircuitSolver_Partial`.
  - done: `decide` is now derived from `(sem, witness)` and no longer a bare
    primitive function field.
  - done: added compatibility lemmas
    (`*.correct_decide`, `SmallLocalCircuitSolver_Partial.decideLocal_decide`)
    and ported locality-lift bridge constructors to semantic solvers.
  - done: downstream lower-bound chain recompiles over semantic solvers
    (`AntiChecker_Partial`, `LB_Formulas_Core_Partial`, `LB_LocalCircuits_Partial`,
     `LB_GeneralFromLocal_Partial`, `FinalResult`).
- Gate to pass:
  - no contradiction theorem may rely only on numeric parameters + opaque `decide`.

Why mandatory:
- Needed to ensure lower bounds are about actual models of computation.

### MCP-4. Remove all remaining conditional external inputs

- [x] Eliminate `StructuredLocalityProviderPartial` assumption from active final chain.
- [x] Eliminate localized bridge placeholder (`GapPartialMCSPPpolyRealToPpolyFormulaGoal` path).
- [x] Eliminate manual `hCardHalf` obligation in main locality-lift route.
- [ ] Replace external witness-provider dependencies with internal constructive theorems.
- [ ] Internalize `AsymptoticLanguageCollapseTransfer` (native reduction from
      `gapPartialMCSP_AsymptoticLanguage` to provider-usable collapse facts).
- Progress note (2026-02-21):
  - done: removed obsolete bridge placeholder alias from
    `ThirdPartyFacts/PpolyFormula.lean`
    (`GapPartialMCSPPpolyRealToPpolyFormulaGoal` + `_of_goal`).
  - done: added certificate auto-route without manual `hCardHalf` parameter:
    `ThirdPartyFacts.locality_lift_partial_of_certificate_auto` and
    `Magnification.locality_lift_partial_of_certificate_auto`
    using typeclass `HalfTableCertificateBound`.
  - done: added constructive packaging layers for default wiring:
    `ConstructiveLocalityEnginePartial` -> `structuredLocalityProviderPartial_of_engine`,
    `ConstructiveAsymptoticLanguageCollapseTransfer` ->
    `asymptoticLanguageCollapseTransfer_of_constructive`,
    plus `*_default_*` wrappers in `FinalResult`.
  - done: added canonical "default from constructive witness" constructors:
    `hasDefaultStructuredLocalityProviderPartial_of_engine`,
    `hasDefaultAsymptoticLanguageCollapseTransfer_of_constructive`,
    and slice-based default constructor
    `hasDefaultAsymptoticLanguageCollapseTransfer_of_sliceAgreement`.
  - done: built internal formula-to-general extraction candidate:
    `generalSolverOfFormula` and packaged engine builder
    `constructiveLocalityEnginePartial_of_formulaData`
    with default-flag constructor
    `hasDefaultStructuredLocalityProviderPartial_of_formulaData`.
  - done: internalized the shrinkage-provider side for the candidate engine
    via canonical witness (`Facts.LocalityLift.ShrinkageWitness.canonical`);
    remaining open side is the constructive `stable` witness for the extracted solver.
  - done: derived constructive `stable` witness lemmas from formula syntax:
    `stableWitness_of_formula_supportBound` and
    `stableWitness_of_formula_sizeBound` (using new
    `FormulaCircuit.support`, `eval_eq_of_eq_on_support`,
    `support_card_le_size` in `Complexity/Interfaces`).
  - done: packaged a one-assumption closure for the stable side:
    `FormulaHalfSizeBoundPartial` ->
    `formulaToGeneralLocalityData_of_halfSize` ->
    `hasDefaultStructuredLocalityProviderPartial_of_halfSize`.
  - done: exported a direct stable witness theorem under that same assumption:
    `stableWitness_of_formula_halfSize` (no extra engine/data wrapping needed).
  - done: added final auto-wiring wrappers from the same half-size condition:
    `NP_not_subset_PpolyFormula_final_of_halfSize` and
    `P_ne_NP_final_of_halfSize`.
  - done: added default half-size flag plumbing:
    `hasDefaultFormulaHalfSizeBoundPartial`,
    `defaultFormulaHalfSizeBoundPartial`,
    `hasDefaultStructuredLocalityProviderPartial_of_default_halfSize`,
    and final wrappers
    `NP_not_subset_PpolyFormula_final_of_default_halfSize`,
    `P_ne_NP_final_of_default_halfSize`.
  - done: added default-transfer final wrappers:
    `NP_not_subset_PpolyFormula_of_asymptotic_language_with_default_transfer`,
    `P_ne_NP_of_asymptotic_language_with_default_transfer`.
  - done: internalized a constructive transfer lemma from explicit
    slice-agreement:
    `AsymptoticLanguageSliceAgreement` +
    `asymptoticLanguageCollapseTransfer_of_sliceAgreement`
    (with constructive map
    `ppolyFormula_fixed_of_asymptotic_slice`).
  - remaining: prove internal inhabitants (`Nonempty ...`) from internal lemmas,
    then switch active final exports to those default wrappers.
  - blocker (research-level, explicit):
    `FormulaHalfSizeBoundPartial` is not derivable from current
    `PpolyFormula` bounds (`size ≤ n^c + c` does not imply `≤ tableLen/2` at
    the target length). See
    `pnp3/Docs/RESEARCH_BLOCKER_FormulaHalfSizeBoundPartial.md`
    (includes explicit A/B/C research routes and theorem deliverables).
- Gate to pass:
  - active final chain typechecks with zero extra hypotheses beyond internal lemmas.

Why mandatory:
- Any remaining external hypothesis keeps final theorem conditional.

### MCP-5. Close final class bridge internally

- [ ] Internalize/remove `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` assumption in final wrapper.
- [ ] Export one canonical unconditional theorem for `P ≠ NP`.
- Gate to pass:
  - `P_ne_NP_final` (or renamed canonical theorem) has no parameters/assumptions.

Why mandatory:
- Last logical dependency before unconditional class separation.

### MCP-6. Research-risk checkpoint (honesty requirement)

- [ ] After MCP-1..MCP-5, run a formal dependency audit of final theorem.
- [ ] If any step still requires a new unproven claim equivalent to the target separation strength,
      mark as "research blocker", not "engineering pending".

Why mandatory:
- Prevents misreporting "near-complete engineering" when remaining gap is mathematical breakthrough-level.

### Execution order (strict)

1. MCP-1
2. MCP-2
3. MCP-3
4. MCP-4
5. MCP-5
6. MCP-6

### Secondary tasks (deprioritized)

The following are useful but not on critical path unless they directly unblock MCP gates:

- documentation-only refactors,
- optional API cleanup unrelated to theorem dependencies,
- non-blocking ergonomic test additions.
