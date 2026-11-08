import Attempt.Surface
import Lean

/-! Complete exact-name audit of the imported addon declaration domain.
Generated entries are explicit and separately classified, never silently ignored.
-/
open Lean Elab Command in
run_cmd do
  let expected : List Name := [
    `Research.LengthwiseSearch.family_iff_all_lengths,
    `Research.LengthwiseSearch.lowerBoundAt_iff_no_solver,
    `Research.LengthwiseSearch.no_family_iff_exists_lowerBoundAt,
    `Research.LengthwiseSearch.lowerBoundAt_mono,
    `Research.LengthwiseSearch.lengthwiseAt_iff_no_family,
    `Research.LengthwiseSearch.R_iff_lengthwise,
    `Research.LengthwiseSearch.exact_R_of_lengthwise,
    `Research.LengthwiseSearch.bounded_output_tuple_exists,
    `Research.LengthwiseSearch.promised_input_of_lowerBoundAt,
    `Research.LengthwiseSearch.threshold_one_le,
    `Research.LengthwiseSearch.witness_width_four_le,
    `Research.LengthwiseSearch.constant_table_promised,
    `Research.LengthwiseSearch.Audit.check_R_full_contract,
    `Research.LengthwiseSearch.Examples.identity_constant_lower_bound,
    `Research.LengthwiseSearch.Examples.no_common_bad_input,
    `Research.LengthwiseSearch.Examples.identity_projection_no_lower_bound,
    `Research.LengthwiseSearch.Examples.zero_width_no_lower_bound,
    `Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction,
    `Research.LengthwiseSearch.Examples.empty_promise_no_lower_bound,
    `Research.LengthwiseSearch.SolverAt,
    `Research.LengthwiseSearch.SolverAt.mk,
    `Research.LengthwiseSearch.SolverAt.outputCircuit,
    `Research.LengthwiseSearch.SolverAt.size_le,
    `Research.LengthwiseSearch.SolverAt.solves,
    `Research.LengthwiseSearch.LowerBoundAt,
    `Research.LengthwiseSearch.BoundedSearchSolver.atLength,
    `Research.LengthwiseSearch.concreteProblem,
    `Research.LengthwiseSearch.polynomialBudget,
    `Research.LengthwiseSearch.LengthwiseAt,
    `Research.LengthwiseSearch.LengthwiseR,
    `Research.LengthwiseSearch.boundedProjection,
    `Research.LengthwiseSearch.Examples.identityProblem,
    `Research.LengthwiseSearch.Examples.constantClass,
    `Research.LengthwiseSearch.Examples.OneBitCircuit,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input,
    `Research.LengthwiseSearch.Examples.projectionClass,
    `Research.LengthwiseSearch.Examples.identity_solver,
    `Research.LengthwiseSearch.Examples.emptyCircuitClass,
    `Research.LengthwiseSearch.Examples.zeroWidthProblem,
    `Research.LengthwiseSearch.Examples.zero_width_solver,
    `Research.LengthwiseSearch.Examples.emptyPromiseProblem,
    `Research.LengthwiseSearch.Examples.empty_promise_solver,
    `Research.LengthwiseSearch.Surface.check_family_iff_all_lengths,
    `Research.LengthwiseSearch.Surface.check_lowerBoundAt_iff_no_solver,
    `Research.LengthwiseSearch.Surface.check_no_family_iff_exists_lowerBoundAt,
    `Research.LengthwiseSearch.Surface.check_lowerBoundAt_mono,
    `Research.LengthwiseSearch.Surface.check_lengthwiseAt_iff_no_family,
    `Research.LengthwiseSearch.Surface.check_R_iff_lengthwise,
    `Research.LengthwiseSearch.Surface.check_exact_R_of_lengthwise,
    `Research.LengthwiseSearch.Surface.check_bounded_output_tuple_exists,
    `Research.LengthwiseSearch.Surface.check_promised_input_of_lowerBoundAt,
    `Research.LengthwiseSearch.Surface.check_threshold_one_le,
    `Research.LengthwiseSearch.Surface.check_witness_width_four_le,
    `Research.LengthwiseSearch.Surface.check_constant_table_promised,
    `Research.LengthwiseSearch.Surface.check_R_full_contract,
    `Research.LengthwiseSearch.Surface.check_identity_constant_lower_bound,
    `Research.LengthwiseSearch.Surface.check_no_common_bad_input,
    `Research.LengthwiseSearch.Surface.check_identity_projection_no_lower_bound,
    `Research.LengthwiseSearch.Surface.check_zero_width_no_lower_bound,
    `Research.LengthwiseSearch.Surface.check_zero_budget_vacuous_obstruction,
    `Research.LengthwiseSearch.Surface.check_empty_promise_no_lower_bound,
    `Research.LengthwiseSearch.Surface.pin_SolverAt,
    `Research.LengthwiseSearch.Surface.pin_SolverAt_mk,
    `Research.LengthwiseSearch.Surface.pin_SolverAt_outputCircuit,
    `Research.LengthwiseSearch.Surface.pin_SolverAt_size_le,
    `Research.LengthwiseSearch.Surface.pin_SolverAt_solves,
    `Research.LengthwiseSearch.Surface.pin_LowerBoundAt,
    `Research.LengthwiseSearch.Surface.pin_atLength,
    `Research.LengthwiseSearch.Surface.pin_concreteProblem,
    `Research.LengthwiseSearch.Surface.pin_polynomialBudget,
    `Research.LengthwiseSearch.Surface.pin_LengthwiseAt,
    `Research.LengthwiseSearch.Surface.pin_LengthwiseR,
    `Research.LengthwiseSearch.Surface.pin_boundedProjection,
    `Research.LengthwiseSearch.Surface.pin_identityProblem,
    `Research.LengthwiseSearch.Surface.pin_constantClass,
    `Research.LengthwiseSearch.Surface.pin_OneBitCircuit,
    `Research.LengthwiseSearch.Surface.pin_OneBitCircuit_constant,
    `Research.LengthwiseSearch.Surface.pin_OneBitCircuit_input,
    `Research.LengthwiseSearch.Surface.pin_projectionClass,
    `Research.LengthwiseSearch.Surface.pin_identity_solver,
    `Research.LengthwiseSearch.Surface.pin_emptyCircuitClass,
    `Research.LengthwiseSearch.Surface.pin_zeroWidthProblem,
    `Research.LengthwiseSearch.Surface.pin_zero_width_solver,
    `Research.LengthwiseSearch.Surface.pin_emptyPromiseProblem,
    `Research.LengthwiseSearch.Surface.pin_empty_promise_solver,
    `Pnp4.Frontier.ContractExpansion.thresholdPoly.eq_1,
    `Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_1,
    `Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_inst,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.casesOn,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant.inj,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant.injEq,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant.sizeOf_spec,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input.inj,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input.injEq,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input.sizeOf_spec,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusion,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtor,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtorType,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.rec,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.recOn,
    `Research.LengthwiseSearch.Examples.emptyCircuitClass.match_1,
    `Research.LengthwiseSearch.Examples.emptyPromiseProblem._proof_1,
    `Research.LengthwiseSearch.Examples.empty_promise_solver._proof_1,
    `Research.LengthwiseSearch.Examples.empty_promise_solver._proof_2,
    `Research.LengthwiseSearch.Examples.identityProblem._proof_1,
    `Research.LengthwiseSearch.Examples.identityProblem._proof_2,
    `Research.LengthwiseSearch.Examples.identity_solver._proof_1,
    `Research.LengthwiseSearch.Examples.identity_solver._proof_2,
    `Research.LengthwiseSearch.Examples.projectionClass.match_1,
    `Research.LengthwiseSearch.Examples.zeroWidthProblem._proof_1,
    `Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction._proof_1_1,
    `Research.LengthwiseSearch.Examples.zero_width_solver._proof_1,
    `Research.LengthwiseSearch.SolverAt._sizeOf_1,
    `Research.LengthwiseSearch.SolverAt._sizeOf_inst,
    `Research.LengthwiseSearch.SolverAt.casesOn,
    `Research.LengthwiseSearch.SolverAt.mk._flat_ctor,
    `Research.LengthwiseSearch.SolverAt.mk.inj,
    `Research.LengthwiseSearch.SolverAt.mk.injEq,
    `Research.LengthwiseSearch.SolverAt.mk.sizeOf_spec,
    `Research.LengthwiseSearch.SolverAt.noConfusion,
    `Research.LengthwiseSearch.SolverAt.noConfusionType,
    `Research.LengthwiseSearch.SolverAt.noConfusionType.withCtor,
    `Research.LengthwiseSearch.SolverAt.noConfusionType.withCtorType,
    `Research.LengthwiseSearch.SolverAt.rec,
    `Research.LengthwiseSearch.SolverAt.recOn,
    `Research.LengthwiseSearch.boundedProjection._proof_1,
    `Research.LengthwiseSearch.lowerBoundAt_iff_no_solver.match_1_1,
    `Research.LengthwiseSearch.threshold_one_le._proof_1_2,
    `Research.LengthwiseSearch.witness_width_four_le._proof_1_1,
  ]
  let generated : List Name := [
    `Pnp4.Frontier.ContractExpansion.thresholdPoly.eq_1,
    `Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_1,
    `Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_inst,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.casesOn,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant.inj,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant.injEq,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.constant.sizeOf_spec,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input.inj,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input.injEq,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.input.sizeOf_spec,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusion,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtor,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtorType,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.rec,
    `Research.LengthwiseSearch.Examples.OneBitCircuit.recOn,
    `Research.LengthwiseSearch.Examples.emptyCircuitClass.match_1,
    `Research.LengthwiseSearch.Examples.emptyPromiseProblem._proof_1,
    `Research.LengthwiseSearch.Examples.empty_promise_solver._proof_1,
    `Research.LengthwiseSearch.Examples.empty_promise_solver._proof_2,
    `Research.LengthwiseSearch.Examples.identityProblem._proof_1,
    `Research.LengthwiseSearch.Examples.identityProblem._proof_2,
    `Research.LengthwiseSearch.Examples.identity_solver._proof_1,
    `Research.LengthwiseSearch.Examples.identity_solver._proof_2,
    `Research.LengthwiseSearch.Examples.projectionClass.match_1,
    `Research.LengthwiseSearch.Examples.zeroWidthProblem._proof_1,
    `Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction._proof_1_1,
    `Research.LengthwiseSearch.Examples.zero_width_solver._proof_1,
    `Research.LengthwiseSearch.SolverAt._sizeOf_1,
    `Research.LengthwiseSearch.SolverAt._sizeOf_inst,
    `Research.LengthwiseSearch.SolverAt.casesOn,
    `Research.LengthwiseSearch.SolverAt.mk._flat_ctor,
    `Research.LengthwiseSearch.SolverAt.mk.inj,
    `Research.LengthwiseSearch.SolverAt.mk.injEq,
    `Research.LengthwiseSearch.SolverAt.mk.sizeOf_spec,
    `Research.LengthwiseSearch.SolverAt.noConfusion,
    `Research.LengthwiseSearch.SolverAt.noConfusionType,
    `Research.LengthwiseSearch.SolverAt.noConfusionType.withCtor,
    `Research.LengthwiseSearch.SolverAt.noConfusionType.withCtorType,
    `Research.LengthwiseSearch.SolverAt.rec,
    `Research.LengthwiseSearch.SolverAt.recOn,
    `Research.LengthwiseSearch.boundedProjection._proof_1,
    `Research.LengthwiseSearch.lowerBoundAt_iff_no_solver.match_1_1,
    `Research.LengthwiseSearch.threshold_one_le._proof_1_2,
    `Research.LengthwiseSearch.witness_width_four_le._proof_1_1,
  ]
  -- Include every imported Attempt owner, even when its declarations use an
  -- unrelated namespace. A new module must not evade explicit classification.
  let ownModulePrefix : Name := `Attempt
  let env ← getEnv
  let actual := env.constants.toList.filterMap fun (n, _) => do
    let idx ← env.getModuleIdxFor? n
    let owner ← env.header.moduleNames[idx.toNat]?
    if ownModulePrefix.isPrefixOf owner then some n else none
  for n in actual do
    logInfo m!"[LENGTHWISE_DECL] {n}"
  for n in actual do
    unless expected.contains n do
      throwError "unexpected lengthwise declaration {n}; update explicit surface classification"
  for n in expected do
    unless actual.contains n do
      throwError "missing expected lengthwise declaration {n}"
  unless expected.length == expected.eraseDups.length do
    throwError "duplicate lengthwise audit name"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for root in expected do
    let axioms ← collectAxioms root
    for a in axioms do
      unless allowed.contains a do
        throwError "nonallowed transitive axiom {a} for {root}"
    logInfo m!"[LENGTHWISE_ROOT] {root}"
    if generated.contains root then logInfo m!"[LENGTHWISE_GENERATED] {root}"
    for a in axioms do
      logInfo m!"[LENGTHWISE_AXIOM] {root} {a}"

#print axioms Research.LengthwiseSearch.family_iff_all_lengths
#print axioms Research.LengthwiseSearch.lowerBoundAt_iff_no_solver
#print axioms Research.LengthwiseSearch.no_family_iff_exists_lowerBoundAt
#print axioms Research.LengthwiseSearch.lowerBoundAt_mono
#print axioms Research.LengthwiseSearch.lengthwiseAt_iff_no_family
#print axioms Research.LengthwiseSearch.R_iff_lengthwise
#print axioms Research.LengthwiseSearch.exact_R_of_lengthwise
#print axioms Research.LengthwiseSearch.bounded_output_tuple_exists
#print axioms Research.LengthwiseSearch.promised_input_of_lowerBoundAt
#print axioms Research.LengthwiseSearch.threshold_one_le
#print axioms Research.LengthwiseSearch.witness_width_four_le
#print axioms Research.LengthwiseSearch.constant_table_promised
#print axioms Research.LengthwiseSearch.Audit.check_R_full_contract
#print axioms Research.LengthwiseSearch.Examples.identity_constant_lower_bound
#print axioms Research.LengthwiseSearch.Examples.no_common_bad_input
#print axioms Research.LengthwiseSearch.Examples.identity_projection_no_lower_bound
#print axioms Research.LengthwiseSearch.Examples.zero_width_no_lower_bound
#print axioms Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction
#print axioms Research.LengthwiseSearch.Examples.empty_promise_no_lower_bound
#print axioms Research.LengthwiseSearch.SolverAt
#print axioms Research.LengthwiseSearch.SolverAt.mk
#print axioms Research.LengthwiseSearch.SolverAt.outputCircuit
#print axioms Research.LengthwiseSearch.SolverAt.size_le
#print axioms Research.LengthwiseSearch.SolverAt.solves
#print axioms Research.LengthwiseSearch.LowerBoundAt
#print axioms Research.LengthwiseSearch.BoundedSearchSolver.atLength
#print axioms Research.LengthwiseSearch.concreteProblem
#print axioms Research.LengthwiseSearch.polynomialBudget
#print axioms Research.LengthwiseSearch.LengthwiseAt
#print axioms Research.LengthwiseSearch.LengthwiseR
#print axioms Research.LengthwiseSearch.boundedProjection
#print axioms Research.LengthwiseSearch.Examples.identityProblem
#print axioms Research.LengthwiseSearch.Examples.constantClass
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.constant
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.input
#print axioms Research.LengthwiseSearch.Examples.projectionClass
#print axioms Research.LengthwiseSearch.Examples.identity_solver
#print axioms Research.LengthwiseSearch.Examples.emptyCircuitClass
#print axioms Research.LengthwiseSearch.Examples.zeroWidthProblem
#print axioms Research.LengthwiseSearch.Examples.zero_width_solver
#print axioms Research.LengthwiseSearch.Examples.emptyPromiseProblem
#print axioms Research.LengthwiseSearch.Examples.empty_promise_solver
#print axioms Research.LengthwiseSearch.Surface.check_family_iff_all_lengths
#print axioms Research.LengthwiseSearch.Surface.check_lowerBoundAt_iff_no_solver
#print axioms Research.LengthwiseSearch.Surface.check_no_family_iff_exists_lowerBoundAt
#print axioms Research.LengthwiseSearch.Surface.check_lowerBoundAt_mono
#print axioms Research.LengthwiseSearch.Surface.check_lengthwiseAt_iff_no_family
#print axioms Research.LengthwiseSearch.Surface.check_R_iff_lengthwise
#print axioms Research.LengthwiseSearch.Surface.check_exact_R_of_lengthwise
#print axioms Research.LengthwiseSearch.Surface.check_bounded_output_tuple_exists
#print axioms Research.LengthwiseSearch.Surface.check_promised_input_of_lowerBoundAt
#print axioms Research.LengthwiseSearch.Surface.check_threshold_one_le
#print axioms Research.LengthwiseSearch.Surface.check_witness_width_four_le
#print axioms Research.LengthwiseSearch.Surface.check_constant_table_promised
#print axioms Research.LengthwiseSearch.Surface.check_R_full_contract
#print axioms Research.LengthwiseSearch.Surface.check_identity_constant_lower_bound
#print axioms Research.LengthwiseSearch.Surface.check_no_common_bad_input
#print axioms Research.LengthwiseSearch.Surface.check_identity_projection_no_lower_bound
#print axioms Research.LengthwiseSearch.Surface.check_zero_width_no_lower_bound
#print axioms Research.LengthwiseSearch.Surface.check_zero_budget_vacuous_obstruction
#print axioms Research.LengthwiseSearch.Surface.check_empty_promise_no_lower_bound
#print axioms Research.LengthwiseSearch.Surface.pin_SolverAt
#print axioms Research.LengthwiseSearch.Surface.pin_SolverAt_mk
#print axioms Research.LengthwiseSearch.Surface.pin_SolverAt_outputCircuit
#print axioms Research.LengthwiseSearch.Surface.pin_SolverAt_size_le
#print axioms Research.LengthwiseSearch.Surface.pin_SolverAt_solves
#print axioms Research.LengthwiseSearch.Surface.pin_LowerBoundAt
#print axioms Research.LengthwiseSearch.Surface.pin_atLength
#print axioms Research.LengthwiseSearch.Surface.pin_concreteProblem
#print axioms Research.LengthwiseSearch.Surface.pin_polynomialBudget
#print axioms Research.LengthwiseSearch.Surface.pin_LengthwiseAt
#print axioms Research.LengthwiseSearch.Surface.pin_LengthwiseR
#print axioms Research.LengthwiseSearch.Surface.pin_boundedProjection
#print axioms Research.LengthwiseSearch.Surface.pin_identityProblem
#print axioms Research.LengthwiseSearch.Surface.pin_constantClass
#print axioms Research.LengthwiseSearch.Surface.pin_OneBitCircuit
#print axioms Research.LengthwiseSearch.Surface.pin_OneBitCircuit_constant
#print axioms Research.LengthwiseSearch.Surface.pin_OneBitCircuit_input
#print axioms Research.LengthwiseSearch.Surface.pin_projectionClass
#print axioms Research.LengthwiseSearch.Surface.pin_identity_solver
#print axioms Research.LengthwiseSearch.Surface.pin_emptyCircuitClass
#print axioms Research.LengthwiseSearch.Surface.pin_zeroWidthProblem
#print axioms Research.LengthwiseSearch.Surface.pin_zero_width_solver
#print axioms Research.LengthwiseSearch.Surface.pin_emptyPromiseProblem
#print axioms Research.LengthwiseSearch.Surface.pin_empty_promise_solver
#print axioms Pnp4.Frontier.ContractExpansion.thresholdPoly.eq_1
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_1
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_inst
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.casesOn
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.constant.inj
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.constant.injEq
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.constant.sizeOf_spec
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.input.inj
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.input.injEq
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.input.sizeOf_spec
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusion
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtor
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtorType
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.rec
#print axioms Research.LengthwiseSearch.Examples.OneBitCircuit.recOn
#print axioms Research.LengthwiseSearch.Examples.emptyCircuitClass.match_1
#print axioms Research.LengthwiseSearch.Examples.emptyPromiseProblem._proof_1
#print axioms Research.LengthwiseSearch.Examples.empty_promise_solver._proof_1
#print axioms Research.LengthwiseSearch.Examples.empty_promise_solver._proof_2
#print axioms Research.LengthwiseSearch.Examples.identityProblem._proof_1
#print axioms Research.LengthwiseSearch.Examples.identityProblem._proof_2
#print axioms Research.LengthwiseSearch.Examples.identity_solver._proof_1
#print axioms Research.LengthwiseSearch.Examples.identity_solver._proof_2
#print axioms Research.LengthwiseSearch.Examples.projectionClass.match_1
#print axioms Research.LengthwiseSearch.Examples.zeroWidthProblem._proof_1
#print axioms Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction._proof_1_1
#print axioms Research.LengthwiseSearch.Examples.zero_width_solver._proof_1
#print axioms Research.LengthwiseSearch.SolverAt._sizeOf_1
#print axioms Research.LengthwiseSearch.SolverAt._sizeOf_inst
#print axioms Research.LengthwiseSearch.SolverAt.casesOn
#print axioms Research.LengthwiseSearch.SolverAt.mk._flat_ctor
#print axioms Research.LengthwiseSearch.SolverAt.mk.inj
#print axioms Research.LengthwiseSearch.SolverAt.mk.injEq
#print axioms Research.LengthwiseSearch.SolverAt.mk.sizeOf_spec
#print axioms Research.LengthwiseSearch.SolverAt.noConfusion
#print axioms Research.LengthwiseSearch.SolverAt.noConfusionType
#print axioms Research.LengthwiseSearch.SolverAt.noConfusionType.withCtor
#print axioms Research.LengthwiseSearch.SolverAt.noConfusionType.withCtorType
#print axioms Research.LengthwiseSearch.SolverAt.rec
#print axioms Research.LengthwiseSearch.SolverAt.recOn
#print axioms Research.LengthwiseSearch.boundedProjection._proof_1
#print axioms Research.LengthwiseSearch.lowerBoundAt_iff_no_solver.match_1_1
#print axioms Research.LengthwiseSearch.threshold_one_le._proof_1_2
#print axioms Research.LengthwiseSearch.witness_width_four_le._proof_1_1
