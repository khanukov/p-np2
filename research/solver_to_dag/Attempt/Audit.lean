import Attempt
import Lean

/- Complete imported Attempt-owner kernel roster. Includes generated entries even
when their names lie outside Research.SolverToDag. No count-only acceptance. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let requested : List Name := [
    ``Pnp3.ComplexityInterfaces.DagCircuit.constCircuit.eq_1,
    ``Pnp3.ComplexityInterfaces.DagCircuit.inputProj.eq_1,
    ``Pnp4.Frontier.ContractExpansion.thresholdPoly.eq_1,
    ``Research.SolverToDag.ConcreteSolver,
    ``Research.SolverToDag.bitMismatch,
    ``Research.SolverToDag.bitMismatch._proof_1,
    ``Research.SolverToDag.bitMismatch.eq_1,
    ``Research.SolverToDag.bitMismatch_size,
    ``Research.SolverToDag.check_bitMismatch_size,
    ``Research.SolverToDag.check_computes_iff_table,
    ``Research.SolverToDag.check_eval_bitMismatch,
    ``Research.SolverToDag.check_eval_pairMismatch,
    ``Research.SolverToDag.check_leafRecognizer_capstone,
    ``Research.SolverToDag.check_leafRecognizer_iff,
    ``Research.SolverToDag.check_leafRecognizer_polynomial,
    ``Research.SolverToDag.check_leafRecognizer_size,
    ``Research.SolverToDag.check_leaves_characterize,
    ``Research.SolverToDag.check_malformed_decode,
    ``Research.SolverToDag.check_malformed_not_verifies,
    ``Research.SolverToDag.check_matchesTable_iff,
    ``Research.SolverToDag.check_matchesTable_size,
    ``Research.SolverToDag.check_negation_no,
    ``Research.SolverToDag.check_negation_not_size_one,
    ``Research.SolverToDag.check_pairMismatch_gates,
    ``Research.SolverToDag.check_pairMismatch_size,
    ``Research.SolverToDag.check_plugSolver_capstone,
    ``Research.SolverToDag.check_plugSolver_eval,
    ``Research.SolverToDag.check_plugSolver_size_le,
    ``Research.SolverToDag.check_projection_yes,
    ``Research.SolverToDag.check_solverWiring_polynomial,
    ``Research.SolverToDag.check_tableEquality_capstone,
    ``Research.SolverToDag.check_tree_size_pos,
    ``Research.SolverToDag.check_vectorEquality_iff,
    ``Research.SolverToDag.check_vectorEquality_size,
    ``Research.SolverToDag.check_witnessBundle_eval,
    ``Research.SolverToDag.check_witnessBundle_gates_le,
    ``Research.SolverToDag.check_witnessWidth_exact,
    ``Research.SolverToDag.check_zero_variable_false,
    ``Research.SolverToDag.check_zero_variable_true,
    ``Research.SolverToDag.check_zero_width_equality,
    ``Research.SolverToDag.check_zero_width_size,
    ``Research.SolverToDag.computes_iff_table,
    ``Research.SolverToDag.concreteProblem,
    ``Research.SolverToDag.eval_bitMismatch,
    ``Research.SolverToDag.eval_pairMismatch,
    ``Research.SolverToDag.leafRecognizer,
    ``Research.SolverToDag.leafRecognizer.eq_1,
    ``Research.SolverToDag.leafRecognizer_capstone,
    ``Research.SolverToDag.leafRecognizer_iff,
    ``Research.SolverToDag.leafRecognizer_iff._simp_1_2,
    ``Research.SolverToDag.leafRecognizer_polynomial,
    ``Research.SolverToDag.leafRecognizer_size,
    ``Research.SolverToDag.leaves,
    ``Research.SolverToDag.leaves.eq_1,
    ``Research.SolverToDag.leaves_characterize,
    ``Research.SolverToDag.leaves_characterize._proof_1_2,
    ``Research.SolverToDag.leaves_characterize._proof_1_3,
    ``Research.SolverToDag.malformedBits,
    ``Research.SolverToDag.malformed_decode,
    ``Research.SolverToDag.malformed_not_verifies,
    ``Research.SolverToDag.matchesTable,
    ``Research.SolverToDag.matchesTable.eq_1,
    ``Research.SolverToDag.matchesTable_iff,
    ``Research.SolverToDag.matchesTable_size,
    ``Research.SolverToDag.matchesTable_size._proof_1_4,
    ``Research.SolverToDag.negationTable,
    ``Research.SolverToDag.negation_no,
    ``Research.SolverToDag.negation_not_size_one,
    ``Research.SolverToDag.pairMismatch,
    ``Research.SolverToDag.pairMismatch.eq_1,
    ``Research.SolverToDag.pairMismatch_gates,
    ``Research.SolverToDag.pairMismatch_size,
    ``Research.SolverToDag.plugSolver,
    ``Research.SolverToDag.plugSolver.eq_1,
    ``Research.SolverToDag.plugSolver_capstone,
    ``Research.SolverToDag.plugSolver_eval,
    ``Research.SolverToDag.plugSolver_size_le,
    ``Research.SolverToDag.plugSolver_size_le._proof_1_1,
    ``Research.SolverToDag.projectionTable,
    ``Research.SolverToDag.projection_yes,
    ``Research.SolverToDag.solverBudget,
    ``Research.SolverToDag.solverBudget.eq_1,
    ``Research.SolverToDag.solverWiring_polynomial,
    ``Research.SolverToDag.tableEquality,
    ``Research.SolverToDag.tableEquality.eq_1,
    ``Research.SolverToDag.tableEquality_capstone,
    ``Research.SolverToDag.treeTable,
    ``Research.SolverToDag.tree_size_pos,
    ``Research.SolverToDag.tree_size_pos._proof_1_1,
    ``Research.SolverToDag.tree_size_pos._proof_1_2,
    ``Research.SolverToDag.tree_size_pos._proof_1_3,
    ``Research.SolverToDag.type_ConcreteSolver,
    ``Research.SolverToDag.type_bitMismatch,
    ``Research.SolverToDag.type_concreteProblem,
    ``Research.SolverToDag.type_leafRecognizer,
    ``Research.SolverToDag.type_leaves,
    ``Research.SolverToDag.type_malformedBits,
    ``Research.SolverToDag.type_matchesTable,
    ``Research.SolverToDag.type_negationTable,
    ``Research.SolverToDag.type_pairMismatch,
    ``Research.SolverToDag.type_plugSolver,
    ``Research.SolverToDag.type_projectionTable,
    ``Research.SolverToDag.type_solverBudget,
    ``Research.SolverToDag.type_tableEquality,
    ``Research.SolverToDag.type_treeTable,
    ``Research.SolverToDag.type_vectorEquality,
    ``Research.SolverToDag.type_witnessBundle,
    ``Research.SolverToDag.type_witnessWidth,
    ``Research.SolverToDag.vectorEquality,
    ``Research.SolverToDag.vectorEquality.eq_1,
    ``Research.SolverToDag.vectorEquality_iff,
    ``Research.SolverToDag.vectorEquality_iff._simp_1_2,
    ``Research.SolverToDag.vectorEquality_size,
    ``Research.SolverToDag.vectorEquality_size._proof_1_2,
    ``Research.SolverToDag.witnessBundle,
    ``Research.SolverToDag.witnessBundle.eq_1,
    ``Research.SolverToDag.witnessBundle_eval,
    ``Research.SolverToDag.witnessBundle_gates_le,
    ``Research.SolverToDag.witnessBundle_gates_le._proof_1_2,
    ``Research.SolverToDag.witnessWidth,
    ``Research.SolverToDag.witnessWidth_exact,
    ``Research.SolverToDag.zero_variable_false,
    ``Research.SolverToDag.zero_variable_true,
    ``Research.SolverToDag.zero_width_equality,
    ``Research.SolverToDag.zero_width_size]
  let mut observed : List Name := []
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let some owner := modules[idx.toNat]? | throwError "module index out of bounds"
      if (`Attempt).isPrefixOf owner then
        unless requested.contains n do throwError "unexpected imported owned declaration {n}"
        observed := n :: observed
  for n in requested do
    unless observed.contains n do throwError "missing imported owned declaration {n}"
    let axs ← collectAxioms n
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "nonallowed transitive axiom {a} for {n}"
      logInfo m!"[SOLVER_DAG_AXIOM] {n} {a}"
    logInfo m!"[SOLVER_DAG_ROOT] {n}"
    elabCommand (← `(#print axioms $(mkIdent n)))
  for path in (← searchPathRef.get) do
    logInfo m!"[SOLVER_DAG_SEARCH_PATH] {path}"
  for n in modules do
    logInfo m!"[SOLVER_DAG_IMPORT] {n}"
  -- Compiler-only codegen names are reported separately from kernel declarations.
  for idx in [:modules.size] do
    let some owner := modules[idx]? | throwError "module name index"
    if (`Attempt).isPrefixOf owner then
      let some data := env.header.moduleData[idx]? | throwError "module data index"
      for n in data.extraConstNames do logInfo m!"[SOLVER_DAG_CODEGEN] {n}"
