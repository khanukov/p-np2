"""Freshly compile partial research and audit it, without claiming a proof of R.

Uses the pinned installed workbench's compilation primitives. This is a trusted
research-code workflow, not a sandbox or a new proof kernel.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

ROOTS = {
    'Research.LengthwiseSearch.family_iff_all_lengths',
    'Research.LengthwiseSearch.lowerBoundAt_iff_no_solver',
    'Research.LengthwiseSearch.no_family_iff_exists_lowerBoundAt',
    'Research.LengthwiseSearch.lowerBoundAt_mono',
    'Research.LengthwiseSearch.lengthwiseAt_iff_no_family',
    'Research.LengthwiseSearch.R_iff_lengthwise',
    'Research.LengthwiseSearch.exact_R_of_lengthwise',
    'Research.LengthwiseSearch.bounded_output_tuple_exists',
    'Research.LengthwiseSearch.promised_input_of_lowerBoundAt',
    'Research.LengthwiseSearch.threshold_one_le',
    'Research.LengthwiseSearch.witness_width_four_le',
    'Research.LengthwiseSearch.constant_table_promised',
    'Research.LengthwiseSearch.Audit.check_R_full_contract',
    'Research.LengthwiseSearch.Examples.identity_constant_lower_bound',
    'Research.LengthwiseSearch.Examples.no_common_bad_input',
    'Research.LengthwiseSearch.Examples.identity_projection_no_lower_bound',
    'Research.LengthwiseSearch.Examples.zero_width_no_lower_bound',
    'Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction',
    'Research.LengthwiseSearch.Examples.empty_promise_no_lower_bound',
    'Research.LengthwiseSearch.SolverAt',
    'Research.LengthwiseSearch.SolverAt.mk',
    'Research.LengthwiseSearch.SolverAt.outputCircuit',
    'Research.LengthwiseSearch.SolverAt.size_le',
    'Research.LengthwiseSearch.SolverAt.solves',
    'Research.LengthwiseSearch.LowerBoundAt',
    'Research.LengthwiseSearch.BoundedSearchSolver.atLength',
    'Research.LengthwiseSearch.concreteProblem',
    'Research.LengthwiseSearch.polynomialBudget',
    'Research.LengthwiseSearch.LengthwiseAt',
    'Research.LengthwiseSearch.LengthwiseR',
    'Research.LengthwiseSearch.boundedProjection',
    'Research.LengthwiseSearch.Examples.identityProblem',
    'Research.LengthwiseSearch.Examples.constantClass',
    'Research.LengthwiseSearch.Examples.OneBitCircuit',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.constant',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.input',
    'Research.LengthwiseSearch.Examples.projectionClass',
    'Research.LengthwiseSearch.Examples.identity_solver',
    'Research.LengthwiseSearch.Examples.emptyCircuitClass',
    'Research.LengthwiseSearch.Examples.zeroWidthProblem',
    'Research.LengthwiseSearch.Examples.zero_width_solver',
    'Research.LengthwiseSearch.Examples.emptyPromiseProblem',
    'Research.LengthwiseSearch.Examples.empty_promise_solver',
    'Research.LengthwiseSearch.Surface.check_family_iff_all_lengths',
    'Research.LengthwiseSearch.Surface.check_lowerBoundAt_iff_no_solver',
    'Research.LengthwiseSearch.Surface.check_no_family_iff_exists_lowerBoundAt',
    'Research.LengthwiseSearch.Surface.check_lowerBoundAt_mono',
    'Research.LengthwiseSearch.Surface.check_lengthwiseAt_iff_no_family',
    'Research.LengthwiseSearch.Surface.check_R_iff_lengthwise',
    'Research.LengthwiseSearch.Surface.check_exact_R_of_lengthwise',
    'Research.LengthwiseSearch.Surface.check_bounded_output_tuple_exists',
    'Research.LengthwiseSearch.Surface.check_promised_input_of_lowerBoundAt',
    'Research.LengthwiseSearch.Surface.check_threshold_one_le',
    'Research.LengthwiseSearch.Surface.check_witness_width_four_le',
    'Research.LengthwiseSearch.Surface.check_constant_table_promised',
    'Research.LengthwiseSearch.Surface.check_R_full_contract',
    'Research.LengthwiseSearch.Surface.check_identity_constant_lower_bound',
    'Research.LengthwiseSearch.Surface.check_no_common_bad_input',
    'Research.LengthwiseSearch.Surface.check_identity_projection_no_lower_bound',
    'Research.LengthwiseSearch.Surface.check_zero_width_no_lower_bound',
    'Research.LengthwiseSearch.Surface.check_zero_budget_vacuous_obstruction',
    'Research.LengthwiseSearch.Surface.check_empty_promise_no_lower_bound',
    'Research.LengthwiseSearch.Surface.pin_SolverAt',
    'Research.LengthwiseSearch.Surface.pin_SolverAt_mk',
    'Research.LengthwiseSearch.Surface.pin_SolverAt_outputCircuit',
    'Research.LengthwiseSearch.Surface.pin_SolverAt_size_le',
    'Research.LengthwiseSearch.Surface.pin_SolverAt_solves',
    'Research.LengthwiseSearch.Surface.pin_LowerBoundAt',
    'Research.LengthwiseSearch.Surface.pin_atLength',
    'Research.LengthwiseSearch.Surface.pin_concreteProblem',
    'Research.LengthwiseSearch.Surface.pin_polynomialBudget',
    'Research.LengthwiseSearch.Surface.pin_LengthwiseAt',
    'Research.LengthwiseSearch.Surface.pin_LengthwiseR',
    'Research.LengthwiseSearch.Surface.pin_boundedProjection',
    'Research.LengthwiseSearch.Surface.pin_identityProblem',
    'Research.LengthwiseSearch.Surface.pin_constantClass',
    'Research.LengthwiseSearch.Surface.pin_OneBitCircuit',
    'Research.LengthwiseSearch.Surface.pin_OneBitCircuit_constant',
    'Research.LengthwiseSearch.Surface.pin_OneBitCircuit_input',
    'Research.LengthwiseSearch.Surface.pin_projectionClass',
    'Research.LengthwiseSearch.Surface.pin_identity_solver',
    'Research.LengthwiseSearch.Surface.pin_emptyCircuitClass',
    'Research.LengthwiseSearch.Surface.pin_zeroWidthProblem',
    'Research.LengthwiseSearch.Surface.pin_zero_width_solver',
    'Research.LengthwiseSearch.Surface.pin_emptyPromiseProblem',
    'Research.LengthwiseSearch.Surface.pin_empty_promise_solver',
    'Pnp4.Frontier.ContractExpansion.thresholdPoly.eq_1',
    'Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_1',
    'Research.LengthwiseSearch.Examples.OneBitCircuit._sizeOf_inst',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.casesOn',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.constant.inj',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.constant.injEq',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.constant.sizeOf_spec',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.input.inj',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.input.injEq',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.input.sizeOf_spec',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusion',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtor',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.noConfusionType.withCtorType',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.rec',
    'Research.LengthwiseSearch.Examples.OneBitCircuit.recOn',
    'Research.LengthwiseSearch.Examples.emptyCircuitClass.match_1',
    'Research.LengthwiseSearch.Examples.emptyPromiseProblem._proof_1',
    'Research.LengthwiseSearch.Examples.empty_promise_solver._proof_1',
    'Research.LengthwiseSearch.Examples.empty_promise_solver._proof_2',
    'Research.LengthwiseSearch.Examples.identityProblem._proof_1',
    'Research.LengthwiseSearch.Examples.identityProblem._proof_2',
    'Research.LengthwiseSearch.Examples.identity_solver._proof_1',
    'Research.LengthwiseSearch.Examples.identity_solver._proof_2',
    'Research.LengthwiseSearch.Examples.projectionClass.match_1',
    'Research.LengthwiseSearch.Examples.zeroWidthProblem._proof_1',
    'Research.LengthwiseSearch.Examples.zero_budget_vacuous_obstruction._proof_1_1',
    'Research.LengthwiseSearch.Examples.zero_width_solver._proof_1',
    'Research.LengthwiseSearch.SolverAt._sizeOf_1',
    'Research.LengthwiseSearch.SolverAt._sizeOf_inst',
    'Research.LengthwiseSearch.SolverAt.casesOn',
    'Research.LengthwiseSearch.SolverAt.mk._flat_ctor',
    'Research.LengthwiseSearch.SolverAt.mk.inj',
    'Research.LengthwiseSearch.SolverAt.mk.injEq',
    'Research.LengthwiseSearch.SolverAt.mk.sizeOf_spec',
    'Research.LengthwiseSearch.SolverAt.noConfusion',
    'Research.LengthwiseSearch.SolverAt.noConfusionType',
    'Research.LengthwiseSearch.SolverAt.noConfusionType.withCtor',
    'Research.LengthwiseSearch.SolverAt.noConfusionType.withCtorType',
    'Research.LengthwiseSearch.SolverAt.rec',
    'Research.LengthwiseSearch.SolverAt.recOn',
    'Research.LengthwiseSearch.boundedProjection._proof_1',
    'Research.LengthwiseSearch.lowerBoundAt_iff_no_solver.match_1_1',
    'Research.LengthwiseSearch.threshold_one_le._proof_1_2',
    'Research.LengthwiseSearch.witness_width_four_le._proof_1_1',
}


def load_workbench(core):
    path = core / "tools/workbench.py"
    spec = importlib.util.spec_from_file_location("installed_workbench", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("attempt", type=Path)
    args = parser.parse_args()
    attempt = args.attempt.resolve()
    metadata = json.loads((attempt / "attempt.json").read_text(encoding="utf-8"))
    core = Path(metadata["core"]).resolve()
    wb = load_workbench(core)
    fingerprint = wb.verify_core(core)
    manifest = json.loads((attempt / "RESEARCH_SOURCE_MANIFEST.json").read_text(encoding="utf-8"))
    actual = {p.relative_to(attempt).as_posix() for p in attempt.rglob("*.lean")
              if ".lake" not in p.parts and p.name != "lakefile.lean"}
    expected = {row["path"] for row in manifest["files"]}
    if actual != expected:
        raise ValueError("research source name set changed; prepare a fresh attempt")
    for row in manifest["files"]:
        raw = (attempt / row["path"]).read_bytes()
        if len(raw) != row["bytes"] or hashlib.sha256(raw).hexdigest() != row["sha256"]:
            raise ValueError("research source identity changed; prepare a fresh attempt")
    root = wb.fresh_check_run(attempt)
    overrides = {}
    for i, (module, source) in enumerate(wb.module_sources(attempt, root)):
        overrides[module] = wb.compile_source(attempt, root, "own-" + str(i),
                                              source, module, overrides)
    printed = []
    for path in root.glob("own-*-compile/stdout.txt"):
        printed.extend(re.findall(r"\[LENGTHWISE_ROOT\] ([^\s]+)", path.read_text(encoding="utf-8")))
    wanted = ROOTS
    if set(printed) != wanted or len(printed) != len(wanted):
        raise RuntimeError("complete direct-root audit did not execute exactly once")

    # This valid theorem STILL HAS a LengthwiseR premise. The production exact-R
    # guard must reject it for that specific reason, after the positive build.
    source = root / "RejectedAsR.lean"
    source.write_text(wb.guard_source("Research.LengthwiseSearch.exact_R_of_lengthwise",
                                     "ConditionalSeparation.OpenProblem.R"), encoding="utf-8")
    rejected = False
    try:
        wb.compile_source(attempt, root, "reject-conditional-as-R", source,
                          "RejectedAsR", overrides)
    except RuntimeError:
        terminal = json.loads((root / "reject-conditional-as-R-compile/terminal.json").read_text())
        transcript = "\n".join((root / ("reject-conditional-as-R-compile/" + name)).read_text(
            encoding="utf-8") for name in ("stdout.txt", "stderr.txt"))
        rejected = terminal["OS_exit"] == 1 and "CLOSED exact expected type" in transcript
        if not rejected:
            raise
    if not rejected:
        raise RuntimeError("conditional interface was incorrectly accepted as closed R")
    for terminal_path in root.glob("*/terminal.json"):
        expected_exit = 1 if terminal_path.parent.name == "reject-conditional-as-R-compile" else 0
        if json.loads(terminal_path.read_text())["OS_exit"] != expected_exit:
            raise RuntimeError("unexpected earlier command failure")
    if (root/"RESULT.json").exists() or (root/"Assembly.lean").exists():
        raise RuntimeError("partial interface cannot produce final-R assembly/result")
    if wb.verify_core(core) != fingerprint:
        raise RuntimeError("installed core changed during partial check")
    result = {"status": "PARTIAL_RESEARCH_INTERFACE_CHECKED_NOT_R",
              "audited_roots": len(printed), "conditional_as_R": "REJECTED_EXPECTED_TYPE",
              "core_source_inventory_sha256": fingerprint, "receipts": str(root)}
    (root / "PARTIAL_RESULT.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
