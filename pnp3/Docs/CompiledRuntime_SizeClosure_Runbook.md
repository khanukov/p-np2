# Compiled runtime size-closure runbook (`P ⊆ PpolyDAG`)

> **STALE NAMES (2026-05-29).** This runbook describes a superseded
> construction.  The compiled-tree / blueprint declarations it names
> (`stepCompiled`, `stepCompiledTruthTable`, `runtimeConfigCompiled`,
> `buildWriteTerm`, `buildNextState`/`Head`/`Tape`, `linearNext*Wire`,
> `LinearStepBlueprint`, …) have been **removed as dead code**: they were
> never wired into the active route and were unused.  The live inclusion
> route is the linear *candidate* route
> (`runtimeConfigCompiledLinear` / `stepCompiledLinearCandidateStepSpecProvider_internal`),
> and the no-arg endpoint is `proved_P_subset_PpolyDAG_internal`.  For the
> current, accurate inclusion-side status use
> `PsubsetPpoly_Internal_TODO.md`, `PsubsetPpoly_AUDITOR_CHECKLIST.md`, and
> `Simulation_FineGrained_Status.md`.  The text below is kept only as
> historical architectural tracing.

Date: 2026-03-02
Status: active

> Current-scope note (2026-04-03):
> this is an inclusion-side architectural runbook, not the global
> project status.

> Release note (2026-03-14):
> this runbook is kept as architectural tracing.
> For the current release status and active route, use:
> `pnp3/Docs/PsubsetPpoly_Internal_TODO.md` and
> `pnp3/Docs/PsubsetPpoly_AUDITOR_CHECKLIST.md`.

## Update (2026-03-13): post-recheck note

Checks on the current tree:

- `./scripts/check.sh` passes;
- the current audit / regression tests pass
  (`AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`).

What changed since this runbook was pinned:

1. The linear size route is closed by the internal witness
   `CompiledRuntimeCircuitSizeBoundLinear_internal`.
2. For the linear route, correctness is closed via
   `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider`
   with an internal step-spec provider.
3. The residual inclusion blocker is no longer the size part, but a
   no-arg evaluator / output-wire agreement witness used to assemble
   `proved_P_subset_PpolyDAG_internal`.

The sections below are kept as an architectural decision trace.

## 1. Executive decision

The current route to closing `CompiledRuntimeCircuitSizeBound` via the
existing `stepCompiled` **cannot be closed** in its present form.

The reason is not a single missing lemma but the architecture of the
step:

1. `ConfigCircuits.stepCircuits` currently uses `truthTableCircuit`
   for `nextTapeCircuit / nextHeadCircuit / nextStateCircuit`.
2. `stepCompiled` is built via
   `toConfigCircuits` → `toTreeWire` → `packFin (compileTree ...)`.
3. This regularly unfolds the DAG representation into trees and
   recompiles.

Bottom line: there is no realistic way to obtain an internal
polynomial bound of the form `n^(c+5) + (c+5)` for
`runtimeConfigCompiled` without refactoring the step.

## 2. What that means for the strategy

The best path to the final goal (`P ⊆ PpolyDAG` without external
contracts):

1. Remove the truth-table step as the basis of the simulation.
2. Make a DAG-preserving step at the `StraightConfig` level
   (append-only builder).
3. Prove the size bound through a one-step gate increment and
   iteration over `runTime`.

This is simultaneously:

- constructive;
- compatible with the already-closed semantic part
  (the `stepCompiled` branch);
- a direct trajectory to closing
  `CompiledRuntimeCircuitSizeBound`.

## 3. Priority plan (actually executable)

### P0 (critical, high complexity)
Introduce a new step `stepCompiledLinear` (working name) that:

1. starts from `sc.circuit` (`EvalBuildCtx` / builder primitives);
2. only appends new gates (no `toTreeWire` / `compileTree` on the
   whole formula);
3. returns new wire selectors for `tape / head / state`.

Expected outcome:

- a one-step lemma of the form
  `gates(stepCompiledLinear sc) ≤ gates(sc) + K(M,n)`.

### P1 (high)
Semantics of the new step:

1. one-step spec:
   `Spec sc f -> Spec (stepCompiledLinear sc) (TM.stepConfig ∘ f)`;
2. iteration: a runtime spec for `Nat.iterate stepCompiledLinear`.

### P2 (medium-high)
Size chain:

1. from P0, derive the bound on `Nat.iterate`;
2. plug in `hRun : runTime ≤ n^c + c`;
3. obtain `CompiledRuntimeCircuitGateBound`;
4. close `CompiledRuntimeCircuitSizeBound` via the existing bridge
   `compiledRuntimeCircuitSizeBound_of_gateBound`.

### P3 (medium)
Route closure:

1. close the runtime-only bundle fully (without input contracts);
2. bring the internal-source endpoint to a no-arg theorem;
3. synchronise `FinalResult` / `Barrier.Bypass`.

## 4. Non-goals (so we don't waste time)

1. Do not try to "push through" the current
   `CompiledRuntimeCircuitSizeBound` using only arithmetic lemmas on
   top of the old `stepCompiled`.
2. Do not add further slack versions of the bound
   (`+6`, `+7`, ...) while the step is still a truth-table /
   tree-recompile.

## 5. Immediate next coding steps

1. Carve out, in `Simulation.lean`, a new namespace / block for the
   linear-step assembly.
2. First close only the gate-growth skeleton:
   - size after append;
   - cumulative per-step increase.
3. Then attach the semantic obligations (using the existing
   templates `Spec` and `runtime_spec_of_next`).

## 6. Definition of Done for this runbook

Block considered closed when all of the following hold at once:

1. there is an internal witness `CompiledRuntimeCircuitSizeBound`;
2. it does not depend on external contract inputs;
3. the route
   `proved_P_subset_PpolyDAG_of_iteratedRuntimeOnlyContracts` can be
   folded down to a no-arg internal theorem;
4. `lake build` passes on the key modules and on the full target.

## 7. Execution status (2026-03-02, current pass)

Done:

1. In `Simulation.lean`, switch points have been carved out:
   - `stepCircuitsTruthTable` + alias `stepCircuits`,
   - `stepCompiledTruthTable` + alias `stepCompiled`.
   - Explicit linear switch points were added:
     `stepCircuitsLinear`, `stepCompiledLinear`.
2. In `StraightLineBuilder.lean`, append-only helpers for
   `EvalBuildCtx` have been added:
   - `appendOp`, `appendConst`, `appendNot`, `appendAnd`,
     `appendOr`.
3. In `Simulation.lean`, append-only scaffolding has been added:
   - `StraightConfig.BuiltWire` + base operations over the
     current / base wire;
   - `BuiltWire.buildSymbolAux / buildSymbol` for
     `OR_i (head_i ∧ tape_i)` without a tree recompile;
   - `BuiltWire.buildGuardSymbol`, `BuiltWire.buildBranchIndicator`,
     `BuiltWire.buildWriteTerm`;
   - `BuiltWire.BuiltCarry` + append-carry transport helpers;
   - `BuiltWire.buildSymbolFromCarry`, `buildBranchFromCarry`,
     `buildWriteTermFromCarry`, `buildWriteBitAux / buildWriteBit`;
   - `linearWriteBitWire` as an explicit linear-step building block.
4. A critical carry-transport defect in the append-only fold has been
   fixed:
   - `buildSymbolFromCarry` no longer loses the external accumulator
     carry;
   - `buildBranchFromCarry` / `buildWriteTermFromCarry` preserve the
     carry;
   - `buildWriteBitAux` now actually performs `acc := acc OR term`.
5. New append-only blocks have been added to continue the linear
   step:
   - `moveIndex`;
   - `headStateSymbolPairs`;
   - `buildStateTermFromCarry`, `buildNextStateAux`,
     `buildNextState`;
   - `buildHeadTermFromCarry`, `buildNextHeadAux`, `buildNextHead`;
   - `buildNextTapeFromCarry`, `buildNextTape`;
   - public switch wires:
     `linearNextStateWire`, `linearNextHeadWire`, `linearNextTapeWire`.
6. The build passes:
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/StraightLineBuilder.lean`,
   - `lake build pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean`,
   - `lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean`.

Next step:

1. Assemble a single `stepCompiledLinear` (one shared circuit,
   selectors for `tape / head / state`) over the already-prepared
   blocks `writeBit / nextState / nextHead / nextTape`.
2. Isolate and pin the per-step gate increment in an explicit lemma.
3. Lift the increment through the iteration over `runTime` and close
   `CompiledRuntimeCircuitGateBound`.
