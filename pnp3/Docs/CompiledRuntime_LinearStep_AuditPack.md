# Compiled runtime linear-step audit pack

Date: 2026-03-02
Status: ready-for-audit (engineering checkpoint)

> Current-scope note (2026-04-03):
> this is an inclusion-only checkpoint.  It is not the source of the
> current global status of the final DAG blockers.

## Update (2026-03-13): checkpoint superseded

After a recheck on the current tree:

- `./scripts/check.sh` passes;
- the current audit / regression tests pass
  (`AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`).

Status relative to the checkpoint below:

1. The internal one-step provider is closed:
   `stepCompiledLinearCandidateStepSpecProvider_internal`.
2. The linear correctness branch is closed via
   `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider`
   with the internal provider
   `stepCompiledLinearCandidateStepSpecProvider_internal`.
3. The linear size route stays closed
   (`CompiledRuntimeCircuitSizeBoundLinear_internal`).

The current active route to no-arg `P ⊆ PpolyDAG` relies on the
internal output-wire witness `CompiledAcceptOutputWireAgreementLinear`.

The rest of the file below is a historical engineering checkpoint.

## 1. What is constructively in place

In `Simulation.lean` an append-only linear one-step scaffold is
assembled without a truth-table inside the new builder blocks:

1. Base blocks:
   - `buildSymbolFromCarry`,
   - `buildBranchFromCarry`,
   - `buildWriteTermFromCarry`.
2. Computing the write:
   - `buildWriteBitAux`, `buildWriteBit`.
3. Computing the next state:
   - `buildStateTermFromCarry`, `buildNextStateAux`,
     `buildNextState`.
4. Computing the next head position:
   - `moveIndex`,
   - `buildHeadTermFromCarry`, `buildNextHeadAux`, `buildNextHead`.
5. Computing the next tape contents:
   - `buildNextTapeFromCarry`, `buildNextTape`.
6. The formalised staging contract:
   - `LinearStepBlueprint`,
   - `linearStepBlueprint`,
   - `linearStepBlueprint_ready`,
   - `linearStepBlueprint_base_le`.

Checkpoint meaning: the full set of components
`writeBit / nextTape / nextHead / nextState` exists as append-only
builders over `sc.circuit`.

## 2. Critical review of the chosen path

Why this is the right path:

1. The old route (`stepCompiledTruthTable`) unfolds the step through
   the tree / truth-table layer and cannot realistically close the
   internal size bound on the runtime iteration.
2. The new route builds steps by appending gates to the existing DAG,
   which is structurally compatible with a proof of the form:
   - one-step increment,
   - iteration over `runTime`,
   - `CompiledRuntimeCircuitGateBound`,
   - `CompiledRuntimeCircuitSizeBound`.

Why this is not yet the finish line:

1. `stepCompiledLinear` is not yet switched to the new blueprint.
2. There is no closed per-step gate-increment lemma for the new
   assembly.
3. There is no final bridge from the increment to the runtime
   iteration specifically for the linear step.

## 3. Current risk picture

Low risk:

1. The local builder blocks exist and compile.
2. Carry-transport consistency in the folds (after the defect fix)
   is confirmed by the build and by the definition structure.

Medium risk:

1. Assembling a single shared circuit for all selectors
   (`tape / head / state`) is not yet fixed in one constructor.

High risk (main remainder):

1. A formal gate-growth bound for the new one-step assembly is
   needed; otherwise `CompiledRuntimeCircuitGateBound` does not
   close.

## 4. What auditors can check right now

Quick commands:

```bash
lake build pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean
lake build pnp3/Complexity/Simulation/Circuit_Compiler.lean
lake env lean pnp3/Tests/StepCompiledLinearBlueprint.lean
```

Spot-check the key definitions:

```bash
rg -n "buildWriteBit|buildNextState|buildNextHead|buildNextTape|LinearStepBlueprint|linearStepBlueprint_ready" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean
rg -n "linearStepBlueprint_base_le|stepCompiledLinearBlueprint_ready_check|stepCompiledLinearBlueprint_base_le_check" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean pnp3/Tests/StepCompiledLinearBlueprint.lean
rg -n "sorry|admit" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean \
  pnp3/Tests/StepCompiledLinearBlueprint.lean \
  pnp3/Docs/CompiledRuntime_LinearStep_AuditPack.md
```

## 5. Next mandatory technical step

1. Construct a single `stepCompiledLinear` from `LinearStepBlueprint`
   on one shared circuit.
2. Prove the one-step increment bound for gates.
3. Lift it through the iteration and close:
   - `CompiledRuntimeCircuitGateBound`,
   - `CompiledRuntimeCircuitSizeBound`.
