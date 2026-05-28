# PsubsetPpoly auditor checklist

Date: 2026-04-03.

Scope note: this checklist verifies the inclusion side `P ⊆ PpolyDAG`
only.

Goal: machine-check, quickly, that the default route for
`P ⊆ PpolyDAG` does not depend on the old legacy tail.

## 1) Check that the legacy runtime branch was removed

```bash
rg -n "def step\b|def runConfig\b|def runtimeConfig\b|runtimeConfig_eq_initial" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean
```

Expected: empty output.

## 2) Check the active no-arg endpoint

```bash
rg -n "theorem proved_P_subset_PpolyDAG_internal|theorem proved_P_subset_PpolyDAG_internal_defeq_linear" \
  pnp3/Complexity/Simulation/Circuit_Compiler.lean
```

Expected: both theorems found.

## 3) Check that the final layer uses the no-arg endpoint

```bash
rg -n "proved_P_subset_PpolyDAG_internal" pnp3/Magnification/FinalResultCore.lean
```

Expected: a usage in the default route.

## 4) Check the explicit-wrapper route (linear, not iterated-legacy)

```bash
rg -n "PsubsetPpolyCompiledRuntimeLinearOutputContracts|proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts" \
  pnp3/Magnification/FinalResultCore.lean pnp3/Barrier/Bypass.lean
```

Expected: `with_provider` / `with_barriers` wired to the linear
bundle.

## 5) Check that key files have no holes

```bash
rg -n "sorry|admit|^\s*axiom\b|^\s*constant\b" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean \
  pnp3/Complexity/Simulation/Circuit_Compiler.lean
```

Expected: empty output.

## 6) Check axioms of the conversion layer (no hidden assumptions)

```bash
cat > /tmp/pnp3_axiom_check_adapter.lean <<'EOF'
import Complexity.PpolyDAG_from_StraightLine
import Complexity.PsubsetPpolyDAG_Internal

#print axioms Pnp3.Complexity.StraightLineAdapter.ppolyDAG_of_straightLine_family
#print axioms Pnp3.Complexity.ppolyDAG_of_ppolyStraightLine
#print axioms Pnp3.Complexity.P_subset_PpolyDAG_of_P_subset_PpolyStraightLine
EOF

lake env lean /tmp/pnp3_axiom_check_adapter.lean
```

Expected: standard logical dependencies only (`propext`, `Quot.sound`),
with no project-local `axiom`.

## 7) Build the key modules

```bash
lake build \
  Complexity.PsubsetPpolyInternal.Simulation \
  Complexity.Simulation.Circuit_Compiler \
  Magnification.FinalResult
```

Expected: successful build.

## 8) Full repository build (recommended)

```bash
lake build
```

Expected: successful build.
