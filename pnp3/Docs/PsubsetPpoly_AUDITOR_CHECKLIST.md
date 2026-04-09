# PsubsetPpoly Auditor Checklist

Дата: 2026-04-03.

Scope note:
этот checklist проверяет только inclusion-side `P ⊆ PpolyDAG`.

Цель: быстро и машинно проверить, что default-route для
`P ⊆ PpolyDAG` не зависит от старого legacy-хвоста.

## 1) Проверка удаления legacy runtime ветки

```bash
rg -n "def step\b|def runConfig\b|def runtimeConfig\b|runtimeConfig_eq_initial" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean
```

Ожидание: пустой вывод.

## 2) Проверка активного no-arg endpoint

```bash
rg -n "theorem proved_P_subset_PpolyDAG_internal|theorem proved_P_subset_PpolyDAG_internal_defeq_linear" \
  pnp3/Complexity/Simulation/Circuit_Compiler.lean
```

Ожидание: обе теоремы найдены.

## 3) Проверка, что финальный слой использует no-arg endpoint

```bash
rg -n "proved_P_subset_PpolyDAG_internal" pnp3/Magnification/FinalResultCore.lean
```

Ожидание: есть использование в default-route.

## 4) Проверка explicit-wrapper route (linear, не iterated-legacy)

```bash
rg -n "PsubsetPpolyCompiledRuntimeLinearOutputContracts|proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts" \
  pnp3/Magnification/FinalResultCore.lean pnp3/Barrier/Bypass.lean
```

Ожидание: `with_provider`/`with_barriers` привязаны к linear bundle.

## 5) Проверка отсутствия дыр в ключевых файлах

```bash
rg -n "sorry|admit|^\s*axiom\b|^\s*constant\b" \
  pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean \
  pnp3/Complexity/Simulation/Circuit_Compiler.lean
```

Ожидание: пустой вывод.

## 6) Проверка аксиом conversion-слоя (без скрытых допущений)

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

Ожидание: только стандартные логические зависимости (`propext`, `Quot.sound`),
без project-local `axiom`.

## 7) Сборка ключевых модулей

```bash
lake build \
  Complexity.PsubsetPpolyInternal.Simulation \
  Complexity.Simulation.Circuit_Compiler \
  Magnification.FinalResult
```

Ожидание: успешная сборка.

## 8) Полная сборка репозитория (рекомендуется)

```bash
lake build
```

Ожидание: успешная сборка.
