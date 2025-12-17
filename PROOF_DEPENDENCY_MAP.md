# Полная карта зависимостей доказательства P≠NP
## От аксиом к финальной теореме

Last updated: 2025-12-16

---

## 🎯 ФИНАЛЬНАЯ ЦЕЛЬ

```lean
theorem P_ne_NP_final : P_ne_NP := ...
```
**Location**: `pnp3/Magnification/FinalResult.lean:57`

---

## 📊 ПОЛНАЯ ЦЕПОЧКА ЗАВИСИМОСТЕЙ

### Уровень 5: ФИНАЛЬНАЯ ТЕОРЕМА
```
P_ne_NP_final
  └─→ P_ne_NP_from_pipeline_kit_formulas
```

### Уровень 4: МОСТ К P≠NP
```
P_ne_NP_from_pipeline_kit_formulas
  ├─→ bridge_from_pipeline_kit_formulas → NP_not_subset_Ppoly
  ├─→ P_ne_NP_of_nonuniform_separation (theorem)
  └─→ P_subset_Ppoly_proof (theorem)
```

### Уровень 3: МАГНИФИКАЦИЯ (Part D)
```
bridge_from_pipeline_kit_formulas
  ├─→ kit.formula_hypothesis → FormulaLowerBoundHypothesis
  ├─→ OPS_trigger_formulas (proved; specialization of OPS_trigger_general)
  └─→ NP_not_subset_Ppoly_of_contra (logic wrapper)

bridge_from_sparse_statement / bridge_from_sparse_kit
  ├─→ SparseLowerBoundHypothesis (разреженные языки)
  └─→ CJW_sparse_trigger (proved; явный малый sparse solver)

bridge_from_LB_Local / bridge_from_pipeline_kit_local
  ├─→ LocalLowerBoundHypothesis
  └─→ Locality_trigger (proved via locality_lift)
```

### Уровень 2: PIPELINE KIT (Интеграция Parts A+B+C)
```
PipelineBridgeKit = pipelineBridgeKit
  ├─→ ac0_statement_from_pipeline → AC0Statement
  ├─→ local_statement_from_pipeline → LocalStatement
  ├─→ general_statement_from_locality → GeneralCircuitStatement
  ├─→ formula_hypothesis_from_pipeline → FormulaLowerBoundHypothesis
  ├─→ local_hypothesis_from_pipeline → LocalLowerBoundHypothesis
  ├─→ general_hypothesis_from_pipeline
  └─→ general_hypothesis_from_locality
```

### Уровень 1: LOWER BOUNDS (Part C)
```
formula_hypothesis_from_pipeline
  └─→ LB_Formulas_statement
      └─→ LB_Formulas_core
          ├─→ antiChecker_exists_testset (PROVEN, relies on AXIOM `antiChecker_exists_large_Y`)
          └─→ no_bounded_atlas_on_testset_of_large_family
              └─→ approxOnTestset_subset_card_le (Part B)
```
```
ac0_statement_from_pipeline
  └─→ LB_Formulas_core
      └─→ antiChecker_exists_testset (PROVEN, relies on AXIOM `antiChecker_exists_large_Y`)
```
```
local_statement_from_pipeline
  └─→ LB_LocalCircuits_core
      └─→ antiChecker_exists_testset_local [AXIOM C.9]
```

### Уровень 0: CORE INFRASTRUCTURE (Parts A+B)

**Part B: Counting/Capacity**
```
no_bounded_atlas_on_testset_of_large_family
  └─→ approxOnTestset_subset_card_le
      └─→ approxOnTestset_card_le
          └─→ approxOnTestsetWitness_injective (PROVEN)
```

**Part A: SAL Core**
```
scenarioFromAC0
  ├─→ ac0PartialWitness
  │   └─→ partial_shrinkage_for_AC0 [AXIOM A.1]
  └─→ PDT → Atlas construction (PROVEN)

locality_lift
  └─→ shrinkage_for_localCircuit [AXIOM A.2]
```

---

## 🔴 АКТИВНЫЕ АКСИОМЫ (минимальный набор)

Всего: **5** (только Parts A/C; Part D целиком доказан).

### Part A — Switching/Shrinkage (2)
1. `partial_shrinkage_for_AC0` — Håstad (1986), Servedio–Tan (2019).
2. `shrinkage_for_localCircuit` — Williams (2014), Chen–Oliveira–Santhanam (2022).

### Part C — Anti-checker lower bounds (3)
3. `antiChecker_exists_large_Y`
4. `antiChecker_exists_large_Y_local`
5. `antiChecker_exists_testset_local`
   - Sources: Lipton–Young (1994), Chapman–Williams (2015), OPS (2019/2021).
   - `antiChecker_exists_testset` теперь доказана из п.3.

Интерфейсные леммы `P_subset_Ppoly_proof` и `P_ne_NP_of_nonuniform_separation` импортированы как теоремы и не считаются аксиомами.

---

## 📌 СТАТУС PART D

- Все триггеры (`OPS_trigger_general`, `OPS_trigger_formulas`, `Locality_trigger`, `CJW_sparse_trigger`) доказаны в `pnp3/Magnification/Facts_Magnification.lean`.
- Мосты (`Bridge_to_Magnification.lean`) используют только доказанные триггеры и аксиомы Parts A/C; в блоке D нет незакрытых допущений.
