# Анализ конструктивности доказательства P≠NP (активный `pnp3/`)
## Дата: 2026-02-19

## Что уже надёжно закрыто в Lean

- Шаги B/C/D (counting, anti-checker ядро, magnification bridge) формально
  доказаны как теоремы.
- В активном коде `pnp3/` нет `sorry/admit`.
- Профиль аксиом-зависимостей ключевых узлов зафиксирован и проверяется в CI:
  `pnp3/Tests/AxiomsAudit.lean` и `pnp3/Tests/CoreConeAxiomsAudit.lean`.

## Текущие внешние входы

### Явные аксиомы (`pnp3/`)

1. `PartialMCSP_profile_is_NP_Hard_rpoly`
2. `PartialMCSP_is_NP_Hard`
3. `localizedFamilyWitness_partial`

Файлы:
- `pnp3/ThirdPartyFacts/Hirahara2022.lean`
- `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`

### Witness-backed теоремы (не аксиомы)

- `partial_shrinkage_for_AC0`
- `shrinkage_for_localCircuit`

Обе теоремы требуют внешние witness-объекты, что отдельно отслеживается в
документации и дорожной карте.

## Ключевой статус финального конуса

- `P_ne_NP_final` и `P_ne_NP_final_asymptotic` зависят от
  `localizedFamilyWitness_partial` (плюс базовые `propext`, `Classical.choice`,
  `Quot.sound`).
- Узлы ниже по конусу (`P_ne_NP_from_partial_formulas`, OPS/local bridge,
  lower-bound core) не тянут project-specific axioms и зависят только от
  базовых классических аксиом Lean.

Это означает, что проектный внешний gap в финальном конусе сейчас локализован
в одном месте.

## Что ещё мешает безусловному результату

1. Закрыть `localizedFamilyWitness_partial` конструктивным доказательством.
2. Закрыть NP-hardness аксиомы Partial MCSP из `Hirahara2022.lean`.
3. Довести witness-путь shrinkage (Part A) до полностью внутреннего
   конструктивного провайдера.

## Проверка воспроизводимости

```bash
lake build
bash scripts/check.sh
lake env lean pnp3/Tests/AxiomsAudit.lean
lake env lean pnp3/Tests/CoreConeAxiomsAudit.lean
```
