# Критический пересмотр аксиоматики (обновление 2025-10-24)

## 1. Минимальный набор для вывода `P_ne_NP`

```
P_ne_NP_final
  └─ bridge_to_magnification
      ├─ antiChecker_exists_testset        (AXIOM C.2)
      ├─ partial_shrinkage_for_AC0         (AXIOM A.1)
      └─ OPS_trigger_formulas              (AXIOM D.2)
```

Финальный аргумент опирается на три внешних результата: switching (A.1),
anti-checker с тестовым множеством (C.2) и магнификационный триггер для формул
(D.2). Остальные семь аксиом поддерживают обобщения (локальные/разреженные
варианты) и используются в вспомогательных сценариях.

## 2. Полный список активных аксиом

| Категория | Аксиомы | Назначение |
|-----------|---------|------------|
| Part A | `partial_shrinkage_for_AC0`, `shrinkage_for_localCircuit` | Switching-леммы |
| Part C | `antiChecker_exists_large_Y`, `antiChecker_exists_testset`,<br>`antiChecker_exists_large_Y_local`, `antiChecker_exists_testset_local` | Anti-checker игры |
| Part D | `OPS_trigger_general`, `OPS_trigger_formulas`,<br>`Locality_trigger`, `CJW_sparse_trigger` | Magnification |

Интерфейсные утверждения `P_subset_Ppoly_proof` и
`P_ne_NP_of_nonuniform_separation` являются теоремами, а не аксиомами.

## 3. Статус инфраструктуры

- `pnp3/Complexity/Interfaces.lean` — содержит доказанные теоремы, заглушек нет.
- `pnp3/LowerBounds/AntiChecker.lean` — четыре аксиомы, остальные факты доказаны.
- `pnp3/Magnification/Facts_Magnification.lean` — четыре триггера оформлены как
  внешние аксиомы, остальная часть файла доказуема.
- `ThirdPartyFacts/Facts_Switching.lean` — две базовые switching-аксиомы.

## 4. Риски и приоритеты

1. **Switching (Part A)** — наибольшая техническая сложность; без новых
   инструментов формализация малореалистична.
2. **Anti-checker (Part C)** — требует серьёзной комбинаторной инфраструктуры, но
   потенциально выполнимо при долгосрочном финансировании.
3. **Magnification (Part D)** — наилучший кандидат для ближайших проектов; можно
   попытаться формализовать один из триггеров (например, `OPS_trigger_formulas`).

## 5. Рекомендации

- Поддерживать документацию в синхронизации с кодом (см. `AXIOMS_FINAL_LIST.md`).
- Отдельно отслеживать архивные файлы; при необходимости переносить подтверждённые
  доказательства в основную ветку.
- Сфокусироваться на поэтапном снятии magnification-аксиом, используя обновлённый
  интерфейс `P_subset_Ppoly`.
