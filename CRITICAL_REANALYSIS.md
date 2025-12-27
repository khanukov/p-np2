# Критический пересмотр аксиоматики (обновление 2025-12-25)

## 1. Минимальный набор для вывода `P_ne_NP`

```
P_ne_NP_final
  └─ bridge_to_magnification
      ├─ antiChecker_exists_large_Y        (THEOREM, derived)
      ├─ partial_shrinkage_for_AC0         (THEOREM, external witness)
      └─ OPS_trigger_formulas              (THEOREM D.2)
```

Финальный аргумент опирается на внешний shrinkage-свидетель для A.1,
а также на доказанный античекер для AC⁰ и магнификационный триггер для формул
(D.2, теперь доказанный). Другой внешний результат (A.2) нужен для локальных
сценариев и расширений.

## 2. Полный список внешних входов

| Категория | Входы | Назначение |
|-----------|-------|------------|
| Part A | `partial_shrinkage_for_AC0`, `shrinkage_for_localCircuit` (theorems + witnesses) | Switching-леммы |
| Part C | — | Anti-checker результаты доказаны |
| Part D | — | Магнификационные триггеры доказаны |

Интерфейсные утверждения `P_subset_Ppoly_proof` и
`P_ne_NP_of_nonuniform_separation` являются теоремами, а не аксиомами.

## 3. Статус инфраструктуры

- `pnp3/Complexity/Interfaces.lean` — содержит доказанные теоремы, заглушек нет.
- `pnp3/LowerBounds/AntiChecker.lean` — все утверждения anti-checker доказаны (включая локальную версию).
- `pnp3/Magnification/Facts_Magnification.lean` — все триггеры (`OPS_trigger_general`,
  `OPS_trigger_formulas`, `Locality_trigger`, `CJW_sparse_trigger`) доказаны.
- `ThirdPartyFacts/Facts_Switching.lean` — две базовые switching-теоремы, требующие witness.

## 4. Риски и приоритеты

1. **Switching (Part A)** — наибольшая техническая сложность; без новых
   инструментов формализация малореалистична.
2. **Magnification (Part D)** — блок завершён; ресурсы можно переключить на A.

## 5. Рекомендации

- Поддерживать документацию в синхронизации с кодом (см. `AXIOMS_FINAL_LIST.md`).
- Отдельно отслеживать архивные файлы; при необходимости переносить подтверждённые
  доказательства в основную ветку.
- Сфокусироваться на поэтапной формализации shrinkage-свидетелей, используя обновлённый
  интерфейс `P_subset_Ppoly`.
