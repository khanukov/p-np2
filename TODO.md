# To-Do / План завершения формализации (P≠NP pipeline)

> **Status (2025-12-26)**: `pnp3/` конвейер полностью формализован и **не содержит аксиом**.
> Единственная условность остаётся из-за **внешних свидетельств (witnesses)** в части A
> (shrinkage/switching) и временного условия `AC0SmallEnough`.
> Этот файл фиксирует **что именно осталось доделать и как**, с привязкой к модулям,
> теоремам и интерфейсам Lean.

---

## Краткий анализ текущего состояния (A → B → C → D)

**Часть A (Switching/Atlas, shrinkage)**
- Реализованы теоремы:
  - `partial_shrinkage_for_AC0` (теорема, но с гипотезой `AC0SmallEnough`).
  - `shrinkage_for_localCircuit` (теорема, но зависит от `FamilyIsLocalCircuit` witness).
- AC⁰ пока фактически реализуется как глубина 2 (DNF), с **слабой оценкой глубины** `M^2`.
- В интерфейсах уже подготовлены параметры глубины `d` и сильная цель `polylog`.
- Введены структуры:
  - `FamilyIsAC0` / `AC0CircuitWitness` — свидетельства принадлежности семьи AC⁰.
  - `FamilyIsLocalCircuit` / `LocalCircuitWitness` — свидетельства локальности.

**Часть B (Covering-Power, ёмкостные оценки)**
- Леммы мощности покрываемых атласом семей доказаны без аксиом.
- Ключевая лемма: `approxOnTestsetWitness_injective` и цепочка следствий — все in Lean.

**Часть C (Античекер)**
- Полностью доказано: существование большого `Y` и тест-набора, на котором малые схемы
  ошибаются. Теоремы: `antiChecker_exists_large_Y`, `antiChecker_exists_testset`.
- Не использует внешних допущений — лишь части A и B.

**Часть D (Magnification)**
- Все триггеры (OPS, CJW, локальность) формализованы как **теоремы**:
  - `OPS_trigger_general`, `OPS_trigger_formulas`, `locality_trigger`,
    `CJW_sparse_trigger` — все без аксиом.
- Мост к финальному выводу собран в `Bridge_to_Magnification.lean`.

**Финальный вывод (P ≠ NP)**
- В `Magnification/FinalResult.lean` есть `P_ne_NP_final` / `P_ne_NP_final_general`.
- Текущая условность: гипотеза `hF_all : ∀ loc, FamilyIsLocalCircuit ...`.
- Внешняя теорема `P ⊆ P/poly` импортируется из `Facts/PsubsetPpoly`.

---

## Что мешает безусловному доказательству

1. **Нет внутренних конструкций свидетелей shrinkage**
   - В `partial_shrinkage_for_AC0` требуется `FamilyIsAC0` (witness для AC⁰).
   - В `shrinkage_for_localCircuit` требуется `FamilyIsLocalCircuit` (witness для локальных схем).
   - Сейчас это **внешние входы**, а не автоматически построенные структуры.

2. **Слабая глубинная оценка (Stage‑1: `M^2`)**
   - Введено условие `AC0SmallEnough` (`M^2 ≤ polylogBudget(n)`), чтобы состыковать
     слабую оценку с целевой `polylog`.
   - Нужно заменить доказательство на полноценную multi-switching лемму, чтобы
     `AC0SmallEnough` исчезло.

3. **Финальная гипотеза `hF_all`**
   - Она исчезнет автоматически, как только будет предоставлен real witness
     через `ExternalLocalityWitnessProvider`.

---

## План работ (детальный, по модулям и шагам)

### 1) Реализовать multi-switching lemma для глубины `d > 2`
**Цель:** получить сильную оценку `polylog` без `AC0SmallEnough`.

**Модули:**
- `pnp3/ThirdPartyFacts/Facts_Switching.lean`
- Возможное выделение нового модуля: `pnp3/ThirdPartyFacts/Facts_Switching_Strong.lean`

**Шаги:**
1. **Индукция по глубине `d`:**
   - База `d=1,2` уже покрыта DNF-конструкцией.
   - Переход `d → d+1`: реализовать multi-switching (Håstad-style),
     аккуратно формализовать объединение частичных сертификатов.
2. **Вывести `PartialCertificate` с глубиной `ac0DepthBound_strong` (polylog).**
3. **Переписать `partial_shrinkage_for_AC0`:**
   - Удалить гипотезу `hSmall : AC0SmallEnough params`.
   - Убрать промежуточные леммы вида `..._le_strong`.
4. **Сделать `partial_shrinkage_for_AC0` источником witness для SAL.**

**Ожидаемый результат:**
- `partial_shrinkage_for_AC0` — чистая теорема без дополнительных условий,
  со strong bound и использованием `FamilyIsAC0` как единственного входа.

---

### 2) Построить реальные AC⁰/Local witnesses (убрать внешний провайдер)
**Цель:** заменить `ExternalLocalityWitnessProvider` на внутренний конструктор.

**Модули:**
- `pnp3/ThirdPartyFacts/LocalityLift.lean`
- `pnp3/ThirdPartyFacts/Facts_Switching.lean`
- Возможный дополнительный модуль для инстанса witness.

**Шаги:**
1. **Из AC⁰ shrinkage получить `AC0CircuitWitness`:**
   - Через `Classical.choose` извлечь witness из существования `PartialCertificate`.
2. **Сконструировать `LocalCircuitWitness`:**
   - Использовать `LocalCircuitParameters.ofAC0` и `locality_lift`.
   - Гарантировать полилог-границы на `ℓ` и `|T|`.
3. **Определить новый `instance : ExternalLocalityWitnessProvider`**
   - Приоритет выше дефолтного (например `priority := 90`).
   - Заполнить поле `witness` реальным shrinkage-свидетельством.

**Ожидаемый результат:**
- Все `FamilyIsLocalCircuit` будут находиться автоматически через typeclass.
- Условность `hF_all` станет ненужной и будет удалена из финальных теорем.

---

### 3) Удалить `AC0SmallEnough` из конвейера
**Цель:** убрать все искусственные мосты между weak и strong bounds.

**Модули:**
- `pnp3/ThirdPartyFacts/Facts_Switching.lean`
- `pnp3/LB_Formulas/*.lean`
- `pnp3/Bridge_to_Magnification.lean` (если где-то просачивается условие)

**Шаги:**
1. Удалить `AC0SmallEnough` из сигнатур (часто в `partial_shrinkage_for_AC0`).
2. Удалить все леммы по подъёму `weak → strong`.
3. Проверить импорты, чтобы downstream не требовал старых условий.

---

### 4) Упростить финальные теоремы `P_ne_NP_final`
**Цель:** убрать `hF_all` и получить безусловный вывод.

**Модули:**
- `pnp3/Magnification/FinalResult.lean`
- `pnp3/Magnification/Bridge_to_Magnification.lean`

**Шаги:**
1. После появления witness-провайдера удалить `hF_all` из `P_ne_NP_final`.
2. Заменить вызовы на версию, которая не требует внешних параметров.
3. Обновить комментарии к финальным теоремам.

---

### 5) Финальная чистка и проверки
**Цель:** зафиксировать полностью автономный статус.

**Модули/файлы:**
- `pnp3/Tests/AxiomsAudit.lean`
- `AXIOMS_FINAL_LIST.md`, `FORMAL_PROOF_COMPLETE.md`, `README.md` (если нужно)

**Шаги:**
1. Прогнать `lake build` и убедиться, что `#print axioms` остаётся пустым.
2. Обновить документы (если нужно) до статуса: 0 аксиом, 0 внешних witnesses.

---

## Конкретные точки правки (кодовые якоря)

- **`pnp3/ThirdPartyFacts/Facts_Switching.lean`**
  - `partial_shrinkage_for_AC0` — сейчас зависит от `AC0SmallEnough`.
  - `partial_shrinkage_for_AC0_with_bound` — промежуточный артефакт Stage‑1.
  - `ac0DepthBound_weak/strong` — готовые границы, нужно сделать strong фактической.

- **`pnp3/ThirdPartyFacts/LocalityLift.lean`**
  - Класс `ExternalLocalityWitnessProvider` — заменить тривиальный instance.
  - Функции `locality_lift` / `locality_lift'` — ждут реальный witness.

- **`pnp3/Magnification/FinalResult.lean`**
  - Убрать `hF_all` после интеграции witness-провайдера.

---

## Текущий чеклист

- [ ] Multi-switching (полилог) для AC⁰ depth `d>2`.
- [ ] Удаление `AC0SmallEnough` и всех weak→strong мостов.
- [ ] Реальный `ExternalLocalityWitnessProvider`.
- [ ] Удаление `hF_all` из `P_ne_NP_final`.
- [ ] Финальная проверка `AxiomsAudit` и обновление документов.

---

## Примечания

- **Классическая логика (`Classical.choose`, `noncomputable`) не снижает строгости** —
  это допустимая методология Lean, используемая в формальных доказательствах.
- Все части B, C, D считаются завершёнными и не требуют доработки.
- Единственная «реальная» математика, остающаяся за пределами Lean, — это
  multi-switching lemma и конструкция witness-ов shrinkage.

