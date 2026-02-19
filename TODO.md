# To-Do / План завершения формализации (P≠NP pipeline)

> **Status (2025-12-26)**: активный `pnp3/` конвейер полностью переведён на **Partial MCSP**,
> формализован и **не содержит аксиом** внутри цепочки A→B→C→D (кроме двух внешних
> фактов NP‑трудности Partial MCSP, оформленных как отдельные аксиомы в
> `pnp3/ThirdPartyFacts/Hirahara2022.lean`).
> Единственная условность остаётся из-за **внешних свидетельств (witnesses)** в части A
> (shrinkage/switching), но сама цепочка построена и проверена.
> Legacy‑ветка GapMCSP перенесена в `archive/`.
>
> Этот файл фиксирует **что именно сделано** и какие дополнительные
> исследовательские задачи остаются вне активного конвейера.

---

> Дополнительно: структурированный асимптотический roadmap с явным разделением
> «можно сделать сразу» vs «нужны дополнительные вводные» вынесен в
> `ASYMPTOTIC_REPAIR_PLAN.md`.

## Краткий анализ текущего состояния (A → B → C → D)

**Часть A (Switching/Atlas, shrinkage)**
- Реализованы теоремы:
  - `partial_shrinkage_for_AC0` (теорема без доп. гипотез о малости).
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
- Все триггеры (OPS, CJW, локальность) формализованы как **теоремы** в partial‑треке.
- Мост к финальному выводу собран в `Bridge_to_Magnification_Partial.lean`.

**Финальный вывод (P ≠ NP)**
- В `Magnification/FinalResult.lean` есть `P_ne_NP_final` (partial‑цепочка).
- Текущая условность: гипотеза `hF_all : ∀ loc, FamilyIsLocalCircuit ...`.
- Внешняя теорема `P ⊆ P/poly` импортируется из `Facts/PsubsetPpoly`.
- Внешние аксиомы NP‑трудности Partial MCSP импортируются из
  `pnp3/ThirdPartyFacts/Hirahara2022.lean`.

---

## Что мешает безусловному доказательству (вне активного конвейера)

1. **Нет внутренних конструкций свидетелей shrinkage**
   - В `partial_shrinkage_for_AC0` требуется `FamilyIsAC0` (witness для AC⁰).
   - В `shrinkage_for_localCircuit` требуется `FamilyIsLocalCircuit` (witness для локальных схем).
   - Сейчас это **внешние входы**, а не автоматически построенные структуры.

2. **Слабая глубинная оценка (Stage‑1: `M^2`)**
   - Условие `AC0SmallEnough` удалено, но `ac0DepthBound_strong` теперь равна
     `max(M², polylog)`. Это сохраняет корректность, однако не даёт чистой
     polylog‑оценки без запаса.
   - Нужно заменить доказательство на полноценную multi-switching лемму и
     вернуть определение `ac0DepthBound_strong = polylog`.

3. **Финальная гипотеза `hF_all`**
   - Она исчезнет автоматически, как только будет предоставлен real witness
     через `Facts.LocalityLift.ShrinkageWitness.Provider`.

4. **Аксиомы NP‑трудности Partial MCSP**
   - Сейчас NP‑hardness задаётся аксиомами
     `PartialMCSP_profile_is_NP_Hard_rpoly` и `PartialMCSP_is_NP_Hard`.
   - Для полностью автономного доказательства нужен формальный перенос
     результата Hirahara (2022) в Lean (или импорт проверенной формализации
     как теоремы).

---

## Обновлённый план (multi-switching + индукция по глубине AC⁰)

Ниже — актуализированный план работ, основанный на multi-switching лемме и
индукции по глубине схем AC⁰. Он заменяет прежний «Stage‑1» подход и детально
указывает, какие математические шаги и интерфейсы должны быть реализованы в Lean.

### 1) Теоретическая база — multi-switching lemma
**Цель:** заменить слабую оценку `M²` на реальную полилог‑оценку, построенную на
обобщении switching‑леммы Хастада к семействам формул.

**Ключевые идеи:**
- Одиночная switching‑лемма: при случайной `p`‑рестрикции `k`‑CNF/`k`‑DNF
  превращается в дерево решений глубины `t` с вероятностью
  `≥ 1 - (C·p·k)^t`.
- **Multi‑switching:** для семейства из `S` формул одной рестрикцией можно
  одновременно упростить их все. Вероятность неудачи оценивается как
  `S^{⌈t/ℓ⌉} · (C·p·k)^t`, где `ℓ` — длина ствола частичного дерева решений.

**Литературная база:**
Impagliazzo–Matthews–Paturi (2012), Servedio–Tan (2019), Håstad (1986).

---

### 2) Индукция по глубине `d` (AC⁰)
**Цель:** получить общий полилог‑сертификат глубины `t` для схем глубины `d`.

**База `d=2` (DNF/CNF):**
- Сразу применяем multi‑switching к множеству термов ширины `k`.
- При параметрах `p = Θ(1/k)` и `ℓ = Θ(log M)` получаем частичный сертификат
  глубины `O(log M)`; на листьях формула сводится к константе или литере.

**Переход `d → d+1`:**
- Рассматриваем нижний слой формул (CNF/DNF) и применяем multi‑switching
  ко всему семейству.
- Получаем общий ствол глубины `ℓ`, на листьях которого исходная схема
  превращается в подсхему глубины `d` размера `M' = M^{O(1)}`.
- По индукции строим хвостовые деревья и «склеиваем» со стволом.
- Итоговая глубина: `t = ℓ + t₂`, где `t₂` — полилог от `M'`.
  Следовательно, `t` остаётся полилогом от `M`.

---

### 3) Вероятностный аргумент → детерминированное существование
**Цель:** превратить «с высокой вероятностью» в «существует конкретная рестрикция».

**Инструмент:**
- Использовать `Classical.choose` для извлечения свидетеля из факта
  существования (следует из положительной вероятности).
- Дерандомизация не требуется, так как цель — существование сертификата.

---

### 4) Сертификаты shrinkage и оценка числа подкубов
**Цель:** формализовать `PartialCertificate` и оценить размер покрытия.

**Ключевые факты:**
- Сертификат состоит из ствола (ℓ ограничений) и хвостов (деревья глубины `≤ t₂`).
- Общая глубина `t` даёт число листьев `≤ 2^t` через
  `PDT.leaves_length_le_pow_depth`.
- Подставляя `t = polylog(M)`, получаем квазиполиномиальную оценку числа подкубов.

---

### 5) Интеграция в AC0PolylogBoundWitness и снятие аксиом
**Цель:** заменить аксиому multi‑switching реальным доказательством.

**Шаги:**
1. Доказать `partial_shrinkage_for_AC0` без аксиом и без `AC0SmallEnough`.
2. Удалить `max(M², polylog)` и вернуть чистую `ac0DepthBound_strong = polylog`.
3. Построить реальные `AC0CircuitWitness` и `LocalCircuitWitness`
   через `Classical.choose` и `locality_lift`.
4. Подменить `Facts.LocalityLift.ShrinkageWitness.Provider` на внутренний instance.
5. Удалить `hF_all` из `P_ne_NP_final` и очистить финальные теоремы.

---

## Конкретные точки правки (кодовые якоря)

- **`pnp3/ThirdPartyFacts/Facts_Switching.lean`**
  - `partial_shrinkage_for_AC0` — сильная граница строится через `max(M², polylog)`;
    нужно заменить на чистую polylog‑оценку после multi-switching.
  - `partial_shrinkage_for_AC0_with_bound` — промежуточный артефакт Stage‑1.
  - `ac0DepthBound_weak/strong` — готовые границы, нужно сделать strong фактической.

- **`pnp3/ThirdPartyFacts/PartialLocalityLift.lean`**
  - Класс `Facts.LocalityLift.ShrinkageWitness.Provider` — заменить тривиальный instance.
  - Мост `locality_lift` в partial‑цепочке ждёт реальный witness.

- **`pnp3/Magnification/FinalResult.lean`**
  - Убрать `hF_all` после интеграции witness-провайдера.

---

## Чеклист активного конвейера (выполнено)

- [x] Partial‑модель и язык: `PartialTruthTable`, `Model_PartialMCSP`.
- [x] Барьер локальности обойдён: рестрикции сохраняют тип в `Model_PartialMCSP`
  (`restriction_preserves_type` и связанный `restrictTable_eq_applyRestriction`).
- [x] Anti‑checker и локальные lower bounds для Partial MCSP.
- [x] Partial‑pipeline statements и magnification bridge.
- [x] FinalResult переведён на Partial MCSP.
- [x] GapMCSP‑ветка перенесена в `archive/`.
- [x] Документация и тесты ориентированы на partial‑конвейер.

---

## Архив/исследовательский backlog (не блокирует активный конвейер)

Эти задачи описывают возможные усиления/улучшения, но не нужны для текущей
partial‑цепочки. Их реализация не требуется для воспроизведения `P_ne_NP_final`.

### Multi‑switching (усиление оценок)
- Реальная конструкция CCDT/encoding (канонический DT, явная инъекция).
- Оценка мощности множества кодов и доказательство `codes.card < (R_s s).card`.
- Интеграция в `Facts_Switching.lean`: заменить `max(M², polylog)` на чистую polylog‑оценку.

### Witness‑ы локальности
- Встроить реальный `Facts.LocalityLift.ShrinkageWitness.Provider` из shrinkage.
- Убрать гипотезу `hF_all` в `Magnification/FinalResult.lean`.

### Контроль соответствия комментариев и кода
- Проверить, что все комментарии в `AC0/MultiSwitching/*` соответствуют
  фактическим определениям (особенно вокруг `BadEvent`, `EncodingWitness`, `R_s`).
- Сверить описания в `Facts_Switching.lean` с реальными параметрами и границами.

---

## Partial MCSP: переход на частичные функции (локальность/рестрикции)

Ниже — актуальный список задач по переходу на Partial MCSP. Подробности и
обоснования см. в `PARTIAL_MCSP_PLAN.md`.

### Модель и язык
- [x] Добавить `pnp3/Models/PartialTruthTable.lean` (decode, mask/values, утилиты).
- [x] Добавить `pnp3/Models/Model_PartialMCSP.lean` с `PartialFunction`
  (канонический тип), `PartialTruthTable` (алиас), `GapPartialMCSPParams`,
  `is_consistent`, `PartialMCSP_YES/NO` и `gapPartialMCSP_Language`.
- [x] Зафиксировать кодирование входа `mask ++ values` для `Option Bool`
  (`BitVec (2 * 2^n)`).
- [x] Переместить `Models/Model_GapMCSP.lean` в архив как legacy‑ветку.

### Рестрикции и замкнутость
- [x] Доказать (не аксиоматизировать) лемму `restriction_preserves_type`
  для Partial MCSP.
- [x] Явно задокументировать проекцию индексов при уменьшении числа переменных.
- [x] Добавить утилиты рестрикции на уровне входов (`applyRestrictionToAssignment`)
  для использования в доказательствах согласованности.

### Anti-checker и lower bounds
- [x] Добавить `pnp3/LowerBounds/AntiChecker_Partial.lean` под Partial MCSP
  (старый файл оставить как legacy).
- [x] Добавить вероятностную лемму: случайная частичная функция (с α-определённостью)
  с высокой вероятностью не имеет малой согласованной схемы.
- [x] Добавить partial‑версию ядра шага C (`LB_Formulas_Core_Partial.lean`)
  на базе anti-checker.
- [x] Добавить partial‑версию формулировок шага C
  (`Magnification/PipelineStatements_Partial.lean`).
- [x] Подключить partial‑ядро шага C в магнификационный конвейер
  (partial‑версия `Bridge_to_Magnification_Partial` и wiring в `FinalResult`).
- [x] Портировать locality‑lift на Partial MCSP и удалить временную аксиому
  `OPS_trigger_formulas_partial`.
- [x] Сделать `FinalResult` полностью partial и убрать legacy‑ветку из
  основного вывода.

### NP-hardness (Hirahara 2022)
- [x] Добавить файл `pnp3/ThirdPartyFacts/Hirahara2022.lean` с аксиомами
  `PartialMCSP_profile_is_NP_Hard_rpoly` и `PartialMCSP_is_NP_Hard`.
- [x] Обновить финальные выводы (например, `Magnification/FinalResult.lean`)
  на аксиомы Hirahara.
- [ ] Довести NP‑hardness до формальной теоремы (перенос доказательства или
  импорт проверенной формализации).

### Документация и аудит
- [x] Обновить `AXIOMS_FINAL_LIST.md` и документы аудита с текущим списком аксиом.
- [x] Убедиться, что в README/FAQ нет устаревших ссылок на GapMCSP в контексте
  «барьера локальности».

---

## Примечания

- **Классическая логика (`Classical.choose`, `noncomputable`) не снижает строгости** —
  это допустимая методология Lean, используемая в формальных доказательствах.
- Все части B, C, D считаются завершёнными и не требуют доработки.
- Единственная «реальная» математика, остающаяся за пределами Lean, — это
  multi-switching lemma и конструкция witness-ов shrinkage.
