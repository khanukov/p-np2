# MultiSwitching: статус, контекст и план завершения

Этот файл служит точкой входа для разработчика, который будет доводить до конца
индуктивный шаг глубины `d → d + 1` в доказательстве `partial_shrinkage_for_AC0`.
Здесь собраны:

* список инфраструктуры, уже реализованной в репозитории, с точными ссылками на
  файлы и определения;
* перечень оставшихся задач и их декомпозиция на конкретные шаги;
* подробный план закрытия шага `d → d + 1` и последующих действий.

Если вы впервые знакомитесь с кодом, начните с раздела «Что уже готово», затем
перейдите к «Что ещё предстоит сделать» и, наконец, следуйте пошаговому плану
из раздела «Чек-лист завершения».

## 1. Что уже готово

Ниже перечислены основные результаты, которые можно напрямую использовать в
оставшейся работе. Для каждого пункта указаны файлы и ключевые конструкции.

### 1.1 Локальный (depth-1) анализ
* **Файл:** `pnp3/ThirdPartyFacts/Depth1_Switching.lean`
* **Статус:** доказаны леммы, связывающие ось (`Axis`), хвосты
  (`AxisTailSystem.TailCertificate`) и погрешность `errU` для каждого пакета
  глубины 1.
* **Полезные конструкции:**
  * `Depth1WitnessInput`, `Depth1WitnessInput.Budgeted`
  * `AxisWitness.toTailCertificate`, `tailCertificateWithinBudget`
  * оценки `ε` и глубины хвоста в пределах `depthBudget`.

### 1.2 Агрегация пакетов глубины 1
* **Файл:** `pnp3/ThirdPartyFacts/MultiSwitching/Core.lean`
* **Статус:** реализована нормализация пакетов и сбор комбинированных
  параметров.
* **Ключевые функции:**
  * `flattenedCNFs`, `totalBadBound`, `combinedTailSelectors`
  * `Depth1WitnessInput.Budgeted.normalizeDepthIndices`
  * `combinedTailSelectors_mem_of_pkg_fun`, `CombinedAxisWitness`

### 1.3 Пул селекторов и присваиваний
* **Файл:** `pnp3/ThirdPartyFacts/MultiSwitching/SelectorPool.lean`
* **Статус:** собраны инструменты для работы с селекторами на фиксированной оси.
* **Основные структуры и леммы:**
  * `leafSelectorPool`, `leafSelectorFinset`, `leafSelectorAssignments`
  * `selectorAssignments`, `selectorTailAssignments`, `selectorTailSupport`
  * `assignMany_selectorAssignments_self`,
    `assignMany_selectorTailAssignments`
  * `TailAssignmentBundle`, `TailAssignmentBundle.popHead`,
    `TailAssignmentBundle.toPDT`
* **Назначение:** эти конструкции позволяют представлять каждый селектор как
  пару (подкуб, список присваиваний), фильтровать по листу оси и постепенно
  восстанавливать селектор с помощью `Subcube.assignMany`. Они уже содержат
  необходимые доказательства об отсутствии дубликатов, корректности поддержки и
  уменьшении длины списков при разборе.

### 1.4 Документация и дорожные карты
* **Файлы:**
  * `pnp3/Core/BooleanBasics.lean` — общий паспорт SAL-инфраструктуры.
  * `pnp3/ThirdPartyFacts/MultiSwitching_Gaps.md` (настоящий документ) —
    актуальный план работ по многослойному шагу.
* **Статус:** описан текущий прогресс, перечислены ключевые вспомогательные
  леммы и подцели.

## 2. Что осталось сделать

1. **Построить глобальные хвосты (`globalTail β`).**
   * Нужно объединить локальные селекторы всех пакетов глубины 1 на общей оси,
     нормализовать их до попарно несовместных листьев и построить хвостовой PDT
     с этими листьями.
   * Требуемые свойства:
     * `selectors_mem_global`: любой селектор из объединённого списка — лист
       построенного `globalTail β`.
     * `depth_globalTail_le`: глубина хвоста контролируется значением
       `τ + Δβ`, где `Δβ` зависит только от количества нормализованных листьев.
     * `errU_globalTail_le`: погрешность объединённого хвоста не превосходит
       суммы локальных погрешностей (можно использовать `totalBadBound`).

2. **Упаковать результат в `CombinedTailCertificate`.**
   * Добавить поля `tails`, `epsilon` и соответствующие леммы (`selectors_mem`,
     `depth_ok`, `err_bound`).
   * Реализовать конструктор
     `chooseCombinedTailCertificate` без `sorry`, используя глобальные хвосты.

3. **Реализовать `Depth1WitnessInput.build`.**
   * На основе `CombinedTailCertificate` построить `AxisTailSystem.TailCertificate`
     и `PartialCertificate` глубины `d + 1`.
   * Доказать вспомогательные леммы о селекторах, глубине и погрешности
     полученного сертификата.

4. **Завершить индуктивный шаг и убрать аксиому.**
   * Использовать готовый сертификат для доказательства шага `d → d + 1`.
   * Заменить аксиому `partial_shrinkage_for_AC0` в
     `pnp3/Facts/Facts_Switching.lean` на теорему и обновить зависимые файлы.

5. **Общая проверка.**
   * Убедиться в отсутствии `sorry`, запустить `lake build` и сопутствующие
     тесты.
   * Обновить документацию (включая этот файл), отметив выполненные пункты.

## 3. Чек-лист завершения шага `d → d + 1`

### A. Конструирование глобальных хвостов

1. **Сырые селекторы.**
   * **Файл:** `MultiSwitching/SelectorPool.lean`.
   * Определить `rawCombinedTailSelectors β` как конкатенацию селекторов всех
     пакетов, для которых соответствующая CNF принадлежит листу оси `β`.
     Использовать имеющиеся функции `leafSelectorPool`,
     `leafSelectorAssignments`, `selectorPackage`.
   * Добавить леммы `mem_raw_of_mem_combined` и `exists_pkg_mem_raw`, позволяющие
     по селектору из `rawCombinedTailSelectors β` восстановить пакет и ссылку на
     локальный хвостовой сертификат.

2. **Дизъюнктная нормализация.**
   * **Предлагаемый файл:** новый модуль `MultiSwitching/SelectorRefinement.lean`
     (либо отдельный раздел в `SelectorPool`).
   * Реализовать функцию `refineDisjoint β : List (Subcube n) → List (Subcube n)`
     с доказательствами:
       - `pairwise_disjoint_refine` (листья попарно несовместны);
       - `cover_of_refine` (объединение равно исходному списку);
       - `subset_of_mem_refine` (каждый элемент списка лежит в `β`);
       - `length_refine_le` (оценка количества листьев через размер поддержки).
   * Для контроля бюджета глубины использовать уже доказанные оценки длин
     списков `selectorTailAssignments` и мощностей `leafSelectorTailSupport`.

3. **Построение PDT.**
   * **Файл:** `MultiSwitching/Core.lean` (рядом с существующими
     конструкторами `AxisWitness.toPartialCertificate...`).
   * Определить
     ```lean
     def globalTail (β : AxisLeaf axis) : PDT n :=
       PDT.ofDisjointLeaves (refineDisjoint β (rawCombinedTailSelectors β))
     ```
     и реализовать вспомогательную функцию `PDT.ofDisjointLeaves`, которая по
     дизъюнктному списку подкубов строит дерево решений с указанными листьями.
   * Доказать леммы:
       - `leaves_globalTail_eq_refine` (листья дерева совпадают с
         нормализованным списком);
       - `selector_mem_globalTail` (любой комбинированный селектор — лист);
       - `depth_globalTail_le` (глубина хвоста ≤ `τ + ⌈log₂ kβ⌉`, где
         `kβ = length (refineDisjoint β …)`).
     Здесь `τ` — исходный бюджет глубины хвостов, а надбавка контролируется
     леммой `length_selectorTailAssignments_le_leafSelectorSupport`.

4. **Контроль ошибки.**
   * Показать, что `errU` от `globalTail β` не превосходит `totalBadBound`.
     Для этого использовать: аддитивность `errU` по дизъюнктным подкубам,
     леммы `CombinedTailCertificate.pkg_epsilon_le` и существующие оценки
     `totalBadBound`.

### B. Упаковка глобальных хвостов

1. **Расширение структуры.**
   * В `MultiSwitching/Core.lean` определить
     ```lean
     structure CombinedTailCertificate :=
     { axis        : Axis n
     , tails       : ∀ β, globalTail β
     , epsilon     : ℝ
     , selectors_mem_global : ...
     , depth_global         : ...
     , err_bound            : ... }
     ```
     Использовать леммы из пункта A для заполнения свойств.

2. **Конструктор `chooseCombinedTailCertificate`.**
   * Собрать структуру на основе данных пакетов глубины 1, оси и новой функции
     `globalTail`. Убедиться, что старые поля (ось, `CombinedAxisWitness`)
     остаются без изменений.

### C. Функция `Depth1WitnessInput.build`

1. На основе `CombinedTailCertificate` построить `AxisTailSystem.TailCertificate`.
   * Использовать `globalTail β` в качестве хвостов и свойства `selectors_mem`,
     `depth_global`, `err_bound` для заполнения полей.

2. Вывести вспомогательные леммы:
   * `Depth1WitnessInput.build_selectors`
   * `Depth1WitnessInput.build_err`
   * `Depth1WitnessInput.build_depth`
   Эти утверждения обеспечат совместимость с конструкторами
   `partialCertificateWithinBudget` и `AxisWitness.toShrinkage`.

### D. Завершение индуктивного шага и демонтаж аксиомы

1. Реализовать основной переход `partialCertificateStep : d → d + 1` в
   `MultiSwitching/Core.lean`, используя `Depth1WitnessInput.build`.
2. Подставить полученный сертификат в `AxisWitness.toShrinkage` и убедиться, что
   условия SAL выполняются.
3. В `pnp3/Facts/Facts_Switching.lean` заменить аксиому
   `partial_shrinkage_for_AC0` на теорему, перестроить зависимые доказательства.
4. Запустить `lake build` и убедиться, что все модули компилируются без `sorry`.

### E. Финальная проверка

1. Перечитать комментарии в новых модулях (`SelectorRefinement`, `Core`) и
   убедиться, что они описывают назначения функций.
2. Обновить документацию (включая этот файл), отметив выполненные пункты.
3. Зафиксировать результаты сборки (`lake build`) в сопроводительном сообщении.

---

Следуя этому плану, можно поэтапно завершить многослойную часть доказательства
и перейти к демонтажу аксиомы `partial_shrinkage_for_AC0`. Если вы закрыли один
из пунктов, обязательно отметьте это здесь и добавьте ссылку на соответствующий
коммит/PR, чтобы следующему разработчику было проще отслеживать прогресс.
