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
      ✅ Получена оценка длины: см. `refineDisjoint_length_le_support`.
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
  * ✅ Подготовлена вспомогательная лемма
    `TailAssignmentBundle.mem_leaves_toPDT` (файл
    `MultiSwitching/SelectorPool.lean`), показывающая, что дерево,
    построенное по хвостовым присваиваниям конкретного селектора,
    действительно содержит этот селектор среди листьев.  Дополнительно
    `mem_leafSelectorTailBundles_leaves` связывает эту лемму с
    объединённым списком `leafSelectorTailBundles`, устраняя ручную
    распаковку `List.map`.
  * ✅ Получена оценка глубины для деревьев из
    `leafSelectorTailBundles`: `leafSelectorTailBundles_depth_le_support`
    (там же) показывает, что глубина каждого такого хвоста не превосходит
    мощности глобальной поддержки `leafSelectorSupport`.  Это связывает
    локальные списки присваиваний с общим бюджетом координат и готовит
    почву для контроля глубины будущего `globalTail` без обращения к
    конкретным пакетам глубины 1.
  * ✅ В `Core/BooleanBasics.lean` введён общий инструмент
    `Subcube.refineByCoords`, рекурсивно разбивающий подкуб по списку
    координат и восстанавливающий соответствующие присваивания
    (`mem_refineByCoords_assignMany`).  На стороне
    `SelectorPool.lean` добавлена упаковка `leafSelectorTailSupportList`
    вместе с леммой `refineBySupport_assignMany`, позволяющей напрямую
    применять общую конструкцию к глобальной поддержке хвостов.  Это
    закрывает подготовительный этап для алгоритма `refineDisjoint` и
    фиксирует список координат без повторов, вдоль которых потребуется
    нормализовать селекторы.
  * ✅ В `Core/PDT.lean` реализована функция `Subcube.refineByCoordsPDT`,
    строящая PDT по списку координат с теми же листьями, что и
    `refineByCoords`.  Дополнительно доказано ограничение глубины
    `Subcube.depth_refineByCoordsPDT_le`, связывающее глубину такого дерева
    с длиной списка координат.  Эти леммы позволят напрямую получать
    нормализованные хвосты, не прибегая к ручной реконструкции дерева
    решений из списка подкубов.
  * ✅ В `Core/BooleanBasics.lean` закрыта лемма `assign_eq_some_value`,
    разворачивающая успешный вызов `Subcube.assign` в утверждение о значении
    нужной координаты.  Эта деталь позволяет напрямую поднимать сведения об
    отдельных присваиваниях в рассуждениях про `TailAssignmentBundle`.
  * ✅ Для `TailAssignmentBundle.popHead` добавлена лемма `tail_coord_ne_head`
    (файл `SelectorPool.lean`), гарантирующая, что после отделения головы
    никакая пара из хвоста не использует исходную координату.  Свойство
    пригодится при конструировании дизъюнктных списков и контроле поддержки
    глобальных хвостов.
  * ✅ В `SelectorPool.lean` введено обозначение `rawCombinedTailSelectors`
    вместе с леммами `mem_rawCombinedTailSelectors_of_mem_combined` и
    `exists_pkg_mem_of_mem_rawCombinedTailSelectors`.  Они зафиксируют «сырой»
    список селекторов для листа `β` и позволяют напрямую восстанавливать пакет
    глубины 1, породивший конкретный селектор, не раскрывая `List.bind` вручную.
  * ✅ Опоры `leafSelectorTailSupport` и `leafSelectorTailSupportList` теперь
    параметризованы лишь осью `A`, без обращения к полной структуре
    `CombinedTailCertificate`.  Это позволяет строить хвостовые разбиения на
    уровне `CombinedAxisWitness` и упростит дальнейшее использование тех же
    списков в конструкциях «глобального хвоста».
  * ✅ В `SelectorPool.lean` появилась вспомогательная лемма
    `TailAssignmentBundle.exists_assignments_of_leafSelector`, которая выдаёт
    список присваиваний из глобальной хвостовой поддержки для любого селектора
    листа.  Лемма сохраняет информацию о том, что полученные координаты
    действительно лежат в `leafSelectorTailSupport`, каждое присваивание
    работает только по свободной координате `β`, и фиксирует равенство
    `Subcube.assignMany β updates = some γ`.  Это готовый строительный блок для
    включения селекторов в `refineByCoords` и последующей увязки с деревом
    `globalTail`.  ✅ Лемма обобщена: она зависит только от выбранной оси `A`,
    так что извлечение присваиваний теперь возможно ещё до построения
    комбинированного сертификата `CombinedTailCertificate`.
  * ✅ В `Core/BooleanBasics.lean` добавлены леммы
    `assign_bind_swap_of_none` и `assignMany_swap_head`, показывающие, что
    последовательные присваивания по различным свободным координатам можно
    переставлять без изменения результата.  Этот инструмент позволит
    нормализовать порядок применения `assignMany` в соответствии со списками
    поддержки и тем самым встраивать хвостовые присваивания селекторов в общий
    вызов `refineByCoords`.
  * ✅ Поверх этого в `SelectorPool.lean` появилась лемма
    `assignMany_selectorTailAssignments_cons_erase`: она формализует перенос
    выбранной пары `(i, b)` из списка `selectorTailAssignments β γ` в голову,
    используя `List.erase` и вновь доказанную коммутативность `assignMany`.
    Совместно с вспомогательной формулой
    `selectorTailAssignments_erase_eq_concat` это даёт готовый механизм
    пошагово выравнивать хвостовые присваивания под порядок координат из
    `leafSelectorTailSupportList`, что требуется перед окончательным
    связыванием селекторов с `refineByCoords`.
  * ✅ Добавлены равенства
    `length selectorTailAssignmentsOrdered = length selectorTailAssignments`
    (при покрытии локальной поддержки) и
    `length selectorTailAssignmentsOrdered = card selectorTailSupport`.
    Использование `List.toFinset` позволяет напрямую переносить подсчёты числа
    хвостовых координат на канонический порядок
    `leafSelectorTailSupportList`, не обращаясь заново к «сырому» списку
    присваиваний.
  * ✅ Дополнительно установлено равенство
    `length selectorTailAssignments = card selectorTailSupport`.  Это формально
    фиксирует, что хвостовой список присваиваний покрывает каждую координату
    поддержки ровно один раз и подготовит переход к работе с точными порядками
    координат при построении `refineDisjoint`.
  * ⏳ Построена вспомогательная функция
    `selectorTailAssignmentsOrdered coords β γ`, которая разворачивает список
    присваиваний `γ` в порядке произвольного списка координат `coords`.  Мы
    доказали, что при включении поддержек этот упорядоченный список содержит те
    же элементы и остаётся без повторов.  Следующий шаг — показать, что при
    выборе `coords = leafSelectorTailSupportList` получаем каноническую форму
    хвостов, пригодную для прямой подстановки в `refineByCoords` и сравнения с
    `globalTailCandidate`.
  * ✅ Закреплены дополнительные свойства упорядоченных хвостов:
    `selectorTailAssignmentsOrdered_coord_mem` и
    `selectorTailAssignmentsOrdered_coord_free` показывают, что каждая пара в
    нормализованном списке действительно использует координаты из
    `coords.toFinset` и работает по свободным координатам `β`, а
    `selectorTailAssignmentsOrdered_pairwise_coords` превращает эти факты в
    попарную независимость координат.  Наконец,
    `selectorTailAssignmentsOrdered_mem_iff` фиксирует, что при покрытии
    поддержки списки `selectorTailAssignments` и
    `selectorTailAssignmentsOrdered` совпадают по множеству элементов.  Эти
    леммы готовят непосредственное применение `assignMany` и связывают
    упорядоченные хвосты с `refineByCoords` без ручного анализа фильтраций.
  * ✅ Для стабильности упорядоченных хвостов добавлены леммы
    `selectorTailAssignmentsOrdered_update_eq`,
    `selectorTailSupport_mem_update_iff` и
    `selectorTailValue_update_eq`.  Они позволяют безопасно заменять базовый
    подкуб `β` на его обновление по координате `i`: если `i` отсутствует в
    списке `coords`, то упорядоченный список присваиваний не меняется, а
    значения `selectorTailValue` и факты о поддержке автоматически
    переносятся.  Это избавляет от ручного разбора `filterMap` при индукции по
    `assignMany`.
  * ✅ Показано, что упорядоченный список `selectorTailAssignmentsOrdered`
    восстанавливает исходный селектор: лемма
    `assignMany_selectorTailAssignmentsOrdered` доказывает, что при покрытии
    поддержки и отсутствии повторов достаточно последовательно применить
    хвостовые присваивания в порядке `coords`, чтобы получить `γ` из ствола
    `β`.  Это ключевой строительный блок для включения селекторов в
    `Core.Subcube.refineByCoords` и, в перспективе, в `globalTailCandidate`.
  * ✅ Следующий шаг закреплён леммой
    `selectorTailAssignmentsOrdered_mem_refineByCoords`: если глобальный список
    координат совпадает с локальной поддержкой селектора, то `γ` лежит в
    `Core.Subcube.refineByCoords β coords`.  Доказательство по индукции по
    списку `coords` аккуратно согласует рекурсию `refineByCoords` с порядком
    `selectorTailAssignmentsOrdered`.  Теперь достаточно показать, что
    `leafSelectorTailSupportList` действительно описывает поддержку каждого
    селектора, чтобы перенести результат на глобальный хвост.  В этом
    направлении добавлены промежуточные леммы
    `leafSelector_mem_refineByCoords_of_support_eq` и
    `leafSelector_mem_refineDisjoint_of_support_eq`: они показывают, что как
    только доказано равенство поддержек, соответствующий селектор автоматически
    попадает в `Core.Subcube.refineByCoords` и `refineDisjoint`, а значит будет
    листом канонического дерева `globalTailCandidate`.  Осталось добыть самое
    равенство поддержек, после чего линейка включений заработает «из коробки».
    ⚠️ Здесь возникло узкое место: все текущие леммы дают лишь включение
    `selectorTailSupport ⊆ leafSelectorTailSupport`, но не обратное.  Требуется
    дополнительный математический факт (скорее всего, следствие пакетного
    сертификата), который бы гарантировал, что каждый `γ ∈ leafSelectorSet`
    действительно фиксирует каждую координату из объединённой поддержки.
    Без этого шага продвижение к `selectors_mem_global` заблокировано.
  * ✅ Лемма `exists_refineDisjoint_subset_leafSelector` сопоставляет каждому
    селектору из `leafSelectorSet` конкретный элемент списка `refineDisjoint`,
    лежащий внутри него.  Вслед за этим вынесены осезависимые версии функций:
    определены `axisRefineDisjoint` и `axisGlobalTailCandidate`, а старая
    реализация `refineDisjoint`/`globalTailCandidate` теперь лишь подставляет
    `C.witness.axis`.  Благодаря этому хвостовые PDT можно строить сразу по оси,
    ещё до появления `CombinedTailCertificate`, и дальнейшая работа сводится к
    анализу поддержки и доказательству `selectors_mem_global` для уже готового
    канонического дерева.
  * ✅ В `Core/BooleanBasics.lean` введено отношение включения подкубов
    `Subcube.subset` и доказаны вспомогательные свойства (`subset_of_assign`,
    `subset_of_assignMany`, `subset_of_mem_refineByCoords`), позволяющие без
    раскрытия определений переносить принадлежность точек вдоль цепочек
    присваиваний.
  * ✅ `refineDisjoint` вынесен на уровень оси: определены
    `axisRefineDisjoint` и «старый» `refineDisjoint` теперь всего лишь подставляет
    `C.witness.axis`.  Для осевой версии доказаны базовые свойства —
    `axisRefineDisjoint_cover`, `axisRefineDisjoint_pairwise_disjoint`,
    `axisRefineDisjoint_subset_leaf`,
    `exists_selector_of_mem_axisRefineDisjoint` и
    `axisRefineDisjoint_length_le_support`.  Леммы
    `mem_axisRefineDisjoint`, `axisRefineDisjoint_cover` и
    `exists_axisRefineDisjoint_subset_leafSelector` показывают, что любая точка
    и любой селектор листа находятся в каноническом списке без раскрытия
    сертификата.  Благодаря этому дизъюнктная нормализация теперь полностью
    доступна на уровне оси `A`, а `CombinedTailCertificate` использует лишь
    простые обёртки (`refineDisjoint_pairwise_disjoint` и т. д.).
  * ✅ Связали осевой список `axisRefineDisjoint` с деревом
    `Core.Subcube.refineByCoordsPDT`: добавлены леммы
    `mem_axisRefineDisjoint_leaves_refineByCoordsPDT` и
    `axisRefineDisjoint_leaves_axisGlobalTailCandidate`, а также оценка глубины
    `depth_axisGlobalTailCandidate_le`.  Из них автоматически следуют обёртки
    для `refineDisjoint` и `globalTailCandidate`.  Теперь любое ветвление по
    `leafSelectorTailSupportList` сразу даёт PDT с контролируемой глубиной и
    гарантированными листьями без предварительного построения комбинированного
    сертификата.
  * ✅ Построены мосты от исходных селекторов к глобальному списку:
    леммы `exists_axisGlobalTailSelector_subset_of_mem_combined` и
    `exists_globalTailSelector_subset_of_mem_combined` нормализуют любой
    элемент `combinedTailSelectors` до подкуба из
    `axisGlobalTailSelectors`/`globalTailSelectors`, сохраняя вложение в
    исходный селектор.  Дальнейший шаг — автоматизировать предпосылку
    `β ⊆ γ` через свойства пакетного хвостового сертификата, после чего
    полученные подкубы сразу станут листьями канонического PDT.

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
