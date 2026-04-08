# Handoff v2 (строгая версия):
# какие именно source-леммы действительно достаточны для замыкания маршрута до `NP_not_subset_PpolyDAG`

**Дата:** 2026-04-06  
**Проект:** `pnp3` (Lean 4)  
**Цель:** передать внешним математикам точный контракт, который можно формализовать и напрямую подключить к существующим wrappers без переархитектуры.

---

## 0) Главное в двух строках

1. Общий тезис «малый DAG + заметная YES-плотность ⇒ promise-YES-subcube» в абстрактном виде неверен (parity-обструкция).
2. Для закрытия текущего route нужен **family-specific** source-result: one-sided certificate isolation на **канонических slices**, с параметрами, совместимыми с downstream-предикатами.

---

## 1) Что уже готово в коде (можно считать стабильным API)

### 1.1 Packaging/quantifiers

В проекте уже есть packaging-теоремы:

- `eventual_promiseYesSubcube_of_smallDAG`,
- `eventual_promiseYesSubcube_of_smallDAG_onCanonicalSlices`.

Они закрывают кванторный переход из pointwise-формы в eventual-форму для weak-route.

### 1.2 Финальные wrappers

`Magnification/FinalResultWeakRoutes.lean` уже содержит bridge/class-level closure:

- из канонического source-debt в `¬ PpolyDAG bridge.L`,
- затем (при NP-свидетеле `bridge.L`) в `NP_not_subset_PpolyDAG`.

Дополнительно в `AsymptoticDAGBarrierTheorems.lean` теперь есть прямые
wrapper-теоремы для **eventual** promise-YES payload:

- `not_globalPpolyDAG_of_eventuallyPromiseYesWeakRoute`,
- `NP_not_subset_PpolyDAG_of_eventuallyPromiseYesWeakRoute`.

### 1.3 Целевые долги в интерфейсе

В `DAGStableRestrictionProducer.lean` уже заведены:

- `canonical_smallDAG_easyImage_source_on_slices`,
- `canonical_smallDAG_easyDensity_source_on_slices`,
- `canonical_smallDAG_witnessEasyDensity_source_on_slices`,
- `canonical_smallDAG_witnessUniformLower_source_on_slices`.

---

## 2) Почему нельзя доказывать слишком общий source-step

### 2.1 Parity-обструкция (концептуально)

Parity имеет:

1. очень малую DAG/branching-program реализацию,
2. YES-плотность `1/2`,
3. но любой нетривиальный axis-aligned subcube содержит обе чётности.

Следовательно, abstract-импликация без специальной структуры slices — ложная цель.

### 2.2 Практический вывод

Нужна не «универсальная» theorem schema, а точная source-лемма для фиксированного `F`/`bridge.L`.

---

## 3) Базовое определение, которое нужно внешней группе

Пусть на длине `n` канонический slice задаётся
`Y_n ⊆ S_n ⊆ {0,1}^n`.

Для частичного присваивания `ρ` обозначим

- `[ρ] := {x : x согласуется с ρ}`,
- `codim([ρ]) = |dom ρ|`.

Назовём `ρ` **one-sided isolating certificate**, если

- `S_n ∩ [ρ] ≠ ∅`,
- `S_n ∩ [ρ] ⊆ Y_n`.

---

## 4) Точная sufficient-лемма: версия A (codim/ambient-density)

Ниже формулировка, которая действительно достаточна, если downstream-предикат нормирует через codimension или ambient-density subcube.

### Теорема A (sufficient)

Пусть существует `c > 0`, `β* > 0` и функция `n1(β)` (для `0 < β < β*`) такие, что:

для любого `0 < β < β*`, любого `n ≥ n1(β)` и любого канонического slice-DAG `G`
размера `≤ B_F(n,β)` существует `ρ` с

1. `S_n ∩ [ρ] ≠ ∅`,
2. `S_n ∩ [ρ] ⊆ Y_n`,
3. `|dom ρ| ≤ c·β·n`.

Тогда для любого `ε ∈ (0,1)`, положив

`β0 := min(β*, ε/c)`,

получаем:

`∀ 0<β<β0, ∃ n0(β), ∀ n≥n0(β),` выполнено pointwise-утверждение
типа `SmallDAGImpliesPromiseYesSubcubeAt` на канонических slices в любом из стандартных смыслов:

- codimension bound `codim ≤ ε n`, или
- ambient-density bound `μ([ρ]) ≥ 2^{-ε n}`.

### Короткая проверка

Из `β < ε/c` и `|dom ρ| ≤ cβn` сразу `|dom ρ| < ε n`,
а значит и codim-bound, и `2^{-|dom ρ|} ≥ 2^{-ε n}`.

---

## 5) Точная sufficient-лемма: версия B (relative-density внутри slice)

Если downstream `easyDensity`/`PromiseYesSubcubeAt` использует не ambient-density,
а **relative-density на promise-domain**, например

`|S_n ∩ [ρ]| / |S_n| ≥ 2^{-ε n}`,

то Теоремы A недостаточно (потому что `S_n ∩ [ρ]` может быть непустым, но очень маленьким).

### Теорема B (усиленный контракт)

К условиям Теоремы A добавляем

`|S_n ∩ [ρ]| ≥ 2^{-dβn} |S_n|` для некоторого `d>0`.

Тогда при

`β0 := min(β*, ε/c, ε/d)`

получаем одновременно:

- codim/ambient-density bound,
- relative-density bound `|S_n∩[ρ]|/|S_n| ≥ 2^{-ε n}`.

---

## 6) Где именно включается length-local asymptotics (`n0(β)`)

Часто source-лемма доказывается для режима «размер DAG ≤ `2^{βn}`», а канонический bound полиномиален:

`B_F(n,β) ≤ n^k`.

Тогда нужен size-cutoff `n0_size(β)` из

`n^k ≤ 2^{β n}`.

Рабочий полностью явный выбор:

- `A(β) := max(16, 8k/β)`,
- `n0_size(β) := ceil(A(β)·log2 A(β))`.

И затем

`n0(β) := max(n1(β), n0_size(β))`.

Это и есть тот шаг, где применяется length-local bridge.

---

## 7) Existential extraction для вероятностных proof-скелетов

Если используется случайное `ρ` из конечного носителя и доказано, что
нужное событие имеет положительную вероятность, то существует конкретный `ρ`-свидетель.

Это обычный конечный вывод (`Pr[E] > 0` на конечном носителе ⇒ `∃ω: E(ω)`),
полностью совместимый с Lean-формализацией.

---

## 8) Какой final contract отправлять математикам

Просить в первую очередь не A/B/C по имени, а следующую helper-цель:

### `canonical_smallDAG_certificateIsolation_on_slices F`

Содержательно:

`∃ c>0, ∃ β*>0, ∀ 0<β<β*, ∃ n1(β), ∀ n≥n1(β), ∀ canonical G (size≤B_F(n,β)), ∃ ρ:`

- `S_n∩[ρ] ≠ ∅`,
- `S_n∩[ρ] ⊆ Y_n`,
- `|dom ρ| ≤ cβn`.

И дополнительно:

- если downstream требует relative-density — добавить пункт Теоремы B.

---

## 9) Lean mapping (что делать после получения proof-пакета)

1. Новый helper predicate/lemma:
   `canonical_smallDAG_certificateIsolation_on_slices`.
2. Из него вывести pointwise:
   `... -> SmallDAGImpliesPromiseYesSubcubeAt` (canonical bound).
3. Применить готовый packaging:
   `eventual_promiseYesSubcube_of_smallDAG_onCanonicalSlices`.
4. Применить готовые weak-route wrappers:
   до `¬ PpolyDAG bridge.L` и `NP_not_subset_PpolyDAG`.

---

## 10) Чеклист приёмки внешнего математического ответа

Пакет считаем достаточным, если в нём явно есть:

- [ ] non-vacuity: `S_n∩[ρ] ≠ ∅`,
- [ ] one-sided purity: `S_n∩[ρ] ⊆ Y_n`,
- [ ] explicit budget: `|dom ρ| ≤ cβn`,
- [ ] корректные кванторы по `β` и `n`,
- [ ] явный `n0(β)`/`n1(β)` и место size-cutoff,
- [ ] если нужен relative-density — отдельный bound типа Теоремы B,
- [ ] никакой новой аксиоматики и нефомализуемых «чёрных ящиков».

---

## 11) Граница утверждений

Этот документ не заявляет «абсолютное P ≠ NP» в общепринятой внешней постановке.
Он фиксирует, какой source-result нужен, чтобы закрыть текущий формальный endpoint
`NP_not_subset_PpolyDAG` в рамках архитектуры данного Lean-проекта.

---

## 12) TL;DR для пересылки

> Нужен family-specific результат: one-sided certificate isolation на канонических slices (с явным контролем `|domρ| = O(βn)` и, при необходимости, relative-density внутри `S_n`). После этого существующий pipeline уже готов и механически доводит до `¬ PpolyDAG bridge.L`, а затем до `NP_not_subset_PpolyDAG`.

---

## 13) Прямой ответ на практический вопрос: «этого достаточно для полного закрытия?»

Коротко: **да, почти всегда достаточно**, но только если вместе с source-пакетом
закрыты ещё четыре формальные предпосылки интеграции:

1. **Корректно зафиксированы `F` и `bridge`** (без смены модели/интерфейсов в процессе).
2. **Есть NP-свидетель для `bridge.L`** в той форме, которую ждут финальные wrappers.
3. **Согласована нормировка downstream-предиката**:
   - если codim/ambient-density — достаточно Теоремы A;
   - если relative-density внутри `S_n` — нужен усиленный вариант Теоремы B.
4. **В формализации нет новых аксиом/`sorry`**, и все промежуточные леммы из Lean mapping реально закрыты.

Если эти четыре пункта выполнены, то ответы из этого md-файла действительно
достаточны, чтобы дособрать endpoint `NP_not_subset_PpolyDAG` в текущем проекте.

---

## 14) Проверка присланного proof-core: witness-coordinate isolation

Ниже фиксируем статус присланного вами ядра доказательства
(`witness-coordinate certificate isolation`):

### 14.1 Что в нём корректно (математически)

Ваш аргумент корректно доказывает one-sided isolation **при условии** структуры:

- есть малый witness-блок координат `J`,
- membership в `Y_n` внутри `S_n` зависит только от `x|_J` через verifier `V_n(u, ·)`,
- есть принимающий шаблон `a*`,
- каждый шаблон реализуем в `S_n`.

Тогда выбор `ρ := a*` на `J` действительно сразу даёт:

- non-vacuity: `S_n ∩ [ρ] ≠ ∅`,
- purity: `S_n ∩ [ρ] ⊆ Y_n`,
- budget: `|dom ρ| = |J| ≤ cβn`.

И это ровно тот тип сертификата, который нужен для source-step в codim/ambient-density трактовке.

### 14.2 Что добавляется для relative-density

Вы правильно указали усиление: нужен uniform lower bound на fibers
`{x ∈ S_n : x|_J = a}`. Тогда relative-density bound следует автоматически
для выбранного `a*`.

### 14.3 Что ещё остаётся для «безусловного закрытия» в коде

Остаётся не логика редукции (она уже есть), а **доказательство самой структуры**
для конкретного `F/bridge.L`:

1. формализовать helper-структуру `witnessCoordinatePresentation` на канонических slices;
2. доказать, что канонический slice вашего `bridge.L` её удовлетворяет
   (и, при необходимости, fiber lower bound);
3. сделать bridge-лемму:
   `witnessCoordinatePresentation -> canonical_smallDAG_certificateIsolation_on_slices`;
4. подключить её в существующий downstream pipeline (без новых аксиом).

Итог: присланный proof-core — **содержательно достаточный условный шаблон**.
Для полного безусловного закрытия в Lean остаётся подтвердить, что эта структура
действительно верна для вашего фиксированного семейства slices.

---

## 15) FAQ — окончательный yes/no

**Вопрос:** «Если ответить на все вопросы из этого документа, можно ли закрыть доказательство безусловно?»
**Ответ:** **Да, можно**, если ответы действительно дают формальные доказательства всех пунктов из §13 и §14.3, и эти доказательства корректно перенесены в Lean без новых `axiom`/`sorry`.

То есть practically это эквивалентно:

1. источник (`source-step`) для вашего конкретного `F/bridge.L` реально доказан;
2. выбран правильный вариант нормировки (A или B);
3. есть NP-свидетель для `bridge.L`;
4. весь мост от source-step до `NP_not_subset_PpolyDAG` компилируется существующими wrappers.

---

## 16) Самодостаточность документа без чтения кода: честная оценка

Короткий ответ: **почти, но не полностью**.

Для математиков документ уже достаточен как roadmap/контракт, но если цель —
доказать всё «в отрыве от репозитория», то не хватает буквально точных
формальных определений некоторых Lean-предикатов и соглашений об их нормировке.

### 16.1 Что ещё нужно добавить, чтобы не смотреть в код вообще

Ниже минимальный список, который должен быть включён в handoff как «appendix of definitions»:

1. Полные сигнатуры и развёртки (на уровне логики первого порядка) для:
   - `GapSliceFamily` (что именно входят в `paramsOf`, `encodedLen`, `tableLen`),
   - `SmallDAGImpliesPromiseYesSubcubeAt`,
   - `canonicalWitnessEasyDensitySourceProviderOnSlices`,
   - `SmallDAGSolver`,
   - `AsymptoticDAGLanguageBridge`.
2. Явная фиксация нормировки для density-утверждений:
   - ambient measure на `{0,1}^n` или
   - relative measure внутри promise-domain `S_n`.
3. Точная форма NP-свидетеля, которую принимает финальный wrapper
   (`hNP : NP bridge.L` в текущем API).
4. Список already-proved bridge-лемм с их входами/выходами в виде «если дано X, то получаем Y» без ссылок на имена файлов.

### 16.2 Практический вывод

Если добавить этот appendix (1–4), то внешний математик действительно сможет
работать полностью автономно от кода и вернуть proof-package, который потом
механически переносится в Lean.
