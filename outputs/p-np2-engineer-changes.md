# Исследование изменений инженера в `~/p-np2`

Дата: 2026-03-26

## Короткий вывод

Инженер не просто «починил сборку». По факту он сделал три содержательных шага:

1. **Убрал временный counting-adapter `hSlackToHalf` из build-critical пути.**
   Теперь Shannon-counting умеет напрямую потреблять slack-неравенство вида
   `circuitCountBound < 2^(tableLen - |S|)`.
2. **Добавил новый consumer-side интерфейс на semantic value coordinates и valid/promise inputs.**
   То есть нижняя часть противоречия теперь умеет работать не на `mask ++ values`, а на более содержательном интерфейсе: только value-биты, только valid encodings, только promise YES/NO.
3. **Довёл документацию и `FinalResult` до честной формулировки остаточного blocker’а.**
   Старый stable-restriction / invariant-provider путь теперь явно помечен как **более сильный fallback**, а не как «единственный честный последний шаг».

Но главный theorem-level gap действительно остался:

> в репозитории **нет мостика** от существующих source-side DAG packages, которые живут на encoded coordinates (`mask ++ values`), к новому promise/value locality interface.

Это я подтверждаю по типам и по текущим bridge-теоремам.

---

## Что именно изменилось

### 1. Shannon counting стал прямым по slack

В `pnp3/Counting/ShannonCounting.lean` добавлена новая основная теорема:

- `exists_hard_function_with_constraints_of_countingSlack`

Она принимает сразу

```lean
circuitCountBound p.n (p.sNO - 1) < 2 ^ (Partial.tableLen p.n - constrained.card)
```

и больше не требует промежуточного перехода через условие вида
`constrained.card ≤ tableLen / 2`.

Старый theorem `exists_hard_function_with_constraints` оставлен как wrapper поверх нового прямого theorem.

### 2. В lower-bound consumer добавлен promise/value слой

В `pnp3/LowerBounds/MCSPGapLocality.lean` появились новые определения и теоремы:

- `ValueCoordinateSet`
- `AgreeOnValues`
- `ValidEncoding`
- `exists_yes_no_agreeing_on_values_of_countingSlack`
- `no_value_local_function_solves_mcsp_of_countingSlack`

Смысл: противоречие теперь можно замыкать через локальность только по semantic truth-table value bits, а не по произвольным координатам encoded input.

Это существенное улучшение API: оно ближе к математическому содержанию counting-аргумента.

### 3. В asymptotic DAG barrier добавлен новый Layer-B интерфейс

В `pnp3/LowerBounds/AsymptoticDAGBarrier.lean` добавлены:

- `SmallDAGImpliesPromiseValueLocalityAt`
- `SmallDAGImpliesPromiseValueLocalityStatement`
- `no_dag_solver_of_promise_value_locality_at`

То есть Layer B теперь умеет говорить:

- о **small DAG solvers**,
- на **promise domain**,
- для **valid encodings**,
- с agreement только на **value coordinates**.

Это хорошо согласовано с новым consumer в `MCSPGapLocality.lean`.

### 4. `FinalResult.lean` и docs честно переописаны

В `pnp3/Magnification/FinalResult.lean` явно записано, что:

- `P_ne_NP_final` всё ещё условен на внешнем `hNPDag : NP_not_subset_PpolyDAG`;
- stable-restriction / certificate-provider / invariant-provider route — это **скомпилированные более сильные sufficient routes**;
- roadmap хочет перейти к **более слабому one-sided promise/value endpoint**, но он пока ещё не доведён до final surface.

`STATUS.md`, `TODO.md`, `pnp3/Docs/AsymptoticDAGBarrier_Status.md` синхронизированы с этой историей.

---

## Что я проверил руками

### Сборка

Я запустил:

- `lake build pnp3/Counting/ShannonCounting.lean pnp3/LowerBounds/MCSPGapLocality.lean pnp3/LowerBounds/AsymptoticDAGBarrier.lean`
- `lake build pnp3/Magnification/FinalResult.lean`

Оба запуска прошли успешно.

Наблюдение: предупреждения действительно остались, но они не связаны напрямую с этими правками; среди них есть упомянутые warnings в `pnp3/Models/PartialTruthTable.lean`.

### Неподключённый файл

Есть ещё **untracked** файл:

- `pnp3/Magnification/AsymptoticDAGCollapse.lean`

Он не входит в tracked diff и не импортируется из build graph, но локально типчекается через:

- `lake env lean pnp3/Magnification/AsymptoticDAGCollapse.lean`

Это похоже на заготовку для асимптотического DAG-моста, но пока не на интегрированную часть репозитория.

---

## Где именно остался blocker

### Текущее сильное source-side API

Существующие DAG-source packages живут в `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`, например:

- `DAGStableRestrictionInvariantPackage`
- `DAGStableRestrictionSlackPackageAt`
- bridge `smallDAGLocalityStatement_of_dagSlackPackageAtProvider`

Их форма принципиально такая:

- есть restriction `r` на **полных encoded coordinates** длины `partialInputLen p`;
- есть locality/invariance по `r.alive`, то есть на подмножестве координат **всего encoded input**;
- downstream bridge выводит **coordinate-locality** на encoded coordinates.

### Новый слабый consumer-side API

Новый путь хочет вместо этого получить:

- множество `S : Finset (Fin tableLen)` из **value coordinates**;
- agreement только по `Partial.valPart`;
- только для `ValidEncoding p x` и `ValidEncoding p y`;
- только для `x ∈ Yes`, `y ∈ No` на promise domain.

### Почему прямого моста сейчас нет

По текущим типам старый пакет не несёт как минимум следующих данных:

1. **проекция alive-set с encoded coordinates на чистые value coordinates**;
2. гарантию, что существенная часть locality вообще сидит на `Layer B value coords`, а не на mask coords;
3. специальную one-sided/promise-valid форму, нужную новому consumer’у;
4. выбранный YES-center / completion semantics, если идти к формулировке типа `YesSubcubeCertificate`.

Иначе говоря: старый пакет сильнее в одном смысле (глобальная encoded-coordinate locality), но **не в правильной форме** для нового API.

Из этого следует, что инженерский blocker описан корректно: проблема уже не техническая сборочная, а содержательная архитектурная.

---

## Моя оценка двух вариантов

Инженер сформулировал развилку:

1. выводить новый promise/value interface из текущих encoded-coordinate package’ов;
2. вводить новый source-side package сразу на value coordinates и promise-valid inputs.

### Вариант A: строить bridge из старого encoded-coordinate API

**Плюсы**

- меньше немедленной переделки существующего DAG-side кода;
- можно сохранить уже написанные invariant/slack packages как upstream source.

**Минусы**

- типовой разрыв здесь не косметический, а структурный;
- старый API квантифицирует по всем encoded inputs и agreement на `r.alive`, а новый — по valid/promise inputs и value-only agreement;
- bridge, вероятно, потребует дополнительных полей, которые по сути и будут новым source-side package в замаскированном виде;
- есть риск потратить время на сложный adapter, который сохранит не тот invariant, который реально нужен theorem-minimal route.

### Вариант B: сразу вводить новый source-side package на value/promise уровне

**Плюсы**

- лучше совпадает с уже написанным consumer-side API;
- форма ближе к реальному contradiction pattern: valid completions, YES/NO promise witnesses, value-coordinate slack;
- легче сделать theorem-minimal endpoint честным и явным;
- старые stable-restriction пакеты можно оставить как stronger fallback и, если получится, потом уже доказать bridge **из них в новый package**, а не наоборот.

**Минусы**

- придётся определить новый source contract и, возможно, переписать часть producer-side DAG analysis;
- часть существующих bridge-теорем на encoded coordinates станет второстепенной инфраструктурой.

### Мой вывод

**Я бы рекомендовал вариант B как основной путь**:

> вводить новый source-side package сразу на value coordinates и promise-valid inputs,
> а старые encoded-coordinate packages оставить как stronger optional route / fallback.

Причина: по текущему состоянию репозитория новый consumer-side слой уже существует и хорошо оформлен, а старые source-side объекты не дают нужный интерфейс «почти бесплатно». Попытка обязать их стать canonical bridge выглядит как борьба с формой старого API.

Более конкретно: если конечная цель — что-то уровня `YesSubcubeCertificate` / `PromiseValueLocalityCertificate`, то полезнее сразу потребовать от source-side анализа именно такие данные:

- центр в YES;
- value-coordinate set `S`;
- slack;
- one-sided acceptance stability на valid completions / promise-valid inputs.

Это гораздо ближе к тому, что реально потребляет новый theorem `no_value_local_function_solves_mcsp_of_countingSlack`.

---

## Что бы я сделал следующим шагом

### Минимальный честный следующий PR

1. **Завести новый source-side structure**, например:
   - `PromiseValueLocalityPackageAt`, или
   - `YesSubcubeCertificateAt`.
2. Поля делать сразу в терминах:
   - `p : GapPartialMCSPParams`
   - `S : Finset (Fin (Partial.tableLen p.n))`
   - `hSlack`
   - one-sided stability на valid encodings / promise-valid completions
3. Доказать bridge:
   - `PromiseValueLocalityPackageAt -> SmallDAGImpliesPromiseValueLocalityAt`
4. Потом уже протянуть это в:
   - asymptotic Layer B,
   - `NP_not_subset_PpolyDAG` wrappers,
   - и только затем в `FinalResult.lean`.

### Что делать со старым route

Старый encoded-coordinate route я бы **не удалял**. Его стоит оставить как:

- regression/audit surface;
- stronger sufficient condition;
- возможный источник partial bridge-лемм вида
  `encoded stable restriction -> promise/value certificate`, если позже окажется, что такой bridge легко закрывается для специальных случаев.

---

## Итоговая оценка прогресса

### Наблюдения

- counting-path стал чище и математически правильнее;
- новый promise/value consumer уже есть и компилируется;
- barrier layer теперь поддерживает этот интерфейс;
- docs и final wrappers стали честнее;
- главный незакрытый кусок действительно сместился в source-side theorem design.

### Инференция

Это **хороший инженерный прогресс**: он реально сократил accidental complexity и локализовал открытый математический вопрос.

### Но

До замыкания DAG-side separation ещё далеко: новый интерфейс на consumer side создан, но producer-side theorem, который его наполняет, пока отсутствует. Поэтому слова инженера о том, что дальше без выбора линии идти «вслепую», выглядят обоснованными.

---

## Sources

- `file:///root/p-np2/pnp3/Counting/ShannonCounting.lean`
- `file:///root/p-np2/pnp3/LowerBounds/MCSPGapLocality.lean`
- `file:///root/p-np2/pnp3/LowerBounds/AsymptoticDAGBarrier.lean`
- `file:///root/p-np2/pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
- `file:///root/p-np2/pnp3/Magnification/FinalResult.lean`
- `file:///root/p-np2/pnp3/Docs/AsymptoticDAGBarrier_Status.md`
- `file:///root/p-np2/STATUS.md`
- `file:///root/p-np2/TODO.md`
