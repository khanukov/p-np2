import Pnp3.ThirdPartyFacts.MultiSwitching.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice

namespace Pnp3
namespace ThirdPartyFacts
namespace MultiSwitching

open Core

/--
  «Пул» селекторов для фиксированного листа `β`: объединяем все значения,
  которые возвращает `combinedTailSelectors` при переборе функций из
  `flattenedCNFs`.  Такая заготовка пригодится при построении глобальных
  хвостов: достаточно показать, что любой конкретный селектор попадает в этот
  список.
-/
noncomputable def leafSelectorPool
    {n M τ w t : Nat}
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Subcube n) :=
  (flattenedCNFs (n := n) (M := M) (τ := τ) (w := w) (t := t) packages).bind
    (fun F =>
      combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        packages A hβ F.eval)

/--
  Нормализованное обозначение для «сырого» списка селекторов, появляющихся в
  объединённом хвосте на листе `β`.  Определение просто переназывает
  существующий `leafSelectorPool`, но подчёркивает, что мы пока не устраняем
  дубликаты и не выполняем дизъюнктную нормализацию.  В дальнейшем этот список
  будет входной точкой для алгоритма `refineDisjoint`.-/
noncomputable def rawCombinedTailSelectors
    {n M τ w t : Nat}
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Subcube n) :=
  leafSelectorPool (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ

/--
  Любой селектор, появившийся в значении `combinedTailSelectors`, автоматически
  входит в «сырой» список `rawCombinedTailSelectors`.  Формула повторяет
  предыдущий результат `mem_leafSelectorPool_of_mem_combined`, но записана через
  новое обозначение, чтобы дальнейшие доказательства могли ссылаться на неё
  без раскрытия определений.-/
lemma mem_rawCombinedTailSelectors_of_mem_combined
    {n M τ w t : Nat}
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily
        (Fs := flattenedCNFs (n := n) (M := M) (τ := τ) (w := w) (t := t)
          packages))
    {γ : Subcube n}
    (hγ : γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        packages A hβ f) :
    γ ∈ rawCombinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
  unfold rawCombinedTailSelectors
  exact CombinedTailCertificate.mem_leafSelectorPool_of_mem_combined
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := A) (β := β) hβ (f := f) hf (γ := γ) hγ

/--
  Элемент «сырого» списка селекторов всегда приходит из некоторого пакета
  глубины 1 и порождён конкретной формулой из `flattenedCNFs`.  Результат
  напрямую обобщает ранее доказанную лемму `exists_pkg_mem_of_mem_pool` и будет
  использоваться при связывании `rawCombinedTailSelectors` с хвостовыми
  сертификатами пакетов.-/
lemma exists_pkg_mem_of_mem_rawCombinedTailSelectors
    {n M τ w t : Nat}
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ rawCombinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    ∃ (pkg : Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))
      (hmem : pkg ∈ packages)
      (F : Core.CNF n w) (hF : F ∈ pkg.input.Fs),
        γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
          packages A hβ F.eval := by
  unfold rawCombinedTailSelectors at hγ
  exact exists_pkg_mem_of_mem_pool (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := A) (β := β) hβ (γ := γ) hγ

/--
  Версия «пула» селекторов без повторений.  Для дальнейшей нормализации
  достаточно знать множество подкубов, поэтому мы убираем дубликаты с помощью
  `List.dedup`.  Подразумевается, что `Subcube` имеет решаемое равенство — это
  обеспечивается инфраструктурой `BooleanBasics`.
-/
noncomputable def leafSelectorSet
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Subcube n) :=
  (leafSelectorPool (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).dedup

/--
  Финизированная версия объединённого набора селекторов.  Мы рассматриваем
  `leafSelectorSet` как подмножество подкубов без повторений и упаковываем его
  в `Finset`.  Такое представление удобно для подсчётов мощности и дальнейшей
  нормализации: можно ссылаться на стандартные леммы о конечных множествах
  вместо работы со списками вручную.
-/
noncomputable def leafSelectorFinset
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : Finset (Subcube n) :=
  ⟨leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ,
    by
      classical
      exact List.nodup_dedup _⟩

namespace CombinedTailCertificate

/--
  Если селектор `γ` появляется в значении `combinedTailSelectors` для функции
  `f`, то он автоматически принадлежит пулу `leafSelectorPool`.
-/
lemma mem_leafSelectorPool_of_mem_combined
    {n M τ w t : Nat}
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily
        (Fs := flattenedCNFs (n := n) (M := M) (τ := τ) (w := w) (t := t)
          packages))
    {γ : Subcube n}
    (hγ : γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        packages A hβ f) :
    γ ∈ leafSelectorPool (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
  classical
  unfold leafSelectorPool
  obtain ⟨pkg, hmem_pkg, F, hF, hf_eq⟩ :=
    (mem_cnfFamily_flattened_iff (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) (f := f)).mp hf
  have hflatten : F ∈ flattenedCNFs (n := n) (M := M) (τ := τ)
      (w := w) (t := t) packages :=
    (mem_flattenedCNFs_iff (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) (F := F)).mpr
      ⟨pkg, hmem_pkg, hF⟩
  refine List.mem_bind.2 ?_
  refine ⟨F, hflatten, ?_⟩
  have hf' : f = F.eval := by simpa [hf_eq]
  simpa [hf'] using hγ

/--
  Любой селектор, входящий в объединённый список, остаётся в списке после
  удаления повторений.
-/
lemma mem_leafSelectorSet_of_mem_pool
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorPool (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
  classical
  unfold leafSelectorSet
  exact List.mem_dedup.mpr hγ

/--
  Комбинация двух предыдущих лемм: селектор, появившийся у конкретной функции,
  сразу же входит в множество без дубликатов.
-/
lemma mem_leafSelectorSet_of_mem_combined
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily
        (Fs := flattenedCNFs (n := n) (M := M) (τ := τ) (w := w) (t := t)
          packages))
    {γ : Subcube n}
    (hγ : γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        packages A hβ f) :
    γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ :=
    mem_leafSelectorSet_of_mem_pool (n := n) (M := M) (τ := τ)
    (w := w) (t := t) (packages := packages) A hβ
      (CombinedTailCertificate.mem_leafSelectorPool_of_mem_combined
        (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) (A := A) (hβ := hβ) (hf := hf) (γ := γ) hγ)

/--
  Для последующего построения глобальных хвостов удобно иметь явный список,
  в котором каждому селектору сопоставляется последовательность фиксированных
  координат (`selectorAssignments`).  Мы переупаковываем `leafSelectorSet`
  в список пар `(γ, assignments)`.  Порядок элементов соответствует порядку
  в `leafSelectorSet`, так что при необходимости можно пользоваться уже
  доказанными свойствами, например отсутствием дубликатов после `dedup`.
-/
noncomputable def leafSelectorAssignments
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Subcube n × List (BitFix n)) :=
  (leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).map
    (fun γ => (γ, selectorAssignments (n := n) γ))

/--
  Специализированная версия `leafSelectorAssignments`, в которой вместо полного
  списка назначений используется отфильтрованный хвостовой список
  `selectorTailAssignments`.  Каждому селектору сопоставляем только те пары
  `(i, b)`, которые ещё не зафиксированы листом оси `β`.  Эта конструкция
  пригодится при построении глобального хвоста: именно по этому списку мы будем
  ветвиться после прохождения ствола.
-/
noncomputable def leafSelectorTailAssignments
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Subcube n × List (BitFix n)) :=
  (leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).map
    (fun γ => (γ, selectorTailAssignments (n := n) β γ))

/--
  Любая пара из `leafSelectorTailAssignments` сопоставляет селектору `γ` именно
  список `selectorTailAssignments β γ`.  Лемма полностью аналогична
  `mem_leafSelectorAssignments_elim`, но сразу работает с хвостовыми
  присваиваниями, что позволяет не возвращаться к фильтрации вручную.
-/
lemma mem_leafSelectorTailAssignments_elim
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorTailAssignments (n := n) (M := M)
        (τ := τ) (w := w) (t := t) (packages := packages) A hβ) :
    entry.2 = selectorTailAssignments (n := n) β entry.1 := by
  classical
  unfold leafSelectorTailAssignments at hentry
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hentry
  simp

/--
  Любая координата, появившаяся в поддержке `selectorTailSupport β γ`,
  автоматически принадлежит объединённой поддержке
  `leafSelectorTailSupport`.  Лемма позволяет сразу переходить от
  локальных сведений о селекторе к глобальным данным, с которыми будет
  строиться общий хвост. -/
lemma selectorTailSupport_subset_leafSelectorTailSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorTailAssignments (n := n) (M := M)
        (τ := τ) (w := w) (t := t) (packages := packages)
        A hβ) :
    selectorTailSupport (n := n) β entry.1
      ⊆ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ := by
  classical
  -- Распаковываем принадлежность из отображения `map`.
  unfold leafSelectorTailAssignments at hentry
  obtain ⟨γ, hγ_mem, rfl⟩ := List.mem_map.1 hentry
  -- `γ` лежит в исходном списке селекторов без повторений.
  have hγ_set : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ := hγ_mem
  -- Преобразуем принадлежность координаты из локальной поддержки
  -- через описанный выше finset.
  intro i hi
  have hpair : ∃ b : Bool, (i, b) ∈ selectorTailAssignments
      (n := n) β γ :=
    (mem_selectorTailSupport (β := β) (γ := γ) (i := i)).1 hi
  obtain ⟨b, hb⟩ := hpair
  -- Преобразуем принадлежность к глобальному списку через определение `map`.
  -- Используем определение глобальной поддержки: найдём требуемый селектор.
  refine (mem_leafSelectorTailSupport (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ).2 ?_
  refine ⟨γ, ?_, ?_⟩
  · -- Переход от списка без повторений к finset-версии.
    have hfin :=
      (mem_leafSelectorFinset
        (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ (γ := γ)).2 hγ_set
    simpa [leafSelectorFinset] using hfin
  · -- Конкретная координата берётся из хвостового списка назначений.
    unfold selectorTailSupport
    refine List.mem_toFinset.2 ?_
    refine ⟨i, ?_, rfl⟩
    exact List.mem_map.2 ⟨(i, b), hb, rfl⟩

/--
  Следствие предыдущей леммы: мощность локальной поддержки селектора
  не превосходит мощности глобальной хвостовой поддержки.  Это особенно
  полезно при оценке числа ветвлений, возникающих при склейке хвостов.
-/
lemma card_selectorTailSupport_le_leafSelectorTailSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorTailAssignments (n := n) (M := M)
        (τ := τ) (w := w) (t := t) (packages := packages)
        A hβ) :
    (selectorTailSupport (n := n) β entry.1).card ≤
      (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ).card := by
  classical
  refine Finset.card_le_of_subset ?_
  exact selectorTailSupport_subset_leafSelectorTailSupport
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ hentry

/--
  Для каждой записи из `leafSelectorTailAssignments` последовательное
  применение `Subcube.assignMany` к листу `β` восстанавливает исходный селектор
  `γ`.  Это прямое следствие леммы `assignMany_selectorTailAssignments`.
-/
lemma leafSelectorTailAssignments_assignMany
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorTailAssignments (n := n) (M := M)
        (τ := τ) (w := w) (t := t) (packages := packages) A hβ) :
    Subcube.assignMany β entry.2 = some entry.1 := by
  classical
  have hassign := mem_leafSelectorTailAssignments_elim
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := A) (β := β) hβ (entry := entry) hentry
  simpa [hassign]
    using assignMany_selectorTailAssignments (n := n) (β := β) (γ := entry.1)

/--
  Специализированный список присваиваний для хвоста относительно фиксированного
  листа `β`.  Мы фильтруем глобальные присваивания селектора, сохраняя только
  те координаты, которые ещё не зафиксированы в `β`.  Эти данные будут
  непосредственно использоваться при построении объединённого хвоста: именно
  по ним дерево решений должно ветвиться после прохождения ствола `β`.
-/
def selectorTailAssignments {n : Nat}
    (β γ : Subcube n) : List (BitFix n) :=
  (selectorAssignments (n := n) γ).filter fun pair => β pair.1 = none

/--
  Элемент входит в список `selectorTailAssignments β γ` тогда и только тогда,
  когда он появляется в глобальном списке присваиваний селектора и
  соответствующая координата не фиксирована в `β`.
-/
lemma mem_selectorTailAssignments {n : Nat} {β γ : Subcube n}
    {pair : BitFix n} :
    pair ∈ selectorTailAssignments (n := n) β γ ↔
      pair ∈ selectorAssignments (n := n) γ ∧ β pair.1 = none := by
  classical
  unfold selectorTailAssignments
  constructor
  · intro hmem
    have h := List.mem_filter.mp hmem
    exact ⟨h.1, h.2⟩
  · rintro ⟨hassign, hβ⟩
    exact List.mem_filter.mpr ⟨hassign, hβ⟩

/-- Любое «хвостовое» присваивание приходит из глобального списка селектора. -/
lemma selectorTailAssignments_subset_assignments {n : Nat}
    {β γ : Subcube n} {pair : BitFix n} :
    pair ∈ selectorTailAssignments (n := n) β γ →
      pair ∈ selectorAssignments (n := n) γ :=
  fun h => (mem_selectorTailAssignments (β := β) (γ := γ) (pair := pair)).1 h |>.1

/--
  Поддержка «хвостовых» присваиваний: множество индексов, которые действительно
  фиксируются в списке `selectorTailAssignments β γ`.  Реализовано через
  преобразование списка пар `(i, b)` в конечное множество индексов `i`.
-/
noncomputable def selectorTailSupport {n : Nat}
    (β γ : Subcube n) [DecidableEq (Fin n)] : Finset (Fin n) :=
  (((selectorTailAssignments (n := n) β γ).map fun pair => pair.1).toFinset)

/--
  Координата входит в поддержку `selectorTailSupport β γ` тогда и только тогда,
  когда в списке `selectorTailAssignments β γ` присутствует соответствующее
  присваивание.  Лемма позволяет без лишних преобразований переходить от
  конечного множества к исходному списку.
-/
lemma mem_selectorTailSupport {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} {i : Fin n} :
    i ∈ selectorTailSupport (n := n) β γ
      ↔ ∃ b : Bool, (i, b) ∈ selectorTailAssignments (n := n) β γ := by
  classical
  unfold selectorTailSupport
  constructor
  · intro hmem
    obtain ⟨value, hvalue_mem, hvalue_eq⟩ := List.mem_toFinset.1 hmem
    obtain ⟨pair, hpair_mem, rfl⟩ := List.mem_map.1 hvalue_mem
    refine ⟨pair.2, ?_⟩
    have hpair : (pair.1, pair.2) ∈ selectorTailAssignments (n := n) β γ := by
      simpa using hpair_mem
    simpa [hvalue_eq] using hpair
  · rintro ⟨b, hb⟩
    refine List.mem_toFinset.2 ?_
    refine ⟨i, ?_, rfl⟩
    apply List.mem_map.2
    exact ⟨(i, b), hb, rfl⟩

/-- Поддержка хвостовых присваиваний является подмножеством полной поддержки селектора. -/
lemma selectorTailSupport_subset_support {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} :
    selectorTailSupport (n := n) β γ
      ⊆ selectorSupport (n := n) γ := by
  classical
  intro i hi
  obtain ⟨b, hb⟩ := (mem_selectorTailSupport (β := β) (γ := γ) (i := i)).1 hi
  have hassign := selectorTailAssignments_subset_assignments
      (β := β) (γ := γ) (pair := (i, b)) hb
  have hmem : γ i = some b :=
    (mem_selectorAssignments (n := n) (γ := γ) (pair := (i, b))).1 hassign
  exact (mem_selectorSupport (n := n) (γ := γ) (i := i)).2 ⟨b, hmem⟩

/--
  Для каждого индекса в поддержке хвостовых присваиваний существует единственное
  значение `b`, которое встречается в списке `selectorTailAssignments β γ`.
  Мы фиксируем это значение через `Classical.choose`, чтобы в дальнейшем не
  искать его заново при разборе списков. -/
noncomputable def selectorTailValue
    {n : Nat} [DecidableEq (Fin n)]
    (β γ : Subcube n) (i : Fin n)
    (hmem : i ∈ selectorTailSupport (n := n) β γ) : Bool :=
  Classical.choose
    ((mem_selectorTailSupport (n := n) (β := β) (γ := γ) (i := i)).1 hmem)

/--
  Из определения `selectorTailValue` сразу следует, что соответствующая пара
  `(i, selectorTailValue β γ i hmem)` действительно присутствует в списке
  `selectorTailAssignments β γ`.  Это равенство часто используется при явном
  удалении данной пары из списка. -/
lemma selectorTailValue_mem
    {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} {i : Fin n}
    (hmem : i ∈ selectorTailSupport (n := n) β γ) :
    (i, selectorTailValue (n := n) (β := β) (γ := γ) i hmem)
        ∈ selectorTailAssignments (n := n) β γ := by
  classical
  have h :=
    (mem_selectorTailSupport (n := n) (β := β) (γ := γ) (i := i)).1 hmem
  exact (Classical.choose_spec h)

/--
  Удобное разложение списка `selectorTailAssignments β γ`: если пара
  `(i, b)` входит в список, то её можно выделить как отдельный элемент,
  записав исходный список в виде `prefix ++ (i, b) :: suffix`.  Эта лемма
  систематически применяется при рекурсивном построении глобальных хвостов.
-/
lemma selectorTailAssignments_split
    {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} {i : Fin n} {b : Bool}
    (hmem : (i, b) ∈ selectorTailAssignments (n := n) β γ) :
    ∃ prefix suffix,
      selectorTailAssignments (n := n) β γ
        = prefix ++ (i, b) :: suffix := by
  classical
  obtain ⟨prefix, suffix, hsplit⟩ := List.mem_split hmem
  exact ⟨prefix, suffix, hsplit⟩

/--
  Если мы удаляем из `selectorTailAssignments β γ` пару, соответствующую
  индексу `i` из поддержки, то длина списка уменьшается ровно на единицу.
  Лемма применяет предыдущий результат о разложении списка. -/
lemma length_selectorTailAssignments_remove
    {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} {i : Fin n}
    (hmem : i ∈ selectorTailSupport (n := n) β γ) :
    (selectorTailAssignments (n := n) β γ).erase
          (i, selectorTailValue (n := n) (β := β) (γ := γ) i hmem)).length
      = (selectorTailAssignments (n := n) β γ).length - 1 := by
  classical
  set pair := (i, selectorTailValue (n := n) (β := β) (γ := γ) i hmem) with hpair
  have hpair_mem : pair ∈ selectorTailAssignments (n := n) β γ := by
    simpa [pair, hpair] using selectorTailValue_mem (β := β) (γ := γ)
      (i := i) (hmem := hmem)
  simpa [pair, hpair]
    using List.length_erase_of_mem hpair_mem

/--
  Обобщённая версия предыдущей оценки: вместо равенства используем неравенство
  в «удобном» направлении.  В дальнейшем мы будем часто применять именно её,
  поскольку она избавляет от явного раскрытия обозначений. -/
lemma length_selectorTailAssignments_remove_le
    {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} {i : Fin n}
    (hmem : i ∈ selectorTailSupport (n := n) β γ) :
    (selectorTailAssignments (n := n) β γ).erase
          (i, selectorTailValue (n := n) (β := β) (γ := γ) i hmem)).length
      < (selectorTailAssignments (n := n) β γ).length := by
  classical
  have hlen := length_selectorTailAssignments_remove
    (n := n) (β := β) (γ := γ) (i := i) hmem
  -- Так как в исходном списке действительно есть элемент с индексом `i`,
  -- его длина положительна, а полученное равенство позволяет немедленно
  -- вывести требуемое строгое неравенство.
  have hpos : 0 < (selectorTailAssignments (n := n) β γ).length := by
    classical
    obtain ⟨b, hb⟩ :=
      (mem_selectorTailSupport (n := n) (β := β) (γ := γ) (i := i)).1 hmem
    have hcard := List.length_pos_of_mem hb
    simpa using hcard
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.pos_iff_ne_zero.mp hpos)
  -- После подстановки `length = k.succ` получаем, что длина после удаления равна `k`.
  have hlen'' :
      (selectorTailAssignments (n := n) β γ).erase
            (i, selectorTailValue (n := n) (β := β) (γ := γ) i hmem)).length
        = k.succ - 1 := by
    simpa [hk] using hlen
  have hrewrite :
      (selectorTailAssignments (n := n) β γ).erase
            (i, selectorTailValue (n := n) (β := β) (γ := γ) i hmem)).length
        = k := by
    simpa [Nat.succ_sub_one] using hlen''
  -- Теперь требуемое неравенство следует из `k < k.succ`.
  have : k < k.succ := Nat.lt_succ_self k
  simpa [hk, hrewrite]

/--
  Глобальная поддержка хвостовых присваиваний: объединяем множества
  `selectorTailSupport β γ` по всем селекторам из `leafSelectorFinset`.  Эта
  конструкция понадобится при оценках глубины объединённых хвостов.
-/
noncomputable def leafSelectorTailSupport {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : Finset (Fin n) :=
  (leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).sup
    (fun γ => selectorTailSupport (n := n) β γ)

/--
  Список координат глобальной хвостовой поддержки.  Порядок фиксируется
  произвольным образом (через `Finset`), однако мы гарантируем отсутствие
  повторов, что позволяет безопасно использовать его в индуктивных процедурах
  вроде `Subcube.refineByCoords`.-/
noncomputable def leafSelectorTailSupportList {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Fin n) :=
  (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).1.toList

lemma leafSelectorTailSupportList_nodup {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    (leafSelectorTailSupportList (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ).Nodup := by
  classical
  simpa [leafSelectorTailSupportList]
    using (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ).2.nodup_toList

lemma leafSelectorTailSupportList_toFinset {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    (leafSelectorTailSupportList (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ).toFinset
      = leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ := by
  classical
  ext i
  constructor
  · intro hi
    have hi_list : i ∈ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ).1.toList :=
      (List.mem_toFinset).1 hi
    have hi_multiset := (Multiset.mem_toList).1 hi_list
    exact (Finset.mem_def).2 hi_multiset
  · intro hi
    have hi_multiset : i ∈ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ).1 :=
      (Finset.mem_def).1 hi
    have hi_list : i ∈ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ).1.toList :=
      Multiset.mem_toList.mpr hi_multiset
    exact (List.mem_toFinset).2 hi_list

lemma refineBySupport_assignMany {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (hmem : γ ∈ Core.Subcube.refineByCoords β
        (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ)) :
    ∃ updates : List (BitFix n),
      updates.Nodup ∧
      (∀ pair ∈ updates, pair.1 ∈ leafSelectorTailSupport (n := n) (M := M)
          (τ := τ) (w := w) (t := t) (packages := packages) A hβ) ∧
      Subcube.assignMany β updates = some γ := by
  classical
  have hnodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  obtain ⟨updates, hnodup_updates, hsubset, hassign⟩ :=
    Core.Subcube.mem_refineByCoords_assignMany
      (β := β) (γ := γ)
      (coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ)
      hnodup hmem
  refine ⟨updates, hnodup_updates, ?subset, hassign⟩
  intro pair hpair
  have hfinset := hsubset pair hpair
  have hcoords := leafSelectorTailSupportList_toFinset
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  simpa [hcoords]

/--
  Дизъюнктная нормализация селекторов на фиксированной оси `A`.  Мы разбиваем
  лист `β` по координатам глобальной поддержки и сохраняем только те уточнения,
  которые вложены в исходные селекторы `leafSelectorSet`.  Этот вариант не
  требует готового `CombinedTailCertificate` и пригодится при построении хвостов
  напрямую из оси.
-/
noncomputable def axisRefineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : List (Subcube n) :=
  let coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ
  let base := Core.Subcube.refineByCoords β coords
  base.filter (fun γ =>
    ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ,
      Core.Subcube.subset (n := n) γ selector)

/--
  Версия `refineDisjoint`, привязанная к конкретному комбинированному
  сертификату.  Она просто подставляет ось `C.witness.axis` в
  `axisRefineDisjoint`, сохраняя существующие обозначения.
-/
noncomputable def refineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) : List (Subcube n) :=
  axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C.witness.axis hβ

/--
  Formula-aware refinement of the global leaf list.  We take the canonical
  disjoint partition `axisRefineDisjoint` and keep only those subcubes that are
  controlled by selectors coming from the specific function `f`.  This bridges
  the gap between per-function tail selectors and the axis-level PDT: each
  element of this list is simultaneously a leaf of the global candidate and a
  subset of some original selector for `f`.
-/
noncomputable def axisGlobalTailSelectors {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (f : BitVec n → Bool) : List (Subcube n) :=
  (axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).filter (fun γ =>
        ∃ selector ∈ combinedTailSelectors (n := n) (M := M)
            (τ := τ) (w := w) (t := t) packages A hβ f,
          Core.Subcube.subset (n := n) γ selector)

/--
  Version of `axisGlobalTailSelectors` specialized to a concrete combined tail
  certificate.  This keeps the original notation `globalTailSelectors` for later
  use in the certificate-level statements.
-/
noncomputable def globalTailSelectors {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (f : BitVec n → Bool) : List (Subcube n) :=
  axisGlobalTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C.witness.axis hβ f

lemma mem_axisRefineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ ↔
      γ ∈ Core.Subcube.refineByCoords β
        (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ)
        ∧ ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) A hβ,
          Core.Subcube.subset (n := n) γ selector := by
  classical
  unfold axisRefineDisjoint
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords
  set base := Core.Subcube.refineByCoords β coords with hbase
  constructor
  · intro hmem
    have hmem_base : γ ∈ base := by
      have := List.mem_of_mem_filter hmem
      simpa [hbase] using this
    have hpredicate :
        ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) A hβ,
          Core.Subcube.subset (n := n) γ selector := by
      obtain ⟨_, hcond⟩ := List.mem_filter.mp hmem
      simpa [hbase] using hcond
    simpa [hcoords, hbase]
      using And.intro (by simpa [hbase] using hmem_base) hpredicate
  · rintro ⟨hmem_base, hpredicate⟩
    have :
        γ ∈ base ∧
          ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w)
              (t := t) (packages := packages) A hβ,
            Core.Subcube.subset (n := n) γ selector := by
      exact And.intro (by simpa [hcoords, hbase] using hmem_base) hpredicate
    simpa [hcoords, hbase] using List.mem_filter.mpr this

lemma axisRefineDisjoint_cover {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {x : BitVec n}
    (hxβ : Core.Subcube.mem (n := n) β x)
    (hx : ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ,
      Core.Subcube.mem (n := n) selector x) :
    ∃ γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ,
      Core.Subcube.mem (n := n) γ x := by
  classical
  obtain ⟨selector, hselector, hxselector⟩ := hx
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords_def
  set base := Core.Subcube.refineByCoords β coords with hbase_def
  have hcoords_nodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  obtain ⟨γ, hγ_base, hγx, _⟩ :=
    Core.Subcube.exists_mem_refineByCoords_of_mem
      (n := n) (β := β) (coords := coords) (x := x) hxβ
  have hsubset_γ_β : Core.Subcube.subset (n := n) γ β :=
    Core.Subcube.subset_of_mem_refineByCoords
      (n := n) (β := β) (γ := γ)
      (coords := coords) hcoords_nodup hγ_base
  have hsubset_γ_selector : Core.Subcube.subset (n := n) γ selector := by
    intro y hyγ
    refine (Core.Subcube.mem_iff (n := n) (β := selector) (x := y)).2 ?_
    intro i b hselib
    have hxsel :=
      (Core.Subcube.mem_iff (n := n) (β := selector) (x := x)).1
        hxselector i b hselib
    by_cases hβi : β i = none
    · have hpair_assign :
        (i, b) ∈ selectorTailAssignments (n := n) β selector := by
        have hassign :=
          (mem_selectorAssignments (n := n) (γ := selector)
            (pair := (i, b))).2 (by simpa using hselib)
        exact
          (mem_selectorTailAssignments (n := n) (β := β) (γ := selector)
            (pair := (i, b))).2 ⟨hassign, hβi⟩
      have hi_support : i ∈ selectorTailSupport (n := n) β selector := by
        refine (mem_selectorTailSupport (n := n) (β := β) (γ := selector)
          (i := i)).2 ?_
        exact ⟨b, hpair_assign⟩
      have hentry :
          (selector, selectorTailAssignments (n := n) β selector)
            ∈ leafSelectorTailAssignments (n := n) (M := M) (τ := τ)
              (w := w) (t := t) (packages := packages) A hβ :=
        mem_leafSelectorTailAssignments_of_mem_set
          (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) (A := A) hβ hselector
      have hi_global : i ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ :=
        selectorTailSupport_subset_leafSelectorTailSupport
          (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ hentry hi_support
      have hi_list : i ∈ coords := by
        have : coords =
            (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) A hβ).1.toList := by
          simpa [hcoords_def, leafSelectorTailSupportList]
        have himulti : i ∈
            (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) A hβ).1 :=
          (Finset.mem_def).1 hi_global
        have hilist' := Multiset.mem_toList.mpr himulti
        simpa [this] using hilist'
      have hγi := Core.Subcube.mem_refineByCoords_value_of_mem
        (n := n) β γ (coords := coords) (x := x)
        hcoords_nodup hxβ hγ_base hγx hi_list hβi
      have hγival : γ i = some b := by
        simpa [hxsel] using hγi
      have hyval :=
        (Core.Subcube.mem_iff (n := n) (β := γ) (x := y)).1 hyγ i b hγival
      simpa [hyval]
    · have hyβ := hsubset_γ_β y hyγ
      have hβval : β i = some b := by
        cases hvalue : β i with
        | none => contradiction
        | some c =>
            have hxβ_val :=
              (Core.Subcube.mem_iff (n := n) (β := β) (x := x)).1 hxβ i c
                (by simpa [hvalue])
            have hcb : c = b := by
              simpa [hxsel] using hxβ_val
            exact by simpa [hvalue, hcb]
      have hyval :=
        (Core.Subcube.mem_iff (n := n) (β := β) (x := y)).1 hyβ i b
          (by simpa [hβval])
      simpa using hyval
  have hpredicate :
      ∃ selector' ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ,
        Core.Subcube.subset (n := n) γ selector' :=
    ⟨selector, hselector, hsubset_γ_selector⟩
  have hmem_filter :
      γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
    have := List.mem_filter.mpr ⟨hγ_base, hpredicate⟩
    simpa [axisRefineDisjoint, hcoords_def, hbase_def]
      using this
  exact ⟨γ, hmem_filter, hγx⟩

lemma mem_refineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ ↔
      γ ∈ Core.Subcube.refineByCoords β
        (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C.witness.axis hβ)
        ∧ ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C.witness.axis hβ,
          Core.Subcube.subset (n := n) γ selector := by
  simpa [refineDisjoint, axisRefineDisjoint]
    using mem_axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := C.witness.axis) (β := β) (γ := γ) hβ

lemma refineDisjoint_cover {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {x : BitVec n}
    (hxβ : Core.Subcube.mem (n := n) β x)
    (hx : ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ,
      Core.Subcube.mem (n := n) selector x) :
    ∃ γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ,
      Core.Subcube.mem (n := n) γ x :=
  axisRefineDisjoint_cover (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) hβ hxβ
      (by simpa using hx)

/--
  Конкретный селектор `γ` порождает лист осевого списка `axisRefineDisjoint`,
  причём полученный подкуб `δ` лежит внутри `γ`.  Построение повторяет
  `axisRefineDisjoint_cover`, но фиксирует исходный селектор, чтобы затем
  сравнить его хвостовую поддержку с каноническим листом.-/
lemma exists_axisRefineDisjoint_subset_leafSelector {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    ∃ δ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ,
      Core.Subcube.subset (n := n) δ γ := by
  classical
  set x : BitVec n := fun i => (γ i).getD false
  have hxγ : Core.Subcube.mem (n := n) γ x := by
    refine (Core.Subcube.mem_iff (n := n) (β := γ) (x := x)).2 ?_
    intro i b hγi
    have : γ i = some b := hγi
    simpa [x, this]
  have hxβ : Core.Subcube.mem (n := n) β x := by
    refine (Core.Subcube.mem_iff (n := n) (β := β) (x := x)).2 ?_
    intro i b hβi
    have : γ i = some b := hsubset hβi
    simpa [x, this]
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords_def
  set base := Core.Subcube.refineByCoords β coords with hbase_def
  have hcoords_nodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  obtain ⟨δ, hδ_base, hδx, -⟩ :=
    Core.Subcube.exists_mem_refineByCoords_of_mem
      (n := n) (β := β) (coords := coords) (x := x) hxβ
  have hsubset_δ_β : Core.Subcube.subset (n := n) δ β :=
    Core.Subcube.subset_of_mem_refineByCoords
      (n := n) (β := β) (γ := δ)
      (coords := coords) hcoords_nodup hδ_base
  have hsubset_δ_γ : Core.Subcube.subset (n := n) δ γ := by
    intro y hyδ
    refine (Core.Subcube.mem_iff (n := n) (β := γ) (x := y)).2 ?_
    intro i b hγib
    by_cases hβi : β i = none
    · have hpair : (i, b) ∈ selectorTailAssignments (n := n) β γ := by
        have hassign :=
          (mem_selectorAssignments (n := n) (γ := γ)
              (pair := (i, b))).2 (by simpa [hγib])
        exact
          (mem_selectorTailAssignments (n := n) (β := β) (γ := γ)
            (pair := (i, b))).2 ⟨hassign, hβi⟩
      have hi_support : i ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ := by
        have hentry :
            (γ, selectorTailAssignments (n := n) β γ)
              ∈ leafSelectorTailAssignments (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) A hβ :=
          mem_leafSelectorTailAssignments_of_mem_set
            (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) (A := A) hβ hγ
        exact selectorTailSupport_subset_leafSelectorTailSupport
          (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ hentry
          ((mem_selectorTailSupport (n := n) (β := β) (γ := γ)
              (i := i)).2 ⟨b, hpair⟩)
      have hi_list : i ∈ coords := by
        have : coords =
            (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) A hβ).1.toList := by
          simpa [hcoords_def, leafSelectorTailSupportList]
        have himulti : i ∈
            (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) A hβ).1 :=
          (Finset.mem_def).1 hi_support
        have hilist' := Multiset.mem_toList.mpr himulti
        simpa [this] using hilist'
      have hδval := Core.Subcube.mem_refineByCoords_value_of_mem
        (n := n) β δ (coords := coords) (x := y)
        hcoords_nodup
        (hsubset_δ_β y hyδ) hδ_base hyδ hi_list hβi
      have : y i = b := by
        have hyδ_val :=
          (Core.Subcube.mem_iff (n := n) (β := δ) (x := y)).1 hyδ i b
            (by simpa [hδval])
        simpa using hyδ_val
      simpa [this]
    · have hyβ := hsubset_δ_β y hyδ
      obtain ⟨c, hc⟩ : ∃ c, β i = some c := by
        cases hβval : β i with
        | none => exact (hβi hβval).elim
        | some c => exact ⟨c, rfl⟩
      have hγc : γ i = some c := hsubset (by simpa [hc])
      have hc_eq : c = b := by
        simpa [hγib, hγc]
      have hβval : β i = some b := by simpa [hc, hc_eq]
      have hyval :=
        (Core.Subcube.mem_iff (n := n) (β := β) (x := y)).1 hyβ i b
          (by simpa [hβval])
      simpa [hyval]
  have hpredicate :
      ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ,
        Core.Subcube.subset (n := n) δ selector :=
    ⟨γ, hγ, hsubset_δ_γ⟩
  have hδ_mem :
      δ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
    have := List.mem_filter.mpr ⟨hδ_base, hpredicate⟩
    simpa [axisRefineDisjoint, hcoords_def, hbase_def] using this
  exact ⟨δ, hδ_mem, hsubset_δ_γ⟩

lemma exists_refineDisjoint_subset_leafSelector {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    ∃ δ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ,
      Core.Subcube.subset (n := n) δ γ :=
  exists_axisRefineDisjoint_subset_leafSelector
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) (γ := γ)
    hβ hγ hsubset

/--
  Any selector returned by `combinedTailSelectors` admits a canonical refinement
  inside `axisGlobalTailSelectors`.  The lemma assumes that the selector agrees
  with the axis leaf `β` on all already fixed coordinates; later on это условие
  будет получено напрямую из пакетного хвостового сертификата.  В результате мы
  получаем нормализованный подкуб `δ`, который одновременно лежит в
  `axisGlobalTailSelectors` (а значит, является листом глобального PDT) и вложен
  в исходный селектор `γ`.
-/
lemma exists_axisGlobalTailSelector_subset_of_mem_combined {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily
        (Fs := flattenedCNFs (n := n) (M := M) (τ := τ) (w := w) (t := t)
          packages))
    {γ : Subcube n}
    (hγ : γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        packages A hβ f)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    ∃ δ ∈ axisGlobalTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ f,
      Core.Subcube.subset (n := n) δ γ := by
  classical
  -- Любой объединённый селектор входит в `leafSelectorSet`, поэтому к нему можно
  -- применить уже доказанную нормализацию через `axisRefineDisjoint`.
  have hγ_leaf : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ :=
    mem_leafSelectorSet_of_mem_combined (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) (A := A) hβ hf hγ
  obtain ⟨δ, hδ_mem, hδ_subset⟩ :=
    exists_axisRefineDisjoint_subset_leafSelector
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := A) (β := β) (γ := γ) hβ hγ_leaf hsubset
  -- После этого остаётся заметить, что отфильтрованный список
  -- `axisGlobalTailSelectors` именно и выбирает такие уточнения.
  have hglobal : δ ∈ axisGlobalTailSelectors (n := n) (M := M) (τ := τ) (w := w)
      (t := t) (packages := packages) A hβ f := by
    refine (mem_axisGlobalTailSelectors (n := n) (M := M) (τ := τ) (w := w)
        (t := t) (packages := packages) (A := A) (β := β) (γ := δ) hβ
        (f := f)).2 ?_
    exact ⟨hδ_mem, γ, hγ, hδ_subset⟩
  exact ⟨δ, hglobal, hδ_subset⟩

/--
  A certificate-level version of
  `exists_axisGlobalTailSelector_subset_of_mem_combined`.  Here we simply plug in
  the axis `C.witness.axis`, so the resulting subcube lives in the global list
  `globalTailSelectors` associated with the combined certificate.
-/
lemma exists_globalTailSelector_subset_of_mem_combined {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily
        (Fs := flattenedCNFs (n := n) (M := M) (τ := τ) (w := w) (t := t)
          packages))
    {γ : Subcube n}
    (hγ : γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        packages C.witness.axis hβ f)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    ∃ δ ∈ globalTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ f,
      Core.Subcube.subset (n := n) δ γ :=
  exists_axisGlobalTailSelector_subset_of_mem_combined
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis)
    (β := β) hβ (f := f) hf hγ hsubset

lemma axisRefineDisjoint_pairwise_disjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    (axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ).Pairwise
      (Core.Subcube.disjoint (n := n)) := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ
  have hpair := Core.Subcube.refineByCoords_pairwise_disjoint
      (n := n) (β := β) (coords := coords)
  have hsub := List.filter_sublist
      (l := Core.Subcube.refineByCoords β coords)
      (p := fun γ =>
        ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ,
          Core.Subcube.subset (n := n) γ selector)
  exact hpair.sublist hsub

lemma refineDisjoint_pairwise_disjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    (refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ).Pairwise
      (Core.Subcube.disjoint (n := n)) :=
  axisRefineDisjoint_pairwise_disjoint
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) hβ

lemma axisRefineDisjoint_subset_leaf {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (hγ : γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    Core.Subcube.subset (n := n) γ β := by
  classical
  obtain ⟨hmem_base, -⟩ :=
    (mem_axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) (A := A) (β := β) (γ := γ) hβ).1 hγ
  have hcoords := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  have := Core.Subcube.subset_of_mem_refineByCoords
    (n := n) (β := β) (γ := γ)
    (coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ)
    hcoords hmem_base
  simpa using this

lemma refineDisjoint_subset_leaf {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hγ : γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ) :
    Core.Subcube.subset (n := n) γ β :=
  axisRefineDisjoint_subset_leaf
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) (γ := γ) hβ
    (by simpa [refineDisjoint, axisRefineDisjoint] using hγ)

lemma exists_selector_of_mem_axisRefineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (hγ : γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ,
      Core.Subcube.subset (n := n) γ selector := by
  classical
  obtain ⟨-, hsubset⟩ :=
    (mem_axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) (A := A) (β := β) (γ := γ) hβ).1 hγ
  exact hsubset

lemma exists_selector_of_mem_refineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hγ : γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ) :
    ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ,
      Core.Subcube.subset (n := n) γ selector :=
  exists_selector_of_mem_axisRefineDisjoint
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) (γ := γ) hβ
    (by simpa [refineDisjoint, axisRefineDisjoint] using hγ)

lemma axisRefineDisjoint_length_le_support {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    (axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ).length
      ≤ 2 ^ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ).card := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords
  set base := Core.Subcube.refineByCoords β coords with hbase
  have hfilter :
      (axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ).length
        ≤ base.length := by
    simpa [axisRefineDisjoint, hcoords, hbase]
      using List.length_filter_le base
        (fun γ =>
          ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
              (w := w) (t := t) (packages := packages) A hβ,
            Core.Subcube.subset (n := n) γ selector)
  have hbase_len : base.length ≤ 2 ^ coords.length := by
    simpa [hbase]
      using Core.Subcube.length_refineByCoords_le_pow_two
        (n := n) (β := β) (coords := coords)
  have hcard :
      coords.length
        = (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ).card := by
    classical
    have : coords =
        (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ).1.toList := by
      simpa [hcoords, leafSelectorTailSupportList]
    subst this
    simpa [Finset.card, Multiset.card] using
      (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ).1.length_toList
  have htotal :
      (axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ).length
        ≤ 2 ^ coords.length :=
    hfilter.trans hbase_len
  simpa [hcard] using htotal

lemma refineDisjoint_length_le_support {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    (refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ).length
      ≤ 2 ^ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ).card :=
  axisRefineDisjoint_length_le_support
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) hβ

/--
  Любая координата, появляющаяся в глобальной поддержке `leafSelectorTailSupport`,
  действительно принадлежит хвостовым присваиваниям некоторого селектора.
-/
lemma mem_leafSelectorTailSupport {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) {i : Fin n} :
    i ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ
      ↔ ∃ γ ∈ leafSelectorFinset (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C.witness.axis hβ,
        i ∈ selectorTailSupport (n := n) β γ := by
  classical
  unfold leafSelectorTailSupport
  constructor
  · intro hmem
    obtain ⟨γ, hγ_mem, hγ_contains⟩ := Finset.mem_sup.1 hmem
    exact ⟨γ, hγ_mem, hγ_contains⟩
  · rintro ⟨γ, hγ_mem, hγ_contains⟩
    exact Finset.mem_sup.2 ⟨γ, hγ_mem, hγ_contains⟩

/--
  Мощность глобальной хвостовой поддержки не превышает мощности полной поддержки
  объединённых селекторов.  Используется при оценке числа дополнительных
  ветвлений при склейке хвостов.
-/
lemma card_leafSelectorTailSupport_le_support
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ).card
      ≤ (leafSelectorSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C.witness.axis hβ).card := by
  classical
  refine Finset.card_le_of_subset ?subset
  intro i hi
  obtain ⟨γ, hγ_mem, hγ_contains⟩ :=
    (mem_leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ (i := i)).1 hi
  have hsubset := selectorTailSupport_subset_support (β := β) (γ := γ)
  have hi_support : i ∈ selectorSupport (n := n) γ :=
    hsubset hγ_contains
  have hγ_support_subset :
      selectorSupport (n := n) γ
        ⊆ leafSelectorSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages)
            C.witness.axis hβ := by
    intro j hj
    have hmem_finset : γ ∈
        leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C.witness.axis hβ := by
      simpa [leafSelectorFinset]
        using hγ_mem
    exact Finset.mem_sup.2 ⟨γ, hmem_finset, hj⟩
  exact hγ_support_subset hi_support

/--
  Each element of the normalized disjoint refinement remains a leaf of the PDT
  constructed via `Core.Subcube.refineByCoordsPDT` on the global support list.
-/
lemma mem_axisRefineDisjoint_leaves_refineByCoordsPDT {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (hγ : γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    γ ∈ PDT.leaves
      (Core.Subcube.refineByCoordsPDT (n := n) β
        (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ)) := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords
  have hmem_base : γ ∈ Core.Subcube.refineByCoords (n := n) β coords := by
    obtain ⟨hmem, -⟩ :=
      (mem_axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) (A := A) (β := β) (γ := γ) hβ).1 hγ
    simpa [hcoords] using hmem
  have hleaves :=
    Core.Subcube.leaves_refineByCoordsPDT (n := n) (β := β) (coords := coords)
  have hmem_leaves :
      γ ∈ PDT.leaves
        (Core.Subcube.refineByCoordsPDT (n := n) β coords) := by
    simpa [hleaves] using hmem_base
  simpa [hcoords] using hmem_leaves

lemma mem_refineDisjoint_leaves_refineByCoordsPDT {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hγ : γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ) :
    γ ∈ PDT.leaves
      (Core.Subcube.refineByCoordsPDT (n := n) β
        (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C hβ)) :=
  mem_axisRefineDisjoint_leaves_refineByCoordsPDT
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis) (β := β) (γ := γ) hβ
    (by simpa [refineDisjoint, axisRefineDisjoint] using hγ)

/--
  The depth of the PDT generated from the global tail-support list is bounded by
  the size of that support.
-/
lemma depth_refineByCoordsPDT_le_leafSelectorTailSupport {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    PDT.depth
        (Core.Subcube.refineByCoordsPDT (n := n) β
          (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ))
      ≤ (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ).card := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords
  have hdepth :=
    Core.Subcube.depth_refineByCoordsPDT_le (n := n) (β := β) (coords := coords)
  have hlen :
      coords.length
        = (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ).card := by
    have : coords =
        (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ).1.toList := by
      simpa [hcoords, leafSelectorTailSupportList]
    subst this
    simpa [Finset.card, Multiset.card] using
      (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) A hβ).1.length_toList
  simpa [hcoords, hlen] using hdepth

namespace CombinedTailCertificate

/--
  PDT-кандидат, построенный только из оси `A` и глобальной хвостовой поддержки.
  Эта версия удобна до появления комбинированного сертификата, а поле
  `globalTailCandidate` ниже просто подставляет `C.witness.axis`.
-/
noncomputable def axisGlobalTailCandidate
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : PDT n :=
  Core.Subcube.refineByCoordsPDT (n := n) β
    (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ)

/--
  A PDT candidate obtained by refining the axis leaf along the global tail
  support extracted from `C`.
-/
noncomputable def globalTailCandidate
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) : PDT n :=
  axisGlobalTailCandidate (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C.witness.axis hβ

lemma axisRefineDisjoint_leaves_axisGlobalTailCandidate
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    (hγ : γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    γ ∈ PDT.leaves
      (axisGlobalTailCandidate (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) := by
  classical
  simpa [axisGlobalTailCandidate]
    using mem_axisRefineDisjoint_leaves_refineByCoordsPDT
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := A) (β := β) (γ := γ) hβ hγ

lemma depth_axisGlobalTailCandidate_le
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    PDT.depth (axisGlobalTailCandidate (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ)
      ≤ (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ).card := by
  classical
  simpa [axisGlobalTailCandidate]
    using depth_refineByCoordsPDT_le_leafSelectorTailSupport
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := A) (β := β) hβ

lemma refineDisjoint_leaves_globalTailCandidate
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hγ : γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ) :
    γ ∈ PDT.leaves (globalTailCandidate (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ) := by
  classical
  simpa [globalTailCandidate]
    using axisRefineDisjoint_leaves_axisGlobalTailCandidate
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := C.witness.axis) (β := β) (γ := γ) hβ
      (by simpa [refineDisjoint, axisRefineDisjoint] using hγ)

/--
  Membership in the per-function global list splits into two independent pieces:
  being one of the axis-level refined leaves and being covered by one of the
  selectors returned by `combinedTailSelectors` for that function.
-/
lemma mem_axisGlobalTailSelectors {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {f : BitVec n → Bool} :
    γ ∈ axisGlobalTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ f ↔
      γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ ∧
        ∃ selector ∈ combinedTailSelectors (n := n) (M := M) (τ := τ)
            (w := w) (t := t) packages A hβ f,
          Core.Subcube.subset (n := n) γ selector := by
  classical
  unfold axisGlobalTailSelectors
  constructor
  · intro hmem
    obtain ⟨hmem_base, hpredicate⟩ := List.mem_filter.mp hmem
    have hmem' : γ ∈ axisRefineDisjoint (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ := by
      simpa using hmem_base
    rcases hpredicate with ⟨selector, hsel, hsubset⟩
    exact ⟨hmem', selector, hsel, hsubset⟩
  · intro hdata
    rcases hdata with ⟨hmem, selector, hsel, hsubset⟩
    exact List.mem_filter.mpr ⟨hmem, ⟨selector, hsel, hsubset⟩⟩

lemma mem_globalTailSelectors {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {f : BitVec n → Bool} :
    γ ∈ globalTailSelectors (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ f ↔
      γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C hβ ∧
        ∃ selector ∈ combinedTailSelectors (n := n) (M := M) (τ := τ)
            (w := w) (t := t) packages C.witness.axis hβ f,
          Core.Subcube.subset (n := n) γ selector := by
  classical
  simpa [globalTailSelectors, refineDisjoint, axisRefineDisjoint]
    using mem_axisGlobalTailSelectors (n := n) (M := M) (τ := τ) (w := w)
      (t := t) (packages := packages) (A := C.witness.axis) (β := β)
      (γ := γ) hβ (f := f)

lemma axisGlobalTailSelectors_mem_leaves_axisGlobalTailCandidate
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β γ : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {f : BitVec n → Bool}
    (hγ : γ ∈ axisGlobalTailSelectors (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ f) :
    γ ∈ PDT.leaves
        (axisGlobalTailCandidate (n := n) (M := M) (τ := τ) (w := w)
          (t := t) (packages := packages) A hβ) := by
  classical
  have hmem := (mem_axisGlobalTailSelectors (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) (A := A) (β := β) (γ := γ)
      (hβ := hβ) (f := f)).1 hγ
  exact axisRefineDisjoint_leaves_axisGlobalTailCandidate
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := A) (β := β) (γ := γ) hβ hmem.1

lemma globalTailSelectors_mem_leaves_globalTailCandidate
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {f : BitVec n → Bool}
    (hγ : γ ∈ globalTailSelectors (n := n) (M := M) (τ := τ) (w := w)
        (t := t) (packages := packages) C hβ f) :
    γ ∈ PDT.leaves (globalTailCandidate (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ) := by
  classical
  simpa [globalTailSelectors, globalTailCandidate, axisGlobalTailCandidate,
    refineDisjoint, axisRefineDisjoint]
    using axisGlobalTailSelectors_mem_leaves_axisGlobalTailCandidate
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := C.witness.axis) (β := β) (γ := γ) hβ
      (f := f) hγ

lemma depth_globalTailCandidate_le
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    PDT.depth (globalTailCandidate (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ)
      ≤ (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C.witness.axis hβ).card := by
  classical
  simpa [globalTailCandidate]
    using depth_axisGlobalTailCandidate_le
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := C.witness.axis) (β := β) hβ

end CombinedTailCertificate

/--
  Если селектор `γ` расширяет лист `β` и его хвостовая поддержка совпадает с
  глобальной поддержкой `leafSelectorTailSupport`, то `γ` попадает в
  нормализованный список `refineDisjoint`.  В дальнейшем это позволит напрямую
  переносить селекторы из объединённого множества в листья
  `globalTailCandidate`.
-/
lemma leafSelector_mem_refineDisjoint_of_support_eq
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b)
    (hsupport : selectorTailSupport (n := n) β γ
        = leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) C.witness.axis hβ) :
    γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ := by
  classical
  have hcoords_mem := leafSelector_mem_refineByCoords_of_support_eq
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := C.witness.axis)
    (β := β) hβ (γ := γ) hsubset hsupport
  refine (mem_refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C (β := β) (γ := γ) hβ).2 ?_
  refine ⟨hcoords_mem, ?_⟩
  refine ⟨γ, hγ, ?_⟩
  simpa using Core.Subcube.subset_refl (n := n) (β := γ)

/--
  Фильтрация по свободным координатам не нарушает уникальность присваиваний:
  если две пары из `selectorTailAssignments β γ` совпадают по индексу, то это
  одна и та же пара.-/
lemma selectorTailAssignments_coordUnique {n : Nat}
    {β γ : Subcube n} {pair₁ pair₂ : BitFix n}
    (h₁ : pair₁ ∈ selectorTailAssignments (n := n) β γ)
    (h₂ : pair₂ ∈ selectorTailAssignments (n := n) β γ)
    (hcoord : pair₁.1 = pair₂.1) :
    pair₁ = pair₂ := by
  classical
  apply selectorAssignments_coordUnique
  · exact selectorTailAssignments_subset_assignments (β := β) (γ := γ) h₁
  · exact selectorTailAssignments_subset_assignments (β := β) (γ := γ) h₂
  · exact hcoord

/--
  Список `selectorTailAssignments` попарно различает координаты: это прямое
  следствие отсутствия дубликатов и леммы `selectorTailAssignments_coordUnique`,
  сводящее возможное совпадение координат к совпадению самих пар.  Удобная
  форма записи для дальнейшей работы с `assignMany_move_to_front`.-/
lemma selectorTailAssignments_pairwise_coords {n : Nat}
    {β γ : Subcube n} :
    (selectorTailAssignments (n := n) β γ).Pairwise
      (fun entry₁ entry₂ => entry₁.1 ≠ entry₂.1) := by
  classical
  refine Core.pairwise_coord_unique_of_nodup
    (updates := selectorTailAssignments (n := n) β γ)
    (hnodup := selectorTailAssignments_nodup (n := n) (β := β) (γ := γ)) ?_
  intro pair₁ pair₂ h₁ h₂ hcoord
  exact selectorTailAssignments_coordUnique (β := β) (γ := γ) h₁ h₂ hcoord

/--
  Удобное выражение для удаления пары `(i, b)` из списка
  `selectorTailAssignments β γ`: после разложения списка в виде
  `prefix ++ (i, b) :: suffix` операция `erase` просто склеивает `prefix`
  и `suffix`.  Поскольку хвостовые присваивания не содержат дубликатов,
  рассматриваемая пара не встречается в `prefix`, что позволяет свести
  доказательство к элементарной индукции по длине `prefix`.
-/
lemma selectorTailAssignments_erase_eq_concat
    {n : Nat} [DecidableEq (BitFix n)]
    {β γ : Subcube n} {i : Fin n} {b : Bool}
    {prefix suffix : List (BitFix n)}
    (hsplit : selectorTailAssignments (n := n) β γ
        = prefix ++ (i, b) :: suffix)
    (hmem : (i, b) ∈ selectorTailAssignments (n := n) β γ) :
    (selectorTailAssignments (n := n) β γ).erase (i, b)
      = prefix ++ suffix := by
  classical
  have hnodup := selectorTailAssignments_nodup (n := n) (β := β) (γ := γ)
  have hnotin_prefix : (i, b) ∉ prefix := by
    -- Деконструкция `nodup` для конкатенации показывает, что рассматриваемая
    -- пара не принадлежит `prefix`: в противном случае нарушилось бы условие
    -- попарной различимости списка `selectorTailAssignments`.
    have hdecomp := List.nodup_append.1 (by simpa [hsplit] using hnodup)
    have hdisjoint := (List.nodup_cons.1 hdecomp.2).1
    intro hcontra
    have hmem : (i, b) ∈ (i, b) :: suffix := by simp
    exact (hdisjoint hcontra hmem).elim
  -- После установления отсутствия пары `(i, b)` в префиксе переходим к
  -- стандартному факту об `erase` на конкатенации.
  revert suffix
  -- Индукция по префиксу позволяет аккуратно удалить рассматриваемую пару.
  refine List.rec ?base ?step prefix
  · intro suffix'
    have hlist : selectorTailAssignments (n := n) β γ
        = (i, b) :: suffix' := by
      simpa using hsplit
    simpa [hlist]
  · intro head tail ih suffix'
    intro hsplit'
    have htail : selectorTailAssignments (n := n) β γ
        = tail ++ (i, b) :: suffix' := by
      simpa [hsplit', List.cons_append, List.append_assoc] using hsplit
    have hhead_ne : head ≠ (i, b) := by
      intro hhead
      have : (i, b) ∈ head :: tail := by
        simpa [hhead] using List.mem_cons_self head tail
      have : (i, b) ∈ selectorTailAssignments (n := n) β γ := by
        simpa [hsplit'] using List.mem_append.2 <| Or.inl this
      exact (hnotin_prefix <| by
        simpa [List.mem_cons, hhead] using this).elim
    simp [hsplit', List.erase_cons_head, hhead_ne, ih suffix' htail]

/-- Координата каждого присваивания действительно не зафиксирована в `β`. -/
lemma selectorTailAssignments_coord_free {n : Nat}
    {β γ : Subcube n} {pair : BitFix n} :
    pair ∈ selectorTailAssignments (n := n) β γ → β pair.1 = none :=
  fun h => (mem_selectorTailAssignments (β := β) (γ := γ) (pair := pair)).1 h |>.2

/-- При обновлении `β` по координате `i` любая другая пара сохраняет
    принадлежность списку `selectorTailAssignments`. -/
lemma selectorTailAssignments_mem_update_iff {n : Nat}
    [DecidableEq (Fin n)]
    {β γ : Subcube n} {i : Fin n} {pair : BitFix n} {b : Bool}
    (hne : pair.1 ≠ i) :
    pair ∈ selectorTailAssignments (n := n) β γ
      ↔ pair ∈ selectorTailAssignments (n := n)
          (fun j : Fin n => if j = i then some b else β j) γ := by
  classical
  unfold selectorTailAssignments
  have : (fun j : Fin n => if j = i then some b else β j) pair.1 = β pair.1 := by
    simp [hne]
  simp [this]

lemma selectorTailSupport_mem_update_iff {n : Nat}
    [DecidableEq (Fin n)]
    {β γ : Subcube n} {i j : Fin n} {b : Bool}
    (hne : j ≠ i) :
    j ∈ selectorTailSupport (n := n) β γ
      ↔ j ∈ selectorTailSupport (n := n)
          (fun k : Fin n => if k = i then some b else β k) γ := by
  classical
  constructor
  · intro hj
    obtain ⟨value, hpair⟩ :=
      (mem_selectorTailSupport (n := n) (β := β) (γ := γ) (i := j)).1 hj
    have hmem :=
      (selectorTailAssignments_mem_update_iff (n := n)
        (β := β) (γ := γ) (i := i)
        (pair := (j, value)) (b := b)
        (hne := by simpa [Prod.fst] using hne)).1 hpair
    exact (mem_selectorTailSupport (n := n)
        (β := fun k => if k = i then some b else β k)
        (γ := γ) (i := j)).2 ⟨value, hmem⟩
  · intro hj
    obtain ⟨value, hpair⟩ :=
      (mem_selectorTailSupport (n := n)
          (β := fun k => if k = i then some b else β k)
          (γ := γ) (i := j)).1 hj
    have hmem :=
      (selectorTailAssignments_mem_update_iff (n := n)
        (β := β) (γ := γ) (i := i)
        (pair := (j, value)) (b := b)
        (hne := by simpa [Prod.fst] using hne)).2 hpair
    exact (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
        (i := j)).2 ⟨value, hmem⟩

lemma selectorTailValue_update_eq {n : Nat}
    [DecidableEq (Fin n)]
    {β γ : Subcube n} {i j : Fin n} {b : Bool}
    (hne : j ≠ i)
    (hmem : j ∈ selectorTailSupport (n := n) β γ) :
    selectorTailValue (n := n) (β := β) (γ := γ) j hmem
      = selectorTailValue (n := n)
          (β := fun k : Fin n => if k = i then some b else β k)
          (γ := γ) j
          ((selectorTailSupport_mem_update_iff (n := n)
              (β := β) (γ := γ) (i := i) (j := j) (b := b) hne).1 hmem) := by
  classical
  obtain ⟨value, hpair⟩ :=
    (mem_selectorTailSupport (n := n) (β := β) (γ := γ) (i := j)).1 hmem
  have hpair' :
      (j, value)
        ∈ selectorTailAssignments (n := n)
            (fun k => if k = i then some b else β k) γ := by
    have :=
      (selectorTailAssignments_mem_update_iff (n := n)
          (β := β) (γ := γ) (i := i)
          (pair := (j, value)) (b := b)
          (hne := by simpa [Prod.fst] using hne)).1 hpair
    simpa using this
  have hchosen := selectorTailValue_mem (n := n) (β := β) (γ := γ)
    (i := j) (hmem := hmem)
  have hchosen' := selectorTailValue_mem (n := n)
    (β := fun k => if k = i then some b else β k)
    (γ := γ) (i := j)
    (hmem := (selectorTailSupport_mem_update_iff (n := n)
        (β := β) (γ := γ) (i := i) (j := j) (b := b) hne).1 hmem)
  have huniq := selectorTailAssignments_coordUnique
    (n := n)
    (β := β) (γ := γ)
    (h₁ := hpair) (h₂ := hchosen)
    (hcoord := by simp)
  have huniq' := selectorTailAssignments_coordUnique
    (n := n)
    (β := fun k => if k = i then some b else β k)
    (γ := γ)
    (h₁ := hpair') (h₂ := hchosen')
    (hcoord := by simp)
  simpa [selectorTailValue, huniq, huniq']

/--
  Перенося пару `(i, b)` в начало списка хвостовых присваиваний, мы не меняем
  результат работы `assignMany`.  Порядок остальных элементов сохраняется за
  счёт использования `List.erase`, которая удаляет найденную пару из исходного
  списка.  Лемма служит строительным блоком для дальнейшей нормализации
  списков по фиксированному порядку координат из
  `leafSelectorTailSupportList`.
-/
lemma assignMany_selectorTailAssignments_cons_erase
    {n : Nat} [DecidableEq (BitFix n)]
    {β γ : Subcube n} {i : Fin n} {b : Bool}
    (hmem : (i, b) ∈ selectorTailAssignments (n := n) β γ) :
    Subcube.assignMany β ((i, b)
        :: (selectorTailAssignments (n := n) β γ).erase (i, b))
      = Subcube.assignMany β (selectorTailAssignments (n := n) β γ) := by
  classical
  obtain ⟨prefix, suffix, hsplit⟩ :=
    selectorTailAssignments_split (n := n) (β := β) (γ := γ)
      (i := i) (b := b) hmem
  have hrest :=
    selectorTailAssignments_erase_eq_concat
      (n := n) (β := β) (γ := γ) (i := i) (b := b)
      (prefix := prefix) (suffix := suffix) hsplit hmem
  have hpairwise := selectorTailAssignments_pairwise_coords
    (n := n) (β := β) (γ := γ)
  have hfree : ∀ entry ∈ (i, b) :: prefix ++ suffix, β entry.1 = none := by
    intro entry hentry
    have hmem_list : entry ∈ selectorTailAssignments (n := n) β γ := by
      have hsplit_mem : entry ∈ prefix ++ (i, b) :: suffix := by
        simpa [hsplit, List.cons_append, List.append_assoc]
          using hentry
      simpa [hsplit] using hsplit_mem
    exact selectorTailAssignments_coord_free (β := β) (γ := γ)
      (pair := entry) hmem_list
  have hpairwise' :
      ((i, b) :: prefix ++ suffix).Pairwise
        (fun e₁ e₂ => e₁.1 ≠ e₂.1) := by
    -- Попарное различие наследуется от исходного списка благодаря тому, что
    -- мы лишь переставили найденную пару в начало, не трогая остальные
    -- элементы.
    have := selectorTailAssignments_pairwise_coords
      (n := n) (β := β) (γ := γ)
    simpa [hsplit, List.cons_append, List.append_assoc]
      using this
  -- Применяем `assignMany_move_to_front` к разложению списка через найденный
  -- префикс и суффикс.
  have hmove := Core.assignMany_move_to_front (n := n) (β := β)
      (pair := (i, b)) (front := prefix) (suffix := suffix)
      (hfree := hfree) (hcoord := hpairwise')
  -- Собираем результат с учётом равенств `hsplit` и выражения для `erase`.
  simpa [hsplit, hrest, List.cons_append, List.append_assoc]
    using hmove

/--
  Присваивание из списка `selectorTailAssignments β γ` всегда успешно применимо к
  подкубу `β`: координата свободна, поэтому `Subcube.assign` возвращает новый
  подкуб, совпадающий с `β` за исключением фиксированного бита.  Лемма
  предоставляет явное выражение для результата и уточняет его поведение на всех
  координатах.  В дальнейшем это позволит по шагам восстанавливать селектор из
  последовательности присваиваний.
-/
lemma selectorTailAssignments_assign_eq_some {n : Nat}
    {β γ : Subcube n} {pair : BitFix n}
    (hmem : pair ∈ selectorTailAssignments (n := n) β γ) :
    ∃ β',
      Subcube.assign β pair.1 pair.2 = some β'
        ∧ β' pair.1 = some pair.2
        ∧ ∀ j, j ≠ pair.1 → β' j = β j := by
  classical
  have hfree : β pair.1 = none :=
    selectorTailAssignments_coord_free (β := β) (γ := γ) (pair := pair) hmem
  refine ⟨fun j => if j = pair.1 then some pair.2 else β j, ?_, ?_, ?_⟩
  · simp [Subcube.assign, hfree]
  · simp
  · intro j hj; simp [hj]

/--
  Уточнённая версия `selectorTailAssignments_assign_eq_some`: подстановка
  возвращаемого подкуба в явном виде избавляет от дальнейшего раскрытия
  определений `Subcube.assign`.
-/
lemma selectorTailAssignments_assign_eq_some'
    {n : Nat} {β γ : Subcube n} {pair : BitFix n}
    (hmem : pair ∈ selectorTailAssignments (n := n) β γ) :
    Subcube.assign β pair.1 pair.2
        = some (fun j => if j = pair.1 then some pair.2 else β j) := by
  classical
  have hfree := selectorTailAssignments_coord_free
    (β := β) (γ := γ) (pair := pair) hmem
  simp [Subcube.assign, hfree]

/-- Список присваиваний для хвоста не содержит повторов: фильтрация не нарушает
    лемму `selectorAssignments_nodup`. -/
lemma selectorTailAssignments_nodup {n : Nat}
    (β γ : Subcube n) :
    (selectorTailAssignments (n := n) β γ).Nodup := by
  classical
  unfold selectorTailAssignments
  exact List.nodup_filter _ (selectorAssignments_nodup (n := n) γ)

/-- Длина списка `selectorTailAssignments` не превосходит длины исходного списка
    присваиваний селектора.  Это прямое следствие свойств `List.filter`. -/
lemma length_selectorTailAssignments_le {n : Nat}
    (β γ : Subcube n) :
    (selectorTailAssignments (n := n) β γ).length
      ≤ (selectorAssignments (n := n) γ).length := by
  classical
  unfold selectorTailAssignments
  exact List.length_filter_le _ _

/--
  Длина списка «хвостовых» присваиваний ограничена размером объединённой
  поддержки `leafSelectorSupport`.  Связываем предыдущую оценку с глобальным
  числом координат, задействованных в хвостах, что пригодится при дальнейшем
  контроле глубины построенного PDT.
-/
lemma length_selectorTailAssignments_le_leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    (selectorTailAssignments (n := n) β γ).length
      ≤ (leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ).card := by
  classical
  refine
    Nat.le_trans
      (length_selectorTailAssignments_le (n := n) (β := β) (γ := γ))
      ?_
  exact
    length_selectorAssignments_le_leafSelectorSupport
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C hβ hγ

/-- Координаты «хвостовых» присваиваний также лежат в объединённой поддержке
    выбранного листа. -/
lemma selectorTailAssignments_subset_leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n) (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ)
    {pair : BitFix n}
    (hpair : pair ∈ selectorTailAssignments (n := n) β γ) :
    pair.1 ∈ leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C.witness.axis hβ := by
  classical
  exact C.selectorAssignments_subset_leafSelectorSupport
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) hβ hγ pair
    (selectorTailAssignments_subset_assignments (β := β) (γ := γ)
      (pair := pair) hpair)

/--
  Если координата принадлежит глобальной хвостовой поддержке, то она свободна в
  исходном листе `β`.  Действительно, такая координата появляется в одном из
  хвостовых списков `selectorTailAssignments β γ`, а значит `β` ещё не фиксирует
  её значение.-/
lemma beta_none_of_mem_leafSelectorTailSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) {i : Fin n}
    (hi : i ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ) :
    β i = none := by
  classical
  obtain ⟨γ, hγ_mem, hi_tail⟩ :=
    (mem_leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ (i := i)).1 hi
  obtain ⟨value, hvalue⟩ :=
    (mem_selectorTailSupport (n := n) (β := β) (γ := γ) (i := i)).1 hi_tail
  have : β i = none := by
    have := (mem_selectorTailAssignments (n := n) (β := β) (γ := γ)
        (pair := (i, value))).1 hvalue
    exact this.2
  simpa using this

/-- Длина `selectorTailAssignments β γ` совпадает с мощностью хвостовой
поддержки `selectorTailSupport β γ`: каждая координата встречается ровно один
раз. -/
lemma length_selectorTailAssignments_eq_card_tailSupport {n : Nat}
    [DecidableEq (Fin n)] {β γ : Subcube n} :
    (selectorTailAssignments (n := n) β γ).length
      = (selectorTailSupport (n := n) β γ).card := by
  classical
  set coords :=
      (selectorTailAssignments (n := n) β γ).map fun pair => pair.1 with hcoords
  have hnodup_pairs := selectorTailAssignments_nodup
    (n := n) (β := β) (γ := γ)
  have hmap_nodup : coords.Nodup := by
    subst hcoords
    refine List.Nodup.map_on hnodup_pairs ?_
    intro a ha b hb hfst
    exact selectorTailAssignments_coordUnique
      (β := β) (γ := γ) ha hb hfst
  have hcard :
      (selectorTailSupport (n := n) β γ).card = coords.length := by
    unfold selectorTailSupport
    simpa [Finset.card, coords, List.dedup_eq_self.mpr hmap_nodup]
  simpa [coords] using hcard.symm

/--
  Упорядоченная версия `selectorTailAssignments`: фиксируем список координат
  `coords` и двигаемся по нему слева направо. Как только очередная координата
  входит в локальную поддержку `selectorTailSupport β γ`, мы восстанавливаем
  соответствующее присваивание через `selectorTailValue` и добавляем его в
  результирующий список.  Позднее мы подставим сюда глобальный список
  `leafSelectorTailSupportList`, чтобы привести хвосты к единому порядку.
-/
noncomputable def selectorTailAssignmentsOrdered {n : Nat}
    [DecidableEq (Fin n)] (coords : List (Fin n))
    (β γ : Subcube n) : List (BitFix n) :=
  coords.filterMap fun i =>
    dite (i ∈ selectorTailSupport (n := n) β γ)
      (fun hi => some (i, selectorTailValue (n := n) (β := β) (γ := γ) i hi))
      (fun _ => none)

lemma selectorTailAssignmentsOrdered_nil {n : Nat}
    [DecidableEq (Fin n)] (β γ : Subcube n) :
    selectorTailAssignmentsOrdered (n := n) [] β γ = [] := by
  simp [selectorTailAssignmentsOrdered]

lemma selectorTailAssignmentsOrdered_cons {n : Nat}
    [DecidableEq (Fin n)] (coords : List (Fin n))
    (β γ : Subcube n) (i : Fin n) :
    selectorTailAssignmentsOrdered (n := n) (i :: coords) β γ =
      if hi : i ∈ selectorTailSupport (n := n) β γ then
        (i, selectorTailValue (n := n) (β := β) (γ := γ) i hi)
          :: selectorTailAssignmentsOrdered (n := n) coords β γ
      else selectorTailAssignmentsOrdered (n := n) coords β γ := by
  classical
  simp [selectorTailAssignmentsOrdered, hi]

lemma selectorTailAssignmentsOrdered_subset_assignments {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    {pair : BitFix n} :
    pair ∈ selectorTailAssignmentsOrdered (n := n) coords β γ →
      pair ∈ selectorTailAssignments (n := n) β γ := by
  classical
  intro hmem
  obtain ⟨i, hi_mem, rfl⟩ := List.mem_filterMap.1 hmem
  split_ifs at hi_mem with hsupport
  · have := selectorTailValue_mem (n := n) (β := β) (γ := γ)
        (i := i) (hmem := hsupport)
    simpa using this
  · cases hi_mem

lemma selectorTailAssignmentsOrdered_coord_mem {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    {pair : BitFix n}
    (hpair : pair ∈ selectorTailAssignmentsOrdered (n := n) coords β γ) :
    pair.1 ∈ coords.toFinset := by
  classical
  obtain ⟨i, hi_mem, hpair_eq⟩ := List.mem_filterMap.1 hpair
  split_ifs at hi_mem with hi_support
  · cases hpair_eq
    exact List.mem_toFinset.2 hi_mem
  · cases hi_mem

lemma selectorTailAssignmentsOrdered_coord_free {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    {pair : BitFix n}
    (hpair : pair ∈ selectorTailAssignmentsOrdered (n := n) coords β γ) :
    β pair.1 = none := by
  classical
  have hassign := selectorTailAssignmentsOrdered_subset_assignments
    (n := n) (coords := coords) (β := β) (γ := γ) hpair
  exact selectorTailAssignments_coord_free (β := β) (γ := γ)
    (pair := pair) hassign

lemma selectorTailAssignmentsOrdered_update_eq {n : Nat}
    [DecidableEq (Fin n)]
    {coords : List (Fin n)} {β γ : Subcube n}
    {i : Fin n} {b : Bool}
    (hnotin : i ∉ coords)
    (hmem : i ∈ selectorTailSupport (n := n) β γ) :
    selectorTailAssignmentsOrdered (n := n) coords β γ
      = selectorTailAssignmentsOrdered (n := n) coords
          (fun k : Fin n => if k = i then some b else β k) γ := by
  classical
  induction coords with
  | nil => simp [selectorTailAssignmentsOrdered]
  | cons head tail ih =>
      have hhead_ne : head ≠ i := by
        intro hcontr; exact hnotin (by simpa [hcontr])
      have htail : i ∉ tail := by
        intro htail_mem
        exact hnotin (by simp [htail_mem])
      have hmem_head :
          head ∈ selectorTailSupport (n := n) β γ
            ↔ head ∈ selectorTailSupport (n := n)
                (fun k => if k = i then some b else β k) γ :=
        selectorTailSupport_mem_update_iff
          (n := n) (β := β) (γ := γ) (i := i) (j := head) (b := b)
          (by simpa [ne_comm] using hhead_ne)
      by_cases hhead_mem : head ∈ selectorTailSupport (n := n) β γ
      · have hval := selectorTailValue_update_eq
          (n := n) (β := β) (γ := γ) (i := i) (j := head) (b := b)
          (hne := hhead_ne) (hmem := hhead_mem)
        simp [selectorTailAssignmentsOrdered_cons, hhead_mem,
          hmem_head.mpr hhead_mem, hval, ih htail hmem]
      · have hhead_mem' : head ∉ selectorTailSupport (n := n)
            (fun k => if k = i then some b else β k) γ :=
          by simpa [hmem_head] using hhead_mem
        simp [selectorTailAssignmentsOrdered_cons, hhead_mem, hhead_mem',
          ih htail hmem]

/--
  Применяя присваивания из упорядоченного списка `selectorTailAssignmentsOrdered`
  в точности в порядке координат `coords`, мы восстанавливаем селектор `γ`.
  Достаточно потребовать, чтобы `coords` покрывал локальную хвостовую
  поддержку и не содержал повторов, а также чтобы `γ` действительно расширял
  ствол `β` на уже фиксированных координатах.  Эти условия автоматически
  выполняются для селекторов из `leafSelectorSet`, поэтому лемма обеспечивает
  прямое включение таких селекторов в каноническое дерево `refineByCoords`.
-/
lemma assignMany_selectorTailAssignmentsOrdered {n : Nat}
    [DecidableEq (Fin n)]
    {coords : List (Fin n)} {β γ : Subcube n}
    (hnodup : coords.Nodup)
    (hcover : selectorTailSupport (n := n) β γ ⊆ coords.toFinset)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    Subcube.assignMany β
        (selectorTailAssignmentsOrdered (n := n) coords β γ) = some γ := by
  classical
  revert β hcover hsubset
  refine coords.rec ?base ?step
  · intro β hcover hsubset
    have hsupport_empty :
        selectorTailSupport (n := n) β γ ⊆ (∅ : Finset (Fin n)) := by
      simpa using hcover
    have hassigns_nil :
        selectorTailAssignments (n := n) β γ = [] := by
      by_contra hnonempty
      obtain ⟨pair, rest, hcons⟩ := List.exists_eq_cons_of_ne_nil hnonempty
      have hmem : pair ∈ selectorTailAssignments (n := n) β γ := by
        simpa [hcons]
      have hcoord : pair.1 ∈ selectorTailSupport (n := n) β γ :=
        (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
            (i := pair.1)).2 ⟨pair.2, hmem⟩
      have : pair.1 ∈ (∅ : Finset (Fin n)) := hsupport_empty hcoord
      simpa using this
    have hγβ : γ = β :=
      (selectorTailAssignments_eq_nil_iff (n := n) (β := β) (γ := γ)
            (hsubset := hsubset)).1 hassigns_nil
    subst hγβ
    simp [selectorTailAssignmentsOrdered_nil, Subcube.assignMany]
  · intro head tail ih β hcover hsubset
    have hnodup_tail : tail.Nodup := (List.nodup_cons.mp hnodup).2
    have hhead_notin_tail : head ∉ tail := (List.nodup_cons.mp hnodup).1
    have hcover_insert : selectorTailSupport (n := n) β γ
        ⊆ (Finset.insert head tail.toFinset) := by
      simpa [List.toFinset_cons] using hcover
    by_cases hhead_mem : head ∈ selectorTailSupport (n := n) β γ
    · set value := selectorTailValue (n := n) (β := β) (γ := γ)
          head hhead_mem with hvalue
      have hordered_cons :
          selectorTailAssignmentsOrdered (n := n) (head :: tail) β γ
            = (head, value)
                :: selectorTailAssignmentsOrdered (n := n) tail β γ := by
        simp [selectorTailAssignmentsOrdered_cons, hhead_mem, hvalue]
      have hpair_mem : (head, value)
            ∈ selectorTailAssignments (n := n) β γ := by
        simpa [hvalue] using
          selectorTailValue_mem (n := n) (β := β) (γ := γ)
            (i := head) (hmem := hhead_mem)
      have hassign_head := selectorTailAssignments_assign_eq_some'
        (n := n) (β := β) (γ := γ) (pair := (head, value)) hpair_mem
      set β' : Subcube n := fun j => if j = head then some value else β j
      have hassign_head' :
          Subcube.assign β head value = some β' := by
        simpa [β', hvalue] using hassign_head
      have hcover_tail' : selectorTailSupport (n := n) β' γ ⊆ tail.toFinset := by
        intro j hj
        have hj_ne_head : j ≠ head := by
          obtain ⟨val, hpair⟩ :=
            (mem_selectorTailSupport (n := n) (β := β') (γ := γ)
                (i := j)).1 hj
          have hfree := selectorTailAssignments_coord_free
              (n := n) (β := β') (γ := γ) (pair := (j, val)) hpair
          intro hjeq; subst hjeq
          have : β' head = none := by simpa using hfree
          have : some value = (none : Option Bool) := by
            simpa [β', hvalue] using this
          cases this
        have hj_mem : j ∈ selectorTailSupport (n := n) β γ := by
          have :=
            (selectorTailSupport_mem_update_iff (n := n)
                (β := β) (γ := γ) (i := head) (j := j) (b := value)
                hj_ne_head).2 hj
          simpa [β'] using this
        have hj_coords : j ∈ Finset.insert head tail.toFinset :=
          hcover_insert hj_mem
        simpa [Finset.mem_insert, hj_ne_head] using hj_coords
      have hsubset_tail : ∀ {i : Fin n} {b : Bool},
          β' i = some b → γ i = some b := by
        intro i b hi
        by_cases hi_head : i = head
        · subst hi_head
          have hassign_tail :=
            selectorTailAssignments_subset_assignments
              (β := β) (γ := γ) hpair_mem
          have hvalue_mem : γ head = some value := by
            have :=
              (mem_selectorAssignments (n := n) (γ := γ)
                  (pair := (head, value))).1 hassign_tail
            simpa [hvalue] using this
          have hval_eq : b = value := by
            have : β' head = some value := by simp [β', hvalue]
            exact Option.some.inj (by simpa [this] using hi)
          subst hval_eq
          simpa [hvalue_mem]
        · have : β i = some b := by simpa [β', hi_head] using hi
          exact hsubset (i := i) (b := b) this
      have hordered_tail_eq :=
        selectorTailAssignmentsOrdered_update_eq
          (n := n) (coords := tail) (β := β) (γ := γ)
          (i := head) (b := value) hhead_notin_tail hhead_mem
      have hassign_tail :=
        ih hnodup_tail hcover_tail' hsubset_tail
      have hassign_tail' : Subcube.assignMany β'
            (selectorTailAssignmentsOrdered (n := n) tail β γ) = some γ := by
        simpa [β', hordered_tail_eq]
          using hassign_tail
      simp [Subcube.assignMany, hordered_cons, hassign_head', hassign_tail']
    · have hcover_tail : selectorTailSupport (n := n) β γ ⊆ tail.toFinset := by
        intro j hj
        have hj_insert : j ∈ Finset.insert head tail.toFinset :=
          hcover_insert hj
        have hj_ne_head : j ≠ head := by
          intro hjeq; subst hjeq; exact hhead_mem hj
        simpa [Finset.mem_insert, hj_ne_head] using hj_insert
      have hordered_cons :
          selectorTailAssignmentsOrdered (n := n) (head :: tail) β γ
            = selectorTailAssignmentsOrdered (n := n) tail β γ := by
        simp [selectorTailAssignmentsOrdered_cons, hhead_mem]
      simpa [hordered_cons] using
        ih hnodup_tail hcover_tail hsubset

/--
  Если список координат `coords` в точности совпадает с поддержкой
  `selectorTailSupport β γ`, то селектор `γ` появляется среди листьев
  `Core.Subcube.refineByCoords β coords`.  Индукция по `coords` повторяет
  построение `refineByCoords`: на каждом шаге мы проверяем, что текущая
  координата действительно свободна в `β` и фиксируется `γ`, после чего
  переходим к хвосту списка и используем предположение индукции.
-/
lemma selectorTailAssignmentsOrdered_mem_refineByCoords {n : Nat}
    [DecidableEq (Fin n)]
    {coords : List (Fin n)} {β γ : Subcube n}
    (hnodup : coords.Nodup)
    (hsupport : selectorTailSupport (n := n) β γ = coords.toFinset)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    γ ∈ Core.Subcube.refineByCoords (n := n) β coords := by
  classical
  revert β hsupport hsubset
  refine coords.rec ?base ?step
  · intro β hsupport hsubset
    have hsupport_empty :
        selectorTailSupport (n := n) β γ = (∅ : Finset (Fin n)) := by
      simpa using hsupport
    have hassigns_nil :
        selectorTailAssignments (n := n) β γ = [] := by
      by_contra hnonempty
      obtain ⟨pair, rest, hcons⟩ :=
        List.exists_eq_cons_of_ne_nil hnonempty
      have hpair : pair ∈ selectorTailAssignments (n := n) β γ := by
        simpa [hcons]
      have hmem_support : pair.1 ∈ selectorTailSupport (n := n) β γ := by
        refine (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
            (i := pair.1)).2 ?_
        exact ⟨pair.2, hpair⟩
      have : pair.1 ∈ (∅ : Finset (Fin n)) := by
        simpa [hsupport_empty] using hmem_support
      exact Finset.not_mem_empty _ this
    have hγβ : γ = β :=
      (selectorTailAssignments_eq_nil_iff (n := n) (β := β) (γ := γ)
          (hsubset := hsubset)).1 hassigns_nil
    subst hγβ
    simpa [Core.Subcube.refineByCoords_nil]
  · intro head tail ih β hsupport hsubset
    have htail_nodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
    have hcoords_finset :
        (head :: tail).toFinset = Finset.insert head tail.toFinset := by
      simpa [List.toFinset_cons]
    have hcoords_insert :
        selectorTailSupport (n := n) β γ = Finset.insert head tail.toFinset := by
      simpa [hcoords_finset] using hsupport
    have hhead_support : head ∈ selectorTailSupport (n := n) β γ := by
      have : head ∈ (head :: tail).toFinset :=
        List.mem_toFinset.mpr (List.mem_cons_self _ _)
      simpa [hcoords_insert] using this
    obtain ⟨value, hvalue_mem⟩ : ∃ value,
        (head, value) ∈ selectorTailAssignments (n := n) β γ := by
      obtain ⟨value, hpair⟩ :=
        (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
            (i := head)).1 hhead_support
      exact ⟨value, hpair⟩
    have hβ_head_none : β head = none :=
      selectorTailAssignments_coord_free (β := β) (γ := γ)
        (pair := (head, value)) hvalue_mem
    set β' : Subcube n := fun j => if j = head then some value else β j
    have hsupport_tail :
        selectorTailSupport (n := n) β' γ = tail.toFinset := by
      apply Finset.ext
      intro j
      by_cases hj : j = head
      · subst hj
        constructor
        · intro hj_support
          obtain ⟨b, hb⟩ :=
            (mem_selectorTailSupport (n := n) (β := β') (γ := γ)
                (i := head)).1 hj_support
          have hfree := selectorTailAssignments_coord_free
            (β := β') (γ := γ) (pair := (head, b)) hb
          have : (some value : Option Bool) = none := by
            simpa [β', show (if head = head then some value else β head) = some value
                by simp] using hfree
          cases this
        · intro hj_tail
          simpa [List.mem_toFinset] using hj_tail
      · constructor
        · intro hj_support
          have :=
            (selectorTailSupport_mem_update_iff (n := n)
                (β := β) (γ := γ) (i := head) (j := j)
                (b := value) (hne := hj)).1 hj_support
          have : j ∈ Finset.insert head tail.toFinset := by
            simpa [hcoords_insert] using this
          simpa [Finset.mem_insert, hj]
        · intro hj_tail
          have : j ∈ selectorTailSupport (n := n) β γ := by
            have : j ∈ Finset.insert head tail.toFinset :=
              Finset.mem_insert.mpr (Or.inr hj_tail)
            simpa [hcoords_insert] using this
          exact
            (selectorTailSupport_mem_update_iff (n := n)
                (β := β) (γ := γ) (i := head) (j := j)
                (b := value) (hne := hj)).2 this
    have hsubset_tail : ∀ {i : Fin n} {b : Bool},
        β' i = some b → γ i = some b := by
      intro i b hi
      by_cases hi_head : i = head
      · subst hi_head
        have hvalue := (mem_selectorAssignments (n := n) (γ := γ)
            (pair := (head, value))).1
            (selectorTailAssignments_subset_assignments
              (β := β) (γ := γ) hvalue_mem)
        simpa [β'] using hvalue
      · have : β i = some b := by simpa [β', hi_head] using hi
        exact hsubset this
    have hmem_tail := ih htail_nodup hsupport_tail hsubset_tail
    have hbranch :
        β' ∈ Core.Subcube.splitCoordinate β head := by
      have := Core.Subcube.splitCoordinate_of_free
        (β := β) (i := head) (b := value) hβ_head_none
      by_cases hval : value = false
      · subst hval; simpa using this
      · have hval' : value = true := by cases value <;> simp [*] at *
        subst hval'; simpa using this
    exact
      (Core.Subcube.mem_refineByCoords_cons (β := β)
          (i := head) (rest := tail) (γ := γ)).2
        ⟨β', hbranch, hmem_tail⟩

/--
  Если локальная хвостовая поддержка конкретного селектора `γ` совпадает с
  глобальной поддержкой `leafSelectorTailSupport`, то сам селектор появляется в
  результатах `Core.Subcube.refineByCoords` по каноническому списку
  координат `leafSelectorTailSupportList`.  Это ключевой мост от равенства
  поддержек к принадлежности нормализованному PDT, построенному по глобальному
  порядку координат.
-/
lemma leafSelector_mem_refineByCoords_of_support_eq
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b)
    (hsupport : selectorTailSupport (n := n) β γ
        = leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ) :
    γ ∈ Core.Subcube.refineByCoords (n := n) β
      (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ) := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ with hcoords_def
  have hnodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  have hcoords_toFinset := leafSelectorTailSupportList_toFinset
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) A hβ
  have hsupport' : selectorTailSupport (n := n) β γ = coords.toFinset := by
    simpa [coords, hcoords_def, hcoords_toFinset]
      using hsupport
  exact selectorTailAssignmentsOrdered_mem_refineByCoords
    (n := n) (coords := coords) (β := β) (γ := γ)
    (hnodup := by simpa [coords, hcoords_def] using hnodup)
    (hsupport := hsupport') (hsubset := hsubset)

/--
  Если `γ` получается в результате `Core.Subcube.refineByCoords β coords`, то его
  хвостовая поддержка в точности совпадает с `coords.toFinset`.  Индукция по
  списку `coords` сводит утверждение к тому, что добавление головы не меняет
  хвостовые координаты для остальных элементов, что обеспечивается леммой
  `selectorTailSupport_mem_update_iff`.-/
lemma selectorTailSupport_eq_coords_of_mem_refineByCoords
    {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n} {coords : List (Fin n)}
    (hcoords : coords.Nodup)
    (hfree : ∀ i ∈ coords, β i = none)
    (hmem : γ ∈ Core.Subcube.refineByCoords (n := n) β coords) :
    selectorTailSupport (n := n) β γ = coords.toFinset := by
  classical
  revert β γ
  induction coords with
  | nil =>
      intro β γ _ hmem
      have hγ : γ = β := by
        simpa [Core.Subcube.refineByCoords, Core.Subcube.listBind]
          using hmem
      simpa [hγ, selectorTailSupport]
  | cons head tail ih =>
      intro β γ hcoords hfree hmem
      obtain ⟨hhead_not_mem, htail_nodup⟩ := List.nodup_cons.mp hcoords
      have hhead_free : β head = none := hfree head (by simp)
      obtain ⟨δ, hδ_split, hγ_tail⟩ :=
        (Core.Subcube.mem_refineByCoords_cons (β := β)
            (i := head) (rest := tail) (γ := γ)).1 hmem
    have hδ_assign : ∃ value : Bool,
        Subcube.assign β head value = some δ := by
      have hcases := Core.Subcube.mem_splitCoordinate
        (β := β) (i := head) (γ := δ) hδ_split
      have hcontr : ¬β head ≠ none := by simpa [hhead_free]
      simpa [hcontr] using hcases
      obtain ⟨value, hassign⟩ := hδ_assign
      have hδ_def : δ = fun j => if j = head then some value else β j := by
        have hassign_explicit :=
          Subcube.assign_of_none (n := n) (β := β) (i := head)
            (b := value) hhead_free
        have := hassign_explicit.trans hassign.symm
        exact (Option.some.inj this).symm
    have htail_free : ∀ i ∈ tail,
        (fun j => if j = head then some value else β j) i = none := by
      intro i hi_tail
      have hi_ne : i ≠ head := by
        exact fun h => hhead_not_mem (by simpa [h] using hi_tail)
      have : β i = none := hfree i (by simpa [hi_tail] using
        (by exact Or.inr hi_tail : i ∈ head :: tail))
      simp [hi_ne, this]
    have hsubset_tail : ∀ {i : Fin n} {b : Bool},
        (fun j => if j = head then some value else β j) i = some b →
          γ i = some b := by
      intro i b hi
      have hδ_subset :=
        Core.Subcube.subset_of_mem_refineByCoords (n := n)
          (β := δ) (γ := γ) (coords := tail)
          htail_nodup hγ_tail
      have hi' : δ i = some b := by simpa [hδ_def] using hi
      exact hδ_subset hi'
    have hsupport_tail := ih htail_nodup htail_free hγ_tail
    have hsubset :=
      Core.Subcube.subset_of_mem_refineByCoords (n := n)
        (β := β) (γ := γ) (coords := head :: tail)
        hcoords hmem
    apply Finset.ext
    intro i
    constructor
    · intro hi_support
      by_cases hi_head : i = head
      · subst hi_head
        have : γ head = some value := by
          have := hsubset (by simpa [hδ_def] using
            (by simp : δ head = some value))
          simpa using this
        have : head ∈ selectorTailSupport (n := n) β γ :=
          (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
            (i := head)).2 ⟨value,
              (mem_selectorTailAssignments (n := n)
                (β := β) (γ := γ) (pair := (head, value))).2
                ⟨(mem_selectorAssignments (n := n) (γ := γ)
                    (pair := (head, value))).2 this,
                  hhead_free⟩⟩
        simpa [List.mem_toFinset] using this
      · have hi_tail : i ∈ tail.toFinset := by
          have :=
            (selectorTailSupport_mem_update_iff (n := n)
                (β := β) (γ := γ) (i := head) (j := i)
                (b := value) (hne := hi_head)).1 hi_support
          simpa [hδ_def] using hi_tail
        simpa [Finset.mem_cons, hi_head]
          using hi_tail
    · intro hi_coords
      have hi_list : i = head ∨ i ∈ tail := by
        simpa [List.mem_toFinset, List.mem_cons] using hi_coords
      cases hi_list with
      | inl h =>
          subst h
          have : γ head = some value :=
            hsubset (by simpa [hδ_def] using
              (by simp : δ head = some value))
          have hmem_pair : (head, value)
              ∈ selectorTailAssignments (n := n) β γ :=
            (mem_selectorTailAssignments (n := n)
                (β := β) (γ := γ) (pair := (head, value))).2
              ⟨(mem_selectorAssignments (n := n)
                    (γ := γ) (pair := (head, value))).2 this,
                hhead_free⟩
          exact (mem_selectorTailSupport (n := n)
            (β := β) (γ := γ) (i := head)).2 ⟨value, hmem_pair⟩
      | inr hi_tail =>
          have hi_mem_tail : i ∈ selectorTailSupport
              (n := n) (β := fun j => if j = head then some value else β j)
              γ := by
            have := (List.mem_toFinset).2 hi_tail
            simpa [hsupport_tail]
              using this
          exact
            (selectorTailSupport_mem_update_iff (n := n)
                (β := β) (γ := γ) (i := head) (j := i)
                (b := value) (hne := by
                  intro h; subst h; exact hcoords.not_mem_head hi_tail)).2
              (by simpa [hδ_def] using hi_mem_tail)
lemma selectorTailAssignments_mem_of_subset_ordered {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    (hsupport : selectorTailSupport (n := n) β γ ⊆ coords.toFinset)
    {pair : BitFix n}
    (hpair : pair ∈ selectorTailAssignments (n := n) β γ) :
    pair ∈ selectorTailAssignmentsOrdered (n := n) coords β γ := by
  classical
  have hcoord : pair.1 ∈ selectorTailSupport (n := n) β γ := by
    refine (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
        (i := pair.1)).2 ?_
    exact ⟨pair.2, hpair⟩
  have hcoord_in_coords : pair.1 ∈ coords.toFinset := hsupport hcoord
  obtain ⟨idx, hidx_mem, rfl⟩ := List.mem_toFinset.1 hcoord_in_coords
  have hvalue_eq :
      selectorTailValue (n := n) (β := β) (γ := γ) idx hcoord = pair.2 := by
    have hchosen := selectorTailValue_mem (n := n) (β := β) (γ := γ)
      (i := idx) (hmem := hcoord)
    have hboth :
        (idx, selectorTailValue (n := n) (β := β) (γ := γ) idx hcoord)
          ∈ selectorTailAssignments (n := n) β γ := hchosen
    have hcoord_unique := selectorTailAssignments_coordUnique
      (n := n) (β := β) (γ := γ)
      (h₁ := hboth) (h₂ := hpair) (hcoord := by simp)
    exact congrArg Prod.snd hcoord_unique
  refine List.mem_filterMap.2 ?_
  refine ⟨idx, hidx_mem, ?_⟩
  simp [selectorTailAssignmentsOrdered, hcoord, hvalue_eq]

lemma selectorTailAssignmentsOrdered_subset {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    (hsupport : selectorTailSupport (n := n) β γ ⊆ coords.toFinset) :
    selectorTailAssignmentsOrdered (n := n) coords β γ ⊆
      selectorTailAssignments (n := n) β γ :=
  fun _ => selectorTailAssignmentsOrdered_subset_assignments (coords := coords)
    (β := β) (γ := γ)

lemma selectorTailSupport_eq_leafSelectorTailSupport_of_mem_refineDisjoint
    {n M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hγ : γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ) :
    selectorTailSupport (n := n) β γ
      = leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C hβ := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ with hcoords_def
  have hcoords_nodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ
  have hcoords_toFinset := leafSelectorTailSupportList_toFinset
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ
  have hfree_coords : ∀ i ∈ coords, β i = none := by
    intro i hi
    have hi_support : i ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ := by
      have : i ∈ coords.toFinset := List.mem_toFinset.mpr hi
      simpa [coords, hcoords_def, hcoords_toFinset] using this
    exact beta_none_of_mem_leafSelectorTailSupport
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C hβ hi_support
  obtain ⟨hmem_base, -⟩ :=
    (mem_refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C (β := β) (γ := γ) hβ).1 hγ
  have := selectorTailSupport_eq_coords_of_mem_refineByCoords
    (n := n) (β := β) (γ := γ) (coords := coords)
    (hcoords := by simpa [coords, hcoords_def] using hcoords_nodup)
    (hfree := hfree_coords) (hmem := hmem_base)
  simpa [coords, hcoords_def, hcoords_toFinset]
    using this

lemma selectorTailAssignments_subset_ordered {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    (hsupport : selectorTailSupport (n := n) β γ ⊆ coords.toFinset) :
    selectorTailAssignments (n := n) β γ ⊆
      selectorTailAssignmentsOrdered (n := n) coords β γ :=
  fun _ hp => selectorTailAssignments_mem_of_subset_ordered
    (coords := coords) (β := β) (γ := γ) hsupport hp

lemma selectorTailAssignmentsOrdered_mem_iff {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    (hsupport : selectorTailSupport (n := n) β γ ⊆ coords.toFinset)
    {pair : BitFix n} :
    pair ∈ selectorTailAssignmentsOrdered (n := n) coords β γ ↔
      pair ∈ selectorTailAssignments (n := n) β γ := by
  constructor
  · exact selectorTailAssignmentsOrdered_subset_assignments
      (n := n) (coords := coords) (β := β) (γ := γ)
  · exact selectorTailAssignments_mem_of_subset_ordered
      (n := n) (coords := coords) (β := β) (γ := γ) hsupport

lemma selectorTailAssignmentsOrdered_nodup {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    (hnodup : coords.Nodup) :
    (selectorTailAssignmentsOrdered (n := n) coords β γ).Nodup := by
  classical
  refine List.nodup_filterMap.mpr ?_
  constructor
  · exact hnodup
  · intro i hi j hj hneq
    split_ifs with hi_mem hj_mem <;> try cases hi_mem
    have hval_i := selectorTailValue_mem (n := n) (β := β) (γ := γ)
        (i := i) (hmem := hi_mem)
    have hval_j := selectorTailValue_mem (n := n) (β := β) (γ := γ)
        (i := j) (hmem := hj_mem)
    have hcoord_unique := selectorTailAssignments_coordUnique
      (n := n) (β := β) (γ := γ)
      (h₁ := hval_i) (h₂ := hval_j) (hcoord := hneq)
    simp [hcoord_unique]

lemma selectorTailAssignmentsOrdered_pairwise_coords {n : Nat}
    [DecidableEq (Fin n)] {coords : List (Fin n)} {β γ : Subcube n}
    (hnodup : coords.Nodup) :
    (selectorTailAssignmentsOrdered (n := n) coords β γ).Pairwise
      (fun entry₁ entry₂ => entry₁.1 ≠ entry₂.1) := by
  classical
  refine Core.pairwise_coord_unique_of_nodup
    (updates := selectorTailAssignmentsOrdered (n := n) coords β γ)
    (hnodup := selectorTailAssignmentsOrdered_nodup
      (n := n) (coords := coords) (β := β) (γ := γ) hnodup) ?_
  intro pair₁ pair₂ h₁ h₂ hcoord
  have h₁_assign := selectorTailAssignmentsOrdered_subset_assignments
    (n := n) (coords := coords) (β := β) (γ := γ) h₁
  have h₂_assign := selectorTailAssignmentsOrdered_subset_assignments
    (n := n) (coords := coords) (β := β) (γ := γ) h₂
  exact selectorTailAssignments_coordUnique
    (β := β) (γ := γ) h₁_assign h₂_assign hcoord

/--
  Длины «упорядоченного» и исходного списков хвостовых присваиваний совпадают,
  как только глобальный список координат покрывает локальную поддержку
  селектора.  Доказательство использует тот факт, что оба списка не содержат
  дубликатов: равенство множеств элементов автоматически переносится на
  `List.length` через `List.toFinset`.
-/
lemma length_selectorTailAssignmentsOrdered_eq_length
    {n : Nat} [DecidableEq (Fin n)] [DecidableEq (BitFix n)]
    {coords : List (Fin n)} {β γ : Subcube n}
    (hnodup : coords.Nodup)
    (hcover : selectorTailSupport (n := n) β γ ⊆ coords.toFinset) :
    (selectorTailAssignmentsOrdered (n := n) coords β γ).length
      = (selectorTailAssignments (n := n) β γ).length := by
  classical
  set ordered := selectorTailAssignmentsOrdered (n := n) coords β γ
  set plain := selectorTailAssignments (n := n) β γ
  have hord_nodup : ordered.Nodup :=
    selectorTailAssignmentsOrdered_nodup
      (n := n) (coords := coords) (β := β) (γ := γ) hnodup
  have hplain_nodup : plain.Nodup :=
    selectorTailAssignments_nodup (n := n) (β := β) (γ := γ)
  have hmem : ∀ pair, pair ∈ ordered ↔ pair ∈ plain :=
    selectorTailAssignmentsOrdered_mem_iff
      (n := n) (coords := coords) (β := β) (γ := γ) hcover
  have hfinset_eq : ordered.toFinset = plain.toFinset := by
    ext pair
    constructor
    · intro hpair
      have : pair ∈ ordered := List.mem_toFinset.mp hpair
      have hplain := (hmem pair).1 this
      exact List.mem_toFinset.mpr hplain
    · intro hpair
      have : pair ∈ plain := List.mem_toFinset.mp hpair
      have hordered := (hmem pair).2 this
      exact List.mem_toFinset.mpr hordered
  have hord_card := List.card_toFinset ordered
  have hplain_card := List.card_toFinset plain
  have hord_len : ordered.length = ordered.toFinset.card := by
    -- В nodup-списке преобразование в `Finset` сохраняет длину.
    simpa [ordered, List.eraseDup_eq_self.mpr hord_nodup] using hord_card
  have hplain_len : plain.length = plain.toFinset.card := by
    simpa [plain, List.eraseDup_eq_self.mpr hplain_nodup] using hplain_card
  have hcard_eq : ordered.toFinset.card = plain.toFinset.card :=
    congrArg Finset.card hfinset_eq
  -- Переносим равенство кардиналов на длины исходных списков.
  simpa [ordered, plain, hord_len, hplain_len] using hcard_eq.symm

/--
  Кардинал локальной хвостовой поддержки можно посчитать как длину
  упорядоченного списка присваиваний.  Это прямое следствие предыдущей леммы
  и известного равенства для «сырого» списка `selectorTailAssignments`.
-/
lemma length_selectorTailAssignmentsOrdered_eq_card_tailSupport
    {n : Nat} [DecidableEq (Fin n)] [DecidableEq (BitFix n)]
    {coords : List (Fin n)} {β γ : Subcube n}
    (hnodup : coords.Nodup)
    (hcover : selectorTailSupport (n := n) β γ ⊆ coords.toFinset) :
    (selectorTailAssignmentsOrdered (n := n) coords β γ).length
      = (selectorTailSupport (n := n) β γ).card := by
  classical
  have hlen := length_selectorTailAssignmentsOrdered_eq_length
    (n := n) (coords := coords) (β := β) (γ := γ) hnodup hcover
  have hcard := length_selectorTailAssignments_eq_card_tailSupport
    (n := n) (β := β) (γ := γ)
  simpa [hlen] using hcard

/--
  Если селектор `γ` фиксирует координату `i`, то либо она уже присутствует в
  осевом листе `β`, либо отображается в списке `selectorTailAssignments β γ`.
  В частности, хвостовые присваивания покрывают все координаты, которые нужно
  дополнительно зафиксировать после прохождения ствола.-/
lemma selectorTailAssignments_support_cover {n : Nat}
    {β γ : Subcube n}
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b)
    {i : Fin n} {b : Bool}
    (hγ : γ i = some b) :
    (β i = some b)
      ∨ ∃ pair ∈ selectorTailAssignments (n := n) β γ, pair = (i, b) := by
  classical
  -- Разбираем значение `β` на рассматриваемой координате.
  cases hβ : β i with
  | none =>
      -- Координата свободна в `β`, значит соответствующее присваивание должно
      -- присутствовать в хвостовом списке.
      have hi_support : i ∈ selectorSupport (n := n) γ :=
        (mem_selectorSupport (n := n) (γ := γ) (i := i)).2 ⟨b, hγ⟩
      obtain ⟨b', hb'⟩ := exists_assignment_for_support
        (n := n) (γ := γ) hi_support
      have hb_eq : b' = b := by
        have hval := (mem_selectorAssignments (n := n) (γ := γ)
            (pair := (i, b'))).1 hb'
        have := Eq.trans (Eq.symm hval) hγ
        exact Option.some.inj this
      refine Or.inr ?_
      refine ⟨(i, b), ?_, by simp [hb_eq]⟩
      have hmem : (i, b') ∈ selectorTailAssignments (n := n) β γ := by
        have := List.mem_filter.mpr ⟨hb', by simpa [hβ]⟩
        simpa [selectorTailAssignments, hb_eq] using this
      simpa [hb_eq] using hmem
  | some bβ =>
      -- Значение уже зафиксировано стволом `β`; по предположению `γ` совпадает.
      have : bβ = b := by
        have hγβ : γ i = some bβ := hsubset (i := i) (b := bβ) hβ
        exact Option.some.inj (by simpa [hγβ] using hγ)
      exact Or.inl (by simpa [hβ, this])

/--
  Каждый селектор из `leafSelectorSet` явно присутствует в списке
  `leafSelectorAssignments` вместе с собственным списком назначений.
-/
lemma mem_leafSelectorAssignments_of_mem_set
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    (γ, selectorAssignments (n := n) γ)
      ∈ leafSelectorAssignments (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ := by
  classical
  unfold leafSelectorAssignments
  -- При отображении списка `leafSelectorSet` функцией `map` каждый элемент
  -- автоматически переходит в пару с соответствующим списком назначений.
  exact List.mem_map.2 ⟨γ, hγ, rfl⟩

/--
  Аналог предыдущей леммы для хвостовых присваиваний: любой селектор из
  `leafSelectorSet` порождает пару в списке `leafSelectorTailAssignments`.
-/
lemma mem_leafSelectorTailAssignments_of_mem_set
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    (γ, selectorTailAssignments (n := n) β γ)
      ∈ leafSelectorTailAssignments (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
  classical
  unfold leafSelectorTailAssignments
  exact List.mem_map.2 ⟨γ, hγ, rfl⟩

/--
  Если пара `(γ, assigns)` принадлежит списку `leafSelectorAssignments`, то
  вторая компонента совпадает с `selectorAssignments γ`.  Лемма позволяет без
  лишних раскрытий переходить от пары к уже известным свойствам списка
  назначений.
-/
lemma mem_leafSelectorAssignments_elim
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorAssignments (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ) :
    entry.2 = selectorAssignments (n := n) entry.1 := by
  classical
  unfold leafSelectorAssignments at hentry
  obtain ⟨γ, hγ, hentry_eq⟩ := List.mem_map.1 hentry
  -- После распаковки пары остаётся лишь свернуть определение назад.
  cases hentry_eq
  simp

/--
  Каждая запись в `leafSelectorAssignments` наследует лемму
  `assignMany_selectorAssignments_self`: последовательное применение
  `Subcube.assignMany` возвращает исходный селектор.
-/
lemma leafSelectorAssignments_assignMany_self
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorAssignments (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) A hβ) :
    Subcube.assignMany entry.1 entry.2 = some entry.1 := by
  classical
  have hassign := mem_leafSelectorAssignments_elim
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := A) (β := β) hβ (entry := entry) hentry
  -- Переписываем по предыдущей лемме и применяем результат
  -- `assignMany_selectorAssignments_self`.
  simpa [hassign]
    using assignMany_selectorAssignments_self (n := n) entry.1

/--
  Эквивалентная формулировка принадлежности через конечное множество:
  элемент входит в `leafSelectorFinset` тогда и только тогда, когда он лежит
  в списке без повторений `leafSelectorSet`.
-/
@[simp] lemma mem_leafSelectorFinset
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) {γ : Subcube n} :
    γ ∈ leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ
      ↔ γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ := by
  classical
  rfl

/--
  Мощность конечного множества селекторов не превышает длину исходного списка
  с повторениями.  Этот простой факт удобен при оценках числа листов, поскольку
  `leafSelectorPool` строится через `List.bind`, где легко получить верхнюю
  границу на длину.
-/
lemma card_leafSelectorFinset_le_pool_length
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    (leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ).card
      ≤ (leafSelectorPool (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ).length := by
  classical
  -- `Finset.card` по определению равна длине списка без повторений, а `dedup`
  -- удаляет лишь дубликаты, поэтому длина не возрастает.
  simpa [leafSelectorFinset, leafSelectorSet]
    using List.length_dedup_le (leafSelectorPool (n := n) (M := M)
      (τ := τ) (w := w) (t := t) (packages := packages) A hβ)

/--
  Любой элемент объединённого пула селекторов порождён некоторой формулой из
  списка `flattenedCNFs`, а значит — конкретным пакетом глубины 1.  Мы явно
  восстанавливаем исходный пакет `pkg`, его принадлежность списку `packages`,
  а также формулу `F ∈ pkg.input.Fs`, которая даёт требуемый селектор.
-/
lemma exists_pkg_mem_of_mem_pool
    {n M τ w t : Nat}
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorPool (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    ∃ (pkg : Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))
      (hmem : pkg ∈ packages)
      (F : Core.CNF n w) (hF : F ∈ pkg.input.Fs),
        γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ)
          (w := w) (t := t) packages A hβ F.eval := by
  classical
  -- Раскрываем определение пула через `List.bind`.
  unfold leafSelectorPool at hγ
  obtain ⟨F, hF_flat, hsel⟩ := List.mem_bind.mp hγ
  -- Формула `F` приходит из некоторого пакета исходного списка `packages`.
  obtain ⟨pkg, hmem_pkg, hF_pkg⟩ :=
    (mem_flattenedCNFs_iff (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) (F := F)).1 hF_flat
  -- Селекторы совпадают с хвостом выбранного пакета.
  refine ⟨pkg, hmem_pkg, F, hF_pkg, ?_⟩
  simpa [leafSelectorPool] using hsel

/--
  Обёртка над предыдущим утверждением: селектор из списка без дубликатов
  `leafSelectorSet` также восстанавливает пакет глубины 1, который его породил.
-/
lemma exists_pkg_mem_of_mem_set
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    ∃ (pkg : Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))
      (hmem : pkg ∈ packages)
      (F : Core.CNF n w) (hF : F ∈ pkg.input.Fs),
        γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ)
          (w := w) (t := t) packages A hβ F.eval := by
  classical
  -- Элемент множества без повторений автоматически принадлежит исходному пулу.
  have hpool : γ ∈ leafSelectorPool (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ := by
    have := List.mem_of_mem_dedup hγ
    simpa [leafSelectorSet] using this
  exact exists_pkg_mem_of_mem_pool (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) (A := A) (β := β) hβ (γ := γ) hpool

/--
  Структура, описывающая, какой именно пакет глубины 1 и какая формула породили
  данный селектор объединённого семейства.  Эти данные понадобятся при
  конструировании глобального хвоста: мы сможем ссылаться на конкретный
  хвостовой сертификат пакета и переиспользовать доказательство принадлежности
  листу.
-/
structure LeafSelectorWitness
    (packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t)))
    (A : Axis n (axisLength n M)) (β γ : Subcube n) : Type _ where
  /-- Пакет глубины 1, в котором встретился селектор `γ`. -/
  pkg : Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t)
  /-- Свидетельство принадлежности пакета списку `packages`. -/
  hmem_pkg : pkg ∈ packages
  /-- Формула из локального списка `pkg.input.Fs`, дающая данный селектор. -/
  F : Core.CNF n w
  /-- Принадлежность формулы пакету. -/
  hF : F ∈ pkg.input.Fs
  /-- Подтверждение того, что рассматриваемый лист действительно относится к
      выбранному пакету. -/
  hβ : β ∈ Axis.leafList (n := n) (ℓ := axisLength n M) A
  /-- Селектор `γ` появляется среди хвостов пакета на оси `A`. -/
  hsel : γ ∈ combinedTailSelectors (n := n) (M := M) (τ := τ)
      (w := w) (t := t) packages A hβ F.eval

attribute [simp] LeafSelectorWitness.hmem_pkg LeafSelectorWitness.hF

/--
  Из элемента множества без повторений `leafSelectorSet` получаем явный
  свидетель пакета и формулы, породивших данный селектор.  Конструкция
  использует классическое соответствие между `flattenedCNFs` и исходными
  пакетами.
-/
noncomputable def chooseLeafSelectorWitness
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    LeafSelectorWitness (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A β γ := by
  classical
  -- Восстанавливаем пакет, формулу и принадлежность селектора.
  obtain ⟨pkg, hmem_pkg, F, hF_pkg, hsel⟩ :=
    exists_pkg_mem_of_mem_set (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) (A := A) (β := β) hβ (γ := γ) hγ
  -- Упаковываем данные в структуру свидетеля.
  refine
    { pkg := pkg
      hmem_pkg := hmem_pkg
      F := F
      hF := hF_pkg
      hβ := hβ
      hsel := by simpa using hsel }

/--
  Уточняем селектор через выбранного пакета: он действительно принадлежит
  локальному хвосту, возвращаемому `pkg.input.build` на той же оси и листе.
-/
lemma chooseLeafSelectorWitness_mem_leaves
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) :
    γ ∈ PDT.leaves
        (((chooseLeafSelectorWitness (n := n) (M := M) (τ := τ)
              (w := w) (t := t) (packages := packages) A hβ hγ).pkg.input.build
            (n := n) (ℓ := axisLength n M) (τ := τ) (w := w) (t := t)
            A β hβ).certificate.witness.realize) := by
  classical
  -- Сохраняем выбранного свидетеля в отдельную переменную для удобства ссылок.
  set W :=
    chooseLeafSelectorWitness (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) A hβ hγ
  -- Применяем лемму о принадлежности селектора листу исходного пакета.
  have hleaf :=
    combinedTailSelectors_mem_of_pkg (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages)
      (pkg := W.pkg) W.hmem_pkg (A := A) (β := β) (hβ := W.hβ)
      (F := W.F) W.hF (γ := γ) W.hsel
  -- Переписываем цель через обозначение `W` и завершаем доказательство.
  simpa [W] using hleaf

/--
  Выбранный свидетель `chooseLeafSelectorWitness` остаётся корректным и после
  расширения бюджета глубины.  Для любого `τTotal ≥ axisLength + τ` селектор
  `γ` попадает в листья хвостового сертификата пакета, перепакованного через
  `packageTailCertificate`.
-/
lemma chooseLeafSelectorWitness_mem_packageTail
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ)
    (τTotal : Nat)
    (hdepth : axisLength n M + τ ≤ τTotal) :
    let W :=
      chooseLeafSelectorWitness (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ hγ
    in
    γ ∈ PDT.leaves
        ((packageTailCertificate (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C W.hmem_pkg τTotal hdepth).certificate.witness
              .realize) := by
  classical
  intro W
  -- Функция `W.F.eval` принадлежит локальному семейству пакета `W.pkg`.
  have hf : W.F.eval ∈ cnfFamily (Fs := W.pkg.input.Fs) := by
    refine (mem_cnfFamily_iff (n := n) (F := W.F)).mpr ?_
    exact ⟨W.F, W.hF, rfl⟩
  -- Переписываем селектор через локальные селекторы выбранного пакета.
  have hsel := W.hsel
  -- После перепаковки в `packageTailCertificate` селектор остаётся листом
  -- соответствующего хвоста.
  have hmem :=
    packageTailCertificate_selectors_mem
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C W.hmem_pkg τTotal hdepth
      (f := W.F.eval) hf (γ := γ)
      (by simpa using hsel)
  simpa using hmem

/-!
### Канонический пакет и хвост для конкретного селектора

Дальнейшим шагам потребуется удобная «обёртка», которая сразу возвращает
пакет глубины 1 и хвостовой сертификат, соответствующие фиксированному
селектору из объединённого множества.  Ниже мы определяем такие вспомогательные
конструкции и фиксируем их ключевые свойства.  Это избавит от повторного
вызова `chooseLeafSelectorWitness` и ручной распаковки его полей в местах,
где достаточно знать, к какому пакету относится селектор и в каком хвостовом
дереве он гарантированно лежит.
-/

/--
  Выбранный пакет глубины 1 для селектора `γ`.  Конструкция просто извлекает
  соответствующее поле из `chooseLeafSelectorWitness`, но оформлена как
  отдельное определение для удобства ссылок.
-/
noncomputable def selectorPackage
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t) :=
  (chooseLeafSelectorWitness (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C.witness.axis hβ hγ).pkg

/-- Свидетельство того, что `selectorPackage` действительно берётся из `packages`. -/
lemma selectorPackage_mem
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    selectorPackage (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ hγ ∈ packages := by
  classical
  unfold selectorPackage
  exact
    (chooseLeafSelectorWitness (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ hγ).hmem_pkg

/--
  Селектор `γ` остаётся листом хвостового сертификата пакета `selectorPackage`
  при любом допустимом расширении бюджета глубины.  Эта форма удобно сочетается
  с последующими конструкциями глобальных хвостов: зная только `γ ∈ leafSelectorSet`,
  можно мгновенно получить соответствующий хвост `packageTailCertificate` и
  ссылку на нужный лист.
-/
lemma selectorPackage_mem_packageTail
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ)
    (τTotal : Nat)
    (hdepth : axisLength n M + τ ≤ τTotal) :
    γ ∈ PDT.leaves
        ((packageTailCertificate (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C
            (selectorPackage_mem (n := n) (M := M) (τ := τ) (w := w) (t := t)
              (packages := packages) C hβ hγ)
            τTotal hdepth).certificate.witness.realize) := by
  classical
  -- Переиспользуем готовую лемму для `chooseLeafSelectorWitness`.
  refine
    chooseLeafSelectorWitness_mem_packageTail (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ hγ τTotal hdepth

/--
  Частный случай предыдущего утверждения: достаточно взять «самосогласованный»
  бюджет `axisLength + τ`.  В практических применениях именно такая граница
  используется для проверки условий индукции, поэтому выносим её в отдельную
  лемму.
-/
lemma selectorPackage_mem_packageTail_selfBound
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    γ ∈ PDT.leaves
        ((packageTailCertificate (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C
            (selectorPackage_mem (n := n) (M := M) (τ := τ) (w := w) (t := t)
              (packages := packages) C hβ hγ)
            (axisLength n M + τ) (Nat.le_refl _)).certificate.witness.realize) :=
  selectorPackage_mem_packageTail (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ hγ (axisLength n M + τ) (Nat.le_refl _)

end CombinedTailCertificate

end MultiSwitching
end ThirdPartyFacts
end Pnp3
/--
  Поддержка (support) селектора: множество координат, которые зафиксированы в
  данном подкубе.  Мы реализуем её как подмножество `Fin n`, фильтруя полный
  набор координат по предикату «значение определено».
-/
noncomputable def selectorSupport {n : Nat} (γ : Subcube n) :
    Finset (Fin n) :=
  (Finset.univ.filter fun i => γ i ≠ none)

/--
  Координата `i` принадлежит поддержке селектора тогда и только тогда, когда в
  подкубе `γ` она фиксирована некоторым булевым значением.
-/
lemma mem_selectorSupport {n : Nat} {γ : Subcube n} {i : Fin n} :
    i ∈ selectorSupport (n := n) γ ↔ ∃ b : Bool, γ i = some b := by
  classical
  unfold selectorSupport
  constructor
  · intro hi
    have hmem := Finset.mem_filter.mp hi
    classical
    cases hγ : γ i with
    | none =>
        have : False := by
          simpa [selectorSupport, hγ] using hmem.2
        exact this.elim
    | some b => exact ⟨b, rfl⟩
  · rintro ⟨b, hb⟩
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ _, by simpa [hb]⟩

/--
  Координата не попадает в поддержку селектора ровно тогда, когда соответствующее
  значение подкуба равно `none`.
-/
lemma not_mem_selectorSupport {n : Nat} {γ : Subcube n} {i : Fin n} :
    i ∉ selectorSupport (n := n) γ ↔ γ i = none := by
  classical
  constructor
  · intro hi
    by_contra hneq
    cases hγ : γ i with
    | none => exact hneq hγ
    | some b =>
        have : i ∈ selectorSupport (n := n) γ :=
          (mem_selectorSupport (n := n) (γ := γ) (i := i)).mpr ⟨b, rfl⟩
        exact (hi this).elim
  · intro hγ hi
    rcases (mem_selectorSupport (n := n) (γ := γ) (i := i)).1 hi with ⟨b, hb⟩
    simpa [hγ] using hb

/--
  Поддержка объединённого набора селекторов: берём `leafSelectorFinset` для
  выбранной оси и листа и объединяем поддержки всех элементов множества.
-/
noncomputable def leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) : Finset (Fin n) :=
  (leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) A hβ).sup (selectorSupport (n := n))

/--
  Принадлежность координаты объединённой поддержке эквивалентна существованию
  селектора из `leafSelectorFinset`, который фиксирует эту координату.
-/
lemma mem_leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) {i : Fin n} :
    i ∈ leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ ↔
      ∃ γ ∈ leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) A hβ,
        i ∈ selectorSupport (n := n) γ := by
  classical
  unfold leafSelectorSupport
  refine Finset.induction_on
    (s := leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ) ?_ ?_
  · simp
  · intro γ s hγ hs ih
    simpa [Finset.sup_cons, ih]

/--
  Для дальнейшей нормализации селекторов удобно иметь явное перечисление всех
  фиксированных координат вместе с назначенными значениями.  Определение ниже
  превращает поддержку `selectorSupport` в список пар `(i, b)`.
  Мы используем `Finset.attach`, чтобы сохранить доказательства принадлежности
  и извлечь соответствующий булевый бит через `Classical.choose`.
-/
noncomputable def selectorAssignments {n : Nat} (γ : Subcube n) :
    List (BitFix n) :=
  ((selectorSupport (n := n) γ).attach.map fun i =>
    let hi : ∃ b : Bool, γ i.1 = some b :=
      (mem_selectorSupport (n := n) (γ := γ) (i := i.1)).1 i.2
    (i.1, Classical.choose hi))

/--
  Любая пара из `selectorAssignments γ` действительно фиксирует соответствующий
  бит в подкубе `γ`.  Лемма будет полезна при конструировании хвостов, поскольку
  позволяет переписывать значения через список назначений.
-/
lemma mem_selectorAssignments {n : Nat} {γ : Subcube n} {pair : BitFix n} :
    pair ∈ selectorAssignments (n := n) γ ↔ γ pair.1 = some pair.2 := by
  classical
  unfold selectorAssignments
  constructor
  · intro hpair
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.1 hpair
    dsimp only
    -- `entry` принадлежит поддержке, значит соответствующий бит определён.
    have := (mem_selectorSupport (n := n) (γ := γ) (i := entry.1)).1 entry.2
    exact Classical.choose_spec this
  · intro hvalue
    -- Координата фиксирована, поэтому она входит в поддержку, а выбранное
    -- значение совпадает с `pair.2`.
    have hmem : pair.1 ∈ selectorSupport (n := n) γ :=
      (mem_selectorSupport (n := n) (γ := γ) (i := pair.1)).2 ⟨pair.2, hvalue⟩
    refine List.mem_map.2 ?_
    refine ⟨⟨pair.1, hmem⟩, ?_, ?_⟩
    · -- Пара из `Finset.attach` действительно фигурирует в списке.
      simpa using (Finset.mem_attach (s := selectorSupport (n := n) γ) hmem)
    · -- После извлечения через `Classical.choose` получаем исходную пару.
      simp [hmem, hvalue]

/--
  Количество пар в `selectorAssignments` совпадает с размером поддержки
  `selectorSupport`.  В частности, список не содержит повторов по координатам.
-/
lemma length_selectorAssignments {n : Nat} (γ : Subcube n) :
    (selectorAssignments (n := n) γ).length
      = (selectorSupport (n := n) γ).card := by
  classical
  unfold selectorAssignments
  -- `Finset.attach` даёт список длины, равной мощности конечного множества.
  simpa [selectorAssignments] using
    (List.length_map (selectorSupport (n := n) γ).attach
      (fun i : (selectorSupport (n := n) γ).attach =>
        (i.1, Classical.choose
          ((mem_selectorSupport (n := n) (γ := γ) (i := i.1)).1 i.2))))

/--
  Список назначений не содержит дубликатов: каждая координата поддержки
  встречается ровно один раз.  Это следует из того, что `Finset.attach`
  возвращает список без повторов, а отображение в пары `(i, b)` сохраняет
  различимость индексов.
-/
lemma selectorAssignments_nodup {n : Nat} (γ : Subcube n) :
    (selectorAssignments (n := n) γ).Nodup := by
  classical
  unfold selectorAssignments
  -- Определяем вспомогательное отображение из элементов `attach` в пары `(i, b)`.
  set f : (selectorSupport (n := n) γ).attach → BitFix n :=
    fun i =>
      (i.1, Classical.choose
        ((mem_selectorSupport (n := n) (γ := γ) (i := i.1)).1 i.2))
  -- Список `attach` не содержит повторов, поэтому достаточно проверить
  -- инъективность отображения `f` на этом списке.
  have hattach :
      ((selectorSupport (n := n) γ).attach).Nodup :=
    (selectorSupport (n := n) γ).nodup_attach
  have hf : ∀ {a b},
      a ∈ (selectorSupport (n := n) γ).attach →
      b ∈ (selectorSupport (n := n) γ).attach →
      f a = f b → a = b := by
    intro a b ha hb hmap
    apply Subtype.ext
    simpa [f] using congrArg Prod.fst hmap
  simpa [selectorAssignments, f]
    using List.nodup_map (f := f) hattach hf

/--
  Список `selectorAssignments` не содержит двух различных пар, фиксирующих одну
  и ту же координату.  Если индексы совпадают, совпадает и пара целиком.  Это
  напрямую следует из того, что подкуб `γ` задаёт единственное значение на
  каждой определённой координате.-/
lemma selectorAssignments_coordUnique {n : Nat} {γ : Subcube n}
    {pair₁ pair₂ : BitFix n}
    (h₁ : pair₁ ∈ selectorAssignments (n := n) γ)
    (h₂ : pair₂ ∈ selectorAssignments (n := n) γ)
    (hcoord : pair₁.1 = pair₂.1) :
    pair₁ = pair₂ := by
  classical
  -- Получаем значения, которые `γ` фиксирует на указанных координатах.
  have hval₁ : γ pair₁.1 = some pair₁.2 :=
    (mem_selectorAssignments (n := n) (γ := γ) (pair := pair₁)).1 h₁
  have hval₂ : γ pair₂.1 = some pair₂.2 :=
    (mem_selectorAssignments (n := n) (γ := γ) (pair := pair₂)).1 h₂
  -- Переписываем первое равенство через индекс `pair₂.1`.
  have hval₁' : γ pair₂.1 = some pair₁.2 := by
    simpa [hcoord] using hval₁
  -- На одной координате `γ` хранит ровно одно значение, значит биты совпадают.
  have hbit : pair₁.2 = pair₂.2 := by
    have := Eq.trans (Eq.symm hval₁') hval₂
    exact Option.some.inj this
  -- Индексы тоже равны, следовательно пары совпадают целиком.
  cases pair₁
  cases pair₂
  cases hcoord
  cases hbit
  simp

/--
  Каждая координата из поддержки встречается в `selectorAssignments`.  Мы
  возвращаем точное значение, которое фиксирует подкуб `γ` на этой координате.
-/
lemma exists_assignment_for_support {n : Nat} {γ : Subcube n} {i : Fin n}
    (hi : i ∈ selectorSupport (n := n) γ) :
    ∃ b : Bool, (i, b) ∈ selectorAssignments (n := n) γ := by
  classical
  obtain ⟨b, hb⟩ := (mem_selectorSupport (n := n) (γ := γ) (i := i)).1 hi
  refine ⟨b, ?_⟩
  have hvalue : γ i = some b := hb
  simpa [mem_selectorAssignments, hvalue]

/--
  Если координата не лежит в поддержке селектора, то ни одна пара из
  `selectorAssignments` не фиксирует её.  Это позволяет безопасно перебирать
  список назначений, не опасаясь лишних координат.
-/
lemma not_mem_selectorAssignments {n : Nat} {γ : Subcube n} {i : Fin n}
    (hi : i ∉ selectorSupport (n := n) γ) :
    (∀ b : Bool, (i, b) ∉ selectorAssignments (n := n) γ) := by
  classical
  intro b
  have hvalue : γ i = none := (not_mem_selectorSupport (n := n) (γ := γ) (i := i)).1 hi
  intro hmem
  have := (mem_selectorAssignments (n := n) (γ := γ) (pair := (i, b))).1 hmem
  simpa [hvalue] using this

/--
  Если последовательность присваиваний согласована с подкубом `γ`, то повторное
  применение `Subcube.assignMany` к `γ` ничего не меняет.  Лемма понадобится при
  восстановлении исходных селекторов из списков назначений.
-/
lemma assignMany_eq_self_of_mem
    {n : Nat} {γ : Subcube n} {updates : List (BitFix n)}
    (hmem : ∀ pair ∈ updates, γ pair.1 = some pair.2) :
    Subcube.assignMany γ updates = some γ := by
  classical
  induction updates with
  | nil =>
      simpa using (Subcube.assignMany_nil (β := γ))
  | cons pair rest ih =>
      rcases pair with ⟨i, b⟩
      have hi : γ i = some b := hmem (i, b) (by simp)
      have hassign : Subcube.assign γ i b = some γ := by
        unfold Subcube.assign
        simpa [hi]
      have hrest : Subcube.assignMany γ rest = some γ := by
        apply ih
        intro pair hpair
        exact hmem pair (by
          have := Or.inr hpair
          simpa using this)
      simp [Subcube.assignMany, hassign, hrest]

/--
  Список `selectorAssignments γ` фиксирует все определённые координаты подкуба,
  поэтому его повторное применение через `Subcube.assignMany` возвращает `γ`.
-/
lemma assignMany_selectorAssignments_self {n : Nat} (γ : Subcube n) :
    Subcube.assignMany γ (selectorAssignments (n := n) γ) = some γ := by
  classical
  apply assignMany_eq_self_of_mem
  intro pair hpair
  exact (mem_selectorAssignments (n := n) (γ := γ) (pair := pair)).1 hpair

/--
  Любая фиксированная координата конкретного селектора входит в объединённую
  поддержку для выбранного листа оси.  На практике это означает, что
  глобальная поддержка `leafSelectorSupport` действительно охватывает все
  локальные селекторы, появляющиеся при нормализации хвостов.
-/
lemma selectorSupport_subset_leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    selectorSupport (n := n) γ ⊆
      leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ := by
  classical
  intro i hi
  refine (mem_leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C.witness.axis hβ).2 ?_
  refine ⟨γ, ?_, ?_⟩
  · simpa using
      (mem_leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ).2 hγ
  · simpa using hi

/--
  Любой элемент списка `selectorAssignments` фиксирует координату, лежащую в
  глобальной поддержке `leafSelectorSupport`.  Лемма показывает, что в процессе
  нормализации мы никогда не выйдем за пределы объединённой поддержки.
-/
lemma selectorAssignments_subset_leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    ∀ pair ∈ selectorAssignments (n := n) γ,
      pair.1 ∈ leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ := by
  classical
  intro pair hpair
  have hmem : γ pair.1 = some pair.2 :=
    (mem_selectorAssignments (n := n) (γ := γ) (pair := pair)).1 hpair
  have hsupp : pair.1 ∈ selectorSupport (n := n) γ :=
    (mem_selectorSupport (n := n) (γ := γ) (i := pair.1)).2 ⟨pair.2, hmem⟩
  exact selectorSupport_subset_leafSelectorSupport
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C hβ hγ hsupp

/--
  Технический лемматор: если список присваиваний `updates` фиксирует каждый
  бит в строгом соответствии с подкубом `γ`, не конфликтует с уже заданными
  значениями подкуба `β`, а любое значение `γ` либо уже присутствует в `β`,
  либо описывается одной из пар `updates`, то последовательное применение
  `Subcube.assignMany` восстанавливает подкуб `γ`.  Условие `coordUnique`
  гарантирует, что в списке нет двух различных записей, фиксирующих одну и ту
  же координату, что в дальнейшем выполняется автоматически для
  `selectorTailAssignments` благодаря лемме `selectorTailAssignments_nodup`.
-/
lemma assignMany_recover_subcube
    {n : Nat} {β γ : Subcube n} {updates : List (BitFix n)}
    (hnodup : updates.Nodup)
    (coordUnique : ∀ {p₁ p₂ : BitFix n},
        p₁ ∈ updates → p₂ ∈ updates → p₁.1 = p₂.1 → p₁ = p₂)
    (hvalues : ∀ {pair : BitFix n}, pair ∈ updates → γ pair.1 = some pair.2)
    (hfree : ∀ {pair : BitFix n}, pair ∈ updates → β pair.1 = none)
    (hsupport : ∀ {i : Fin n} {b : Bool}, γ i = some b →
        (β i = some b) ∨ ∃ pair ∈ updates, pair = (i, b))
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    Subcube.assignMany β updates = some γ := by
  classical
  induction updates with
  | nil =>
      -- Пустой список не накладывает ограничений, поэтому `β = γ`.
      have : β = γ := by
        funext i
        classical
        by_cases hβ : β i = none
        · -- Пустая программа присваиваний не добавляет ограничений к свободной координате.
          -- Если бы `γ` фиксировала её, то `hsupport` потребовал бы соответствующего
          -- элемента в `updates`, что невозможно.
          have : γ i = none := by
            by_contra hcontr
            obtain ⟨b, hb⟩ := Option.ne_none_iff_exists.mp hcontr
            have := hsupport (i := i) (b := b) (by simpa [hb])
            -- Вторая альтернатива невозможна, а первая противоречит `hβ`.
            cases this with
            | inl hfixed => exact (Option.noConfusion (by simpa [hβ] using hfixed))
            | inr hmem =>
                rcases hmem with ⟨pair, hpair, _⟩
                simpa using hpair
          simpa [hβ, this]
        · -- Если координата уже фиксирована в `β`, `γ` содержит то же значение.
          obtain ⟨b, hβVal⟩ := Option.ne_none_iff_exists.mp (by simpa [hβ] : β i ≠ none)
          have := hsubset (i := i) (b := b) hβVal
          simpa [hβVal]
      simpa [Subcube.assignMany, this]
  | cons pair rest ih =>
      have hcons := List.nodup_cons.mp hnodup
      have hpair_notin : pair ∉ rest := hcons.1
      have hnodup_rest : rest.Nodup := hcons.2
      have hβ_none : β pair.1 = none :=
        hfree (pair := pair) (by simp)
      have hγ_value : γ pair.1 = some pair.2 :=
        hvalues (pair := pair) (by simp)
      -- Присваивание совместимо: получаем новый подкуб `β₁`.
      have hassign := by
        simpa [Subcube.assign, hβ_none]
          using (show Subcube.assign β pair.1 pair.2
              = some (fun j => if j = pair.1 then some pair.2 else β j) from
              by simp [Subcube.assign, hβ_none])
      -- Вводим обозначение для промежуточного подкуба.
      set β₁ : Subcube n := fun j => if j = pair.1 then some pair.2 else β j
      have hassign_simp : Subcube.assign β pair.1 pair.2 = some β₁ := by
        simpa [β₁] using hassign
      -- Уточняем предпосылки для хвоста списка.
      have hcoord_rest : ∀ {p₁ p₂ : BitFix n},
          p₁ ∈ rest → p₂ ∈ rest → p₁.1 = p₂.1 → p₁ = p₂ := by
        intro p₁ p₂ hp₁ hp₂ hidx
        have hp₁' : p₁ ∈ pair :: rest := by exact List.mem_cons_of_mem _ hp₁
        have hp₂' : p₂ ∈ pair :: rest := by exact List.mem_cons_of_mem _ hp₂
        have := coordUnique (p₁ := p₁) (p₂ := p₂) hp₁' hp₂' hidx
        -- Проверяем, что ни один из элементов не совпадает с `pair`.
        have hp₁_ne : p₁ ≠ pair := by
          intro hcontr
          subst hcontr
          exact hpair_notin hp₁
        have hp₂_ne : p₂ ≠ pair := by
          intro hcontr
          subst hcontr
          exact hpair_notin hp₂
        cases this with
        | rfl => rfl
      have hvalues_rest : ∀ {pair' : BitFix n},
          pair' ∈ rest → γ pair'.1 = some pair'.2 := by
        intro pair' hmem
        exact hvalues (pair := pair') (by exact List.mem_cons_of_mem _ hmem)
      have hfree_rest : ∀ {pair' : BitFix n},
          pair' ∈ rest → β₁ pair'.1 = none := by
        intro pair' hmem
        have hp'ne : pair'.1 ≠ pair.1 := by
          intro hidx
          have hpair' := coordUnique
              (p₁ := pair') (p₂ := pair)
              (by exact List.mem_cons_of_mem _ hmem)
              (by simp)
              hidx
          have : pair' = pair := by
            -- `coordUnique` возвращает равенство, но нам важно, что `pair`
            -- не встречается в `rest`.
            simpa using hpair'
          subst this
          exact hpair_notin hmem
        -- Для остальных координат значение совпадает с исходным `β`.
        have : pair'.1 ≠ pair.1 := hp'ne
        simp [β₁, this, hfree (pair := pair') (by exact List.mem_cons_of_mem _ hmem)]
      have hsupport_rest : ∀ {i : Fin n} {b : Bool}, γ i = some b →
          (β₁ i = some b) ∨ ∃ pair' ∈ rest, pair' = (i, b) := by
        intro i b hi
        have base := hsupport (i := i) (b := b) hi
        rcases base with hβ | ⟨pair', hmem, hpair_eq⟩
        · by_cases hi_idx : i = pair.1
          · subst hi_idx
            -- На координате `pair.1` новое значение совпадает с `γ`.
            have : b = pair.2 := by
              apply Option.some.inj
              simpa [hi_idx] using hγ_value.trans hi.symm
            subst this
            simp [β₁]
          · have : β₁ i = some b := by
              simp [β₁, hi_idx, hβ]
            exact Or.inl this
        · -- Если значение задаётся списком `updates`, то либо это голова,
          -- либо элемент хвоста.
          have hmem_cons : pair' ∈ pair :: rest := by
            simpa using hmem
          have hpair_cases : pair' = pair ∨ pair' ∈ rest := by
            simpa [List.mem_cons] using hmem_cons
          cases hpair_cases with
          | inl hpair_eq =>
              -- Совпадает с головой списка: координата та же, что у `pair`.
              subst hpair_eq
              have : i = pair.1 := by
                apply congrArg Prod.fst
                simpa using hpair_eq
              subst this
              have hb : b = pair.2 := by
                apply congrArg Prod.snd
                simpa using hpair_eq
              subst hb
              left
              simp [β₁]
          | inr hrest_mem =>
              right
              exact ⟨pair', hrest_mem, hpair_eq⟩
      have hsubset_rest : ∀ {i : Fin n} {b : Bool},
          β₁ i = some b → γ i = some b := by
        intro i b hi
        by_cases hi_idx : i = pair.1
        · subst hi_idx
          have : b = pair.2 := by
            -- Из определения `β₁` значение на `pair.1` фиксируется как `pair.2`.
            simpa [β₁] using hi
          subst this
          exact hγ_value
        · have hβ : β i = some b := by
            simpa [β₁, hi_idx] using hi
          exact hsubset (i := i) (b := b) hβ
      -- Применяем индуктивное предположение к хвосту списка.
      have ih_app := ih hnodup_rest hcoord_rest hvalues_rest hfree_rest
        hsupport_rest hsubset_rest
      -- Собираем итоговое выражение.
      simpa [Subcube.assignMany, hassign_simp] using ih_app


/--
  Длина списка `selectorAssignments` не превосходит размера объединённой
  поддержки `leafSelectorSupport`.  Следовательно, при построении будущего
  глобального хвоста нам достаточно работать с конечным числом координат,
  контролируемым единым бюджетом глубины.
-/
lemma length_selectorAssignments_le_leafSelectorSupport
    {n M τ w t : Nat} [DecidableEq (Subcube n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ) :
    (selectorAssignments (n := n) γ).length ≤
      (leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ).card := by
  classical
  have hsubset := selectorSupport_subset_leafSelectorSupport
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C hβ hγ
  have hcard :=
    Finset.card_le_of_subset hsubset
  simpa [length_selectorAssignments] using hcard

/--
  Применение `Subcube.assignMany` к осевому листу `β` по списку
  `selectorTailAssignments β γ` восстанавливает селектор `γ`.  Предположение
  `hsubset` гарантирует, что `γ` действительно расширяет `β` по уже зафиксированным
  координатам, а добавочные значения берутся из хвостового списка.-/
lemma assignMany_selectorTailAssignments {n : Nat}
    {β γ : Subcube n}
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    Subcube.assignMany β (selectorTailAssignments (n := n) β γ) = some γ := by
  classical
  refine assignMany_recover_subcube
    (β := β) (γ := γ)
    (updates := selectorTailAssignments (n := n) β γ)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact selectorTailAssignments_nodup (β := β) (γ := γ)
  · intro p₁ p₂ hp₁ hp₂ hcoord
    exact selectorTailAssignments_coordUnique
      (β := β) (γ := γ) hp₁ hp₂ hcoord
  · intro pair hpair
    exact (mem_selectorAssignments (n := n) (γ := γ) (pair := pair)).1
      (selectorTailAssignments_subset_assignments (β := β) (γ := γ) hpair)
  · intro pair hpair
    exact selectorTailAssignments_coord_free (β := β) (γ := γ) hpair
  · intro i b hγ
    exact selectorTailAssignments_support_cover (n := n)
      (β := β) (γ := γ) hsubset (i := i) (b := b) hγ
  · exact hsubset

/--
  Уточнение предыдущего результата: если список `selectorTailAssignments β γ`
  непуст, то его голову можно выделить в явную пару `pair`, после чего
  применение `Subcube.assign` к `β` успешно переходит в промежуточный подкуб,
  а оставшиеся присваивания восстанавливают селектор `γ`.
-/
lemma selectorTailAssignments_cons_assign {n : Nat}
    {β γ : Subcube n}
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b)
    {pair : BitFix n} {rest : List (BitFix n)}
    (hcons : selectorTailAssignments (n := n) β γ = pair :: rest) :
    ∃ β', Subcube.assign β pair.1 pair.2 = some β'
        ∧ Subcube.assignMany β' rest = some γ := by
  classical
  have hassign := assignMany_selectorTailAssignments
    (n := n) (β := β) (γ := γ) (hsubset := hsubset)
  -- Подставляем представление списка с явно выделенной головой.
  have : Subcube.assignMany β (pair :: rest) = some γ := by
    simpa [hcons] using hassign
  cases hstep : Subcube.assign β pair.1 pair.2 with
  | none =>
      -- Противоречие: успешное применение `assignMany` невозможно, если одно из
      -- присваиваний уже конфликтует с базовым подкубом.
      simp [Subcube.assignMany, hcons, hstep] at this
  | some β' =>
      have htail : Subcube.assignMany β' rest = some γ := by
        simpa [Subcube.assignMany, hcons, hstep] using this
      exact ⟨β', hstep, htail⟩

/--
  Если список хвостовых присваиваний пуст, то селектор `γ` совпадает с базовым
  листом `β`.  Обратное также верно: когда `γ = β`, дополнительных присваиваний
  не требуется, поэтому `selectorTailAssignments` возвращает пустой список.
  Гипотеза `hsubset` зафиксирует стандартное условие «`γ` расширяет `β` на
  уже определённых координатах» и автоматически выполняется для селекторов,
  полученных из хвостовых сертификатов пакетов глубины 1.
-/
lemma selectorTailAssignments_eq_nil_iff
    {n : Nat} [DecidableEq (Fin n)]
    {β γ : Subcube n}
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    selectorTailAssignments (n := n) β γ = [] ↔ γ = β := by
  classical
  constructor
  · intro hnil
    funext i
    cases hβ : β i with
    | none =>
        -- Показываем, что координата также свободна в `γ`.
        classical
        by_contra hγ
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hγ
        have hcover := selectorTailAssignments_support_cover
          (n := n) (β := β) (γ := γ)
          (hsubset := hsubset) (i := i) (b := b) (hγ := hb)
        cases hcover with
        | inl hcontr =>
            simp [hβ] at hcontr
        | inr hmem =>
            -- Противоречие: список хвостовых присваиваний пуст.
            simp [selectorTailAssignments, hnil] at hmem
        -- Значит `γ i = none`.
        simp [hβ]
    | some b =>
        -- На зафиксированной координате значения совпадают благодаря `hsubset`.
        exact (hsubset (i := i) (b := b) hβ)
  · intro hγβ
    subst hγβ
    -- В списке `selectorAssignments β` каждая пара фиксирует координату
    -- ствола, поэтому условие фильтра никогда не выполняется.
    unfold selectorTailAssignments
    refine List.filter_eq_nil.2 ?_
    intro pair hpair
    have hvalue := (mem_selectorAssignments (n := n) (γ := β)
      (pair := pair)).1 hpair
    -- Присваивание фильтруется, потому что соответствующая координата уже
    -- зафиксирована в `β` и не может равняться `none`.
    simp [hvalue]

/--
  Небольшой пакет данных, сопоставляющий селектору `γ` список хвостовых
  присваиваний и фиксирующий ключевые инварианты, доказанные выше.  Такие
  пакеты будут использованы при построении единого хвоста для объединённого
  семейства CNF.
-/
structure TailAssignmentBundle (n : Nat) (β γ : Subcube n) where
  /-- Последовательность присваиваний, превращающая `β` в `γ`. -/
  assignments : List (BitFix n)
  /-- Последовательное применение действительно восстанавливает селектор. -/
  assignMany_eq : Subcube.assignMany β assignments = some γ
  /-- В списке нет дубликатов пар `(i, b)`. -/
  nodup : assignments.Nodup
  /-- Каждая координата встречается не более одного раза. -/
  coord_unique : ∀ {pair₁ pair₂},
      pair₁ ∈ assignments → pair₂ ∈ assignments →
        pair₁.1 = pair₂.1 → pair₁ = pair₂
  /-- Любое присваивание воздействует на свободную координату `β`. -/
  coord_free : ∀ {pair}, pair ∈ assignments → β pair.1 = none

namespace TailAssignmentBundle

variable {n : Nat} {β γ : Subcube n}

/--
  Для селектора `γ` из `leafSelectorSet` мы можем явно извлечь список
  присваиваний `updates`, который реконструирует `γ` из осевого листа `β`,
  использует только координаты глобальной хвостовой поддержки
  `leafSelectorTailSupport`.  Предположение `hsubset` фиксирует стандартное
  условие «`γ` уточняет `β` на уже установленных координатах»; в дальнейшем оно
  будет выводиться из свойств пакетного сертификата.-/
lemma exists_assignments_of_leafSelector
    {M τ w t : Nat} [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    {A : Axis n (axisLength n M)}
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A)
    {γ : Subcube n}
    (hγ : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A hβ)
    (hsubset : ∀ {i : Fin n} {b : Bool}, β i = some b → γ i = some b) :
    ∃ updates : List (BitFix n),
      updates.Nodup ∧
        (∀ pair ∈ updates,
            pair.1 ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
              (w := w) (t := t) (packages := packages) A hβ) ∧
        (∀ pair ∈ updates, β pair.1 = none) ∧
        Subcube.assignMany β updates = some γ := by
  classical
  refine ⟨selectorTailAssignments (n := n) β γ,
    selectorTailAssignments_nodup (n := n) (β := β) (γ := γ), ?subset, ?free, ?assign⟩
  · intro pair hpair
    -- Прежде всего переводим принадлежность к хвостовым присваиваниям
    -- в факт о локальной поддержке конкретного селектора.
    have htail_mem : pair.1 ∈ selectorTailSupport (n := n) β γ := by
      refine (mem_selectorTailSupport (n := n) (β := β) (γ := γ)
        (i := pair.1)).2 ?_
      refine ⟨pair.2, ?_⟩
      simpa using hpair
    -- Локальная поддержка любого селектора включена в глобальную хвостовую
    -- поддержку — это следует из принадлежности пары списку
    -- `leafSelectorTailAssignments`.
    have hentry :
        (γ, selectorTailAssignments (n := n) β γ)
          ∈ leafSelectorTailAssignments (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) A hβ :=
      mem_leafSelectorTailAssignments_of_mem_set
        (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) (A := A) (β := β) hβ hγ
    have hsubset :=
      selectorTailSupport_subset_leafSelectorTailSupport
        (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) A (β := β) hβ
        (entry := (γ, selectorTailAssignments (n := n) β γ)) hentry
    exact hsubset htail_mem
  · intro pair hpair
    exact selectorTailAssignments_coord_free (β := β) (γ := γ)
      (pair := pair) hpair
  · simpa using assignMany_selectorTailAssignments (n := n) (β := β)
      (γ := γ) (hsubset := hsubset)

lemma mem_leaves_toPDT
    (bundle : TailAssignmentBundle (n := n) β γ) :
    γ ∈ PDT.leaves (TailAssignmentBundle.toPDT
      (n := n) (β := β) (γ := γ) bundle) := by
  classical
  -- Индукция по длине списка `assignments`.
  refine (Nat.rec (motive := fun m => ∀ {β γ}
      {bundle : TailAssignmentBundle (n := n) β γ},
        bundle.assignments.length = m →
          γ ∈ PDT.leaves (TailAssignmentBundle.toPDT
            (n := n) (β := β) (γ := γ) bundle))
    (by
      -- База: список присваиваний пуст.
      intro β γ bundle hlen
      have hnil : bundle.assignments = [] := by
        have : bundle.assignments.length = 0 := by simpa using hlen
        exact (List.length_eq_zero.mp this)
      -- Получаем `γ = β` из свойства `assignMany_eq`.
      have hassign := bundle.assignMany_eq
      have hβγ : β = γ := by
        simpa [hnil, Subcube.assignMany] using hassign
      have hγβ : γ = β := hβγ.symm
      -- При пустом списке `toPDT` возвращает лист `β`.
      have hpop : bundle.popHead = none :=
        (TailAssignmentBundle.popHead_eq_none
          (n := n) (β := β) (γ := γ) bundle).2 hnil
      -- Теперь упрощаем определение дерева и проверяем принадлежность листу.
      have htree : TailAssignmentBundle.toPDT
          (n := n) (β := β) (γ := γ) bundle = PDT.leaf β := by
        -- В ветке `none` дерево сводится к единственному листу `β`.
        simpa [TailAssignmentBundle.toPDT, hpop, hnil, hγβ]
      simpa [htree, hγβ] using List.mem_singleton_self β)
    (by
      -- Переход: список непуст, снимаем голову и применяем ИГ к хвосту.
      intro m ih β γ bundle hlen
      classical
      cases hassign : bundle.assignments with
      | nil =>
          -- Противоречие: длина непустого списка не может быть нулевой.
          have : (0 : Nat) = Nat.succ m := by
            simpa [hassign] using hlen
          cases this
      | cons pair rest =>
          -- Длина хвоста равна `m`.
          have hlen_rest : rest.length = m := by
            simpa [hassign] using
              Nat.succ.inj (by simpa [hassign] using hlen)
          -- Уточняем результат `popHead` и выписываем соответствующий шаг.
          have hpop_none : bundle.popHead ≠ none := by
            intro hnone
            have hcontra :=
              (TailAssignmentBundle.popHead_eq_none
                (n := n) (β := β) (γ := γ) bundle).1 hnone
            simpa [hassign] using hcontra
          cases hstep : bundle.popHead with
          | none => exact (hpop_none hstep).elim
          | some step =>
              -- Связь между данными шага и исходным списком.
              obtain ⟨pair', rest', hassign', hp, htail⟩ :=
                TailAssignmentBundle.popHead_eq_some
                  (n := n) (β := β) (γ := γ)
                  (bundle := bundle) (step := step) hstep
              -- Списки совпадают, поэтому `pair' = pair`, `rest' = rest`.
              have hcons := by
                simpa [hassign] using hassign'
              obtain ⟨hp_eq, hrest_eq⟩ := List.cons.inj hcons
              -- Переписываем данные шага через известные равенства.
              subst hp_eq
              subst hrest_eq
              -- Индуктивная гипотеза для хвоста.
              have htail_len :
                  step.tail.assignments.length = m := by
                simpa [htail] using hlen_rest
              have hmem_tail : γ ∈ PDT.leaves
                  (TailAssignmentBundle.toPDT
                    (n := n) (β := step.next) (γ := γ) step.tail) :=
                ih (β := step.next) (γ := γ)
                  (bundle := step.tail) htail_len
              -- Обозначения для ветвей дерева.
              set tailTree := TailAssignmentBundle.toPDT
                (n := n) (β := step.next) (γ := γ) step.tail with htailTree
              set zeroBranch := if step.pair.2 = false then tailTree
                  else PDT.leaf (fun j : Fin n => if j = step.pair.1 then
                      some (Bool.not step.pair.2) else β j) with hzero
              set oneBranch := if step.pair.2 = true then tailTree
                  else PDT.leaf (fun j : Fin n => if j = step.pair.1 then
                      some (Bool.not step.pair.2) else β j) with hone
              -- Переписываем цель через явное выражение для `toPDT`.
              have htree : TailAssignmentBundle.toPDT
                  (n := n) (β := β) (γ := γ) bundle
                  = PDT.node step.pair.1 zeroBranch oneBranch := by
                have hpair_val := show step.pair = pair from by
                  -- После подстановок `pair` совпадает со `step.pair`.
                  simpa using hp
                -- Упрощаем определение `toPDT`.
                simp [TailAssignmentBundle.toPDT, hstep, hassign,
                  hpair_val, hzero, hone, htailTree]
              -- Завершаем: `γ` принадлежит объединению листьев узла.
              have hnode_mem : γ ∈ PDT.leaves
                  (PDT.node step.pair.1 zeroBranch oneBranch) := by
                -- Ветви обрабатываются через стандартную формулу для листьев узла.
                classical
                cases step.pair.2 with
                | false =>
                    have : γ ∈ PDT.leaves zeroBranch := by
                      simpa [hzero] using hmem_tail
                    have hmem_append : γ ∈
                        (PDT.leaves zeroBranch)
                          ++ (PDT.leaves oneBranch) :=
                      List.mem_append.mpr (Or.inl this)
                    simpa [PDT.leaves, hzero, hone]
                      using hmem_append
                | true =>
                    have : γ ∈ PDT.leaves oneBranch := by
                      simpa [hone] using hmem_tail
                    have hmem_append : γ ∈
                        (PDT.leaves zeroBranch)
                          ++ (PDT.leaves oneBranch) :=
                      List.mem_append.mpr (Or.inr this)
                    simpa [PDT.leaves, hzero, hone]
                      using hmem_append
              simpa [htree] using hnode_mem))
    (bundle.assignments.length) rfl

/--
  Глубина дерева, построенного `TailAssignmentBundle.toPDT`, ограничена длиной
  исходного списка присваиваний.  Доказательство повторяет индукцию из
  предыдущей леммы и использует тот факт, что при разборе головы список
  хвостовых присваиваний укорачивается на один элемент.-/
lemma depth_toPDT_le_length
    (bundle : TailAssignmentBundle (n := n) β γ) :
    PDT.depth (TailAssignmentBundle.toPDT
      (n := n) (β := β) (γ := γ) bundle)
      ≤ bundle.assignments.length := by
  classical
  -- Индукция по длине списка присваиваний.
  refine (Nat.rec (motive := fun m => ∀ {β γ}
      {bundle : TailAssignmentBundle (n := n) β γ},
        bundle.assignments.length = m →
          PDT.depth (TailAssignmentBundle.toPDT
            (n := n) (β := β) (γ := γ) bundle) ≤ m)
    (by
      -- Пустой список: дерево состоит из одного листа, глубина равна нулю.
      intro β γ bundle hlen
      have hnil : bundle.assignments = [] := by
        have : bundle.assignments.length = 0 := by simpa using hlen
        exact List.length_eq_zero.mp this
      have htree : TailAssignmentBundle.toPDT
          (n := n) (β := β) (γ := γ) bundle = PDT.leaf β := by
        simpa [TailAssignmentBundle.toPDT, hnil]
          using (TailAssignmentBundle.popHead_eq_none
            (n := n) (β := β) (γ := γ) bundle).mpr hnil
      simpa [htree, hlen, hnil]
        using (Nat.zero_le 0 : (0 : Nat) ≤ 0))
    (by
      intro m ih β γ bundle hlen
      classical
      -- Список непуст: снимаем голову и применяем предположение индукции.
      cases hassign : bundle.assignments with
      | nil =>
          have : (0 : Nat) = Nat.succ m := by
            simpa [hassign] using hlen
          cases this
      | cons pair rest =>
          -- Длина хвоста равна `m`.
          have hlen_rest : rest.length = m := by
            simpa [hassign] using
              Nat.succ.inj (by simpa [hassign] using hlen)
          -- Раскрываем результат `popHead`.
          have hpop : bundle.popHead ≠ none := by
            intro hnone
            have := (TailAssignmentBundle.popHead_eq_none
              (n := n) (β := β) (γ := γ) bundle).1 hnone
            simpa [hassign] using this
          cases hstep : bundle.popHead with
          | none => exact (hpop hstep).elim
          | some step =>
              obtain ⟨pair', rest', hassign', hp, htail⟩ :=
                TailAssignmentBundle.popHead_eq_some
                  (n := n) (β := β) (γ := γ)
                  (bundle := bundle) (step := step) hstep
              have hcons := by simpa [hassign] using hassign'
              obtain ⟨hpair_eq, hrest_eq⟩ := List.cons.inj hcons
              subst hpair_eq
              subst hrest_eq
              -- Применяем предположение индукции к хвостовому пакету.
              have htail_len :
                  step.tail.assignments.length = m := by
                simpa [htail] using hlen_rest
              have hdepth_tail : PDT.depth
                  (TailAssignmentBundle.toPDT
                    (n := n) (β := step.next) (γ := γ) step.tail)
                    ≤ m :=
                ih (β := step.next) (γ := γ)
                  (bundle := step.tail) htail_len
              -- Глубина листовых ветвей не превосходит глубины хвоста.
              have hdepth_zero :
                  PDT.depth
                      (if step.pair.2 = false then
                          TailAssignmentBundle.toPDT
                            (n := n) (β := step.next) (γ := γ) step.tail
                        else
                          PDT.leaf
                            (fun j : Fin n =>
                              if j = step.pair.1 then
                                some (Bool.not step.pair.2)
                              else β j))
                    ≤ m := by
                split_ifs
                · simpa using hdepth_tail
                · have : (0 : Nat) ≤ m := Nat.zero_le _
                  simpa [PDT.depth] using this
              have hdepth_one :
                  PDT.depth
                      (if step.pair.2 = true then
                          TailAssignmentBundle.toPDT
                            (n := n) (β := step.next) (γ := γ) step.tail
                        else
                          PDT.leaf
                            (fun j : Fin n =>
                              if j = step.pair.1 then
                                some (Bool.not step.pair.2)
                              else β j))
                    ≤ m := by
                split_ifs
                · simpa using hdepth_tail
                · have : (0 : Nat) ≤ m := Nat.zero_le _
                  simpa [PDT.depth] using this
              -- Теперь оцениваем глубину корневого узла.
              have hmax :
                  Nat.max
                      (PDT.depth
                        (if step.pair.2 = false then
                            TailAssignmentBundle.toPDT
                              (n := n) (β := step.next) (γ := γ) step.tail
                          else
                            PDT.leaf
                              (fun j : Fin n =>
                                if j = step.pair.1 then
                                  some (Bool.not step.pair.2)
                                else β j)))
                      (PDT.depth
                        (if step.pair.2 = true then
                            TailAssignmentBundle.toPDT
                              (n := n) (β := step.next) (γ := γ) step.tail
                          else
                            PDT.leaf
                              (fun j : Fin n =>
                                if j = step.pair.1 then
                                  some (Bool.not step.pair.2)
                                else β j)))
                    ≤ m :=
                Nat.max_le hdepth_zero hdepth_one
              -- Переписываем целевое дерево через определение `toPDT`.
              have htree : TailAssignmentBundle.toPDT
                  (n := n) (β := β) (γ := γ) bundle
                  = PDT.node step.pair.1
                      (if step.pair.2 = false then
                          TailAssignmentBundle.toPDT
                            (n := n) (β := step.next) (γ := γ) step.tail
                        else
                          PDT.leaf
                            (fun j : Fin n =>
                              if j = step.pair.1 then
                                some (Bool.not step.pair.2)
                              else β j))
                      (if step.pair.2 = true then
                          TailAssignmentBundle.toPDT
                            (n := n) (β := step.next) (γ := γ) step.tail
                        else
                          PDT.leaf
                            (fun j : Fin n =>
                              if j = step.pair.1 then
                                some (Bool.not step.pair.2)
                              else β j)) := by
                simp [TailAssignmentBundle.toPDT, hstep, hassign]
              -- Завершаем оценку глубины.
              have hsucc :
                  PDT.depth (TailAssignmentBundle.toPDT
                      (n := n) (β := β) (γ := γ) bundle)
                    ≤ Nat.succ m := by
                simpa [htree, PDT.depth]
                  using Nat.succ_le_succ hmax
              -- Переводим длину обратно к `Nat.succ m`.
              simpa [hassign] using hsucc))
    (bundle.assignments.length) rfl

/-- Разбор `popHead`: результат `none` эквивалентен пустому списку присваиваний. -/
@[simp] lemma popHead_eq_none (bundle : TailAssignmentBundle (n := n) β γ) :
    bundle.popHead = none ↔ bundle.assignments = [] := by
  classical
  cases hassign : bundle.assignments with
  | nil =>
      simp [TailAssignmentBundle.popHead, hassign]
  | cons pair rest =>
      have : (bundle.popHead).isSome := by
        simp [TailAssignmentBundle.popHead, hassign]
      constructor
      · intro hnone
        simpa [Option.isSome, hnone] using this
      · intro hnil
        cases hnil

/-- Если `popHead` возвращает некоторый `HeadStep`, то исходный список
  присваиваний непустой и совпадает с парой `step.pair :: step.tail.assignments`. -/
lemma popHead_eq_some
    {bundle : TailAssignmentBundle (n := n) β γ}
    {step : HeadStep (n := n) (β := β) (γ := γ)}
    (hstep : bundle.popHead = some step) :
    ∃ pair rest,
      bundle.assignments = pair :: rest ∧
      step.pair = pair ∧
      step.tail.assignments = rest := by
  classical
  cases hassign : bundle.assignments with
  | nil =>
      have : bundle.popHead = none := by
        simp [TailAssignmentBundle.popHead, hassign]
      simp [hstep] at this
  | cons pair rest =>
      simp [TailAssignmentBundle.popHead, hassign] at hstep
      refine ⟨pair, rest, rfl, ?_, ?_⟩
      · simpa using congrArg HeadStep.pair hstep
      · simpa using congrArg (fun t => t.tail.assignments) hstep

/-- Длина хвоста, возвращаемого `popHead`, строго меньше длины исходного списка. -/
lemma popHead_tail_length_lt
    {bundle : TailAssignmentBundle (n := n) β γ}
    {step : HeadStep (n := n) (β := β) (γ := γ)}
    (hstep : bundle.popHead = some step) :
    step.tail.assignments.length < bundle.assignments.length := by
  classical
  obtain ⟨pair, rest, hassign, rfl, rtail⟩ := popHead_eq_some
    (n := n) (β := β) (γ := γ) (bundle := bundle) (step := step) hstep
  simpa [hassign, rtail] using Nat.lt_succ_self rest.length

/--
  После снятия головы списка присваиваний никакая пара из хвоста не использует
  ту же координату, что и голова.  Свойство `coord_unique` сразу даёт
  требуемое различие индексов.-/
lemma tail_coord_ne_head
    {bundle : TailAssignmentBundle (n := n) β γ}
    {step : HeadStep (n := n) (β := β) (γ := γ)}
    (hstep : bundle.popHead = some step)
    {pair : BitFix n} (hmem : pair ∈ step.tail.assignments) :
    pair.1 ≠ step.pair.1 := by
  classical
  obtain ⟨headPair, rest, hassign, hpair, htail⟩ :=
    popHead_eq_some (n := n) (β := β) (γ := γ)
      (bundle := bundle) (step := step) hstep
  have hassign_cons : bundle.assignments = step.pair :: rest := by
    simpa [hassign, hpair]
  have hrest : pair ∈ rest := by
    simpa [htail] using hmem
  have hmem_bundle : pair ∈ bundle.assignments := by
    simpa [hassign_cons] using List.mem_cons_of_mem step.pair hrest
  intro hcoord
  have hpair_eq : pair = step.pair :=
    bundle.coord_unique hmem_bundle
      (by
        have : step.pair ∈ bundle.assignments := by
          simpa [hassign_cons] using List.mem_cons_self step.pair rest
        exact this)
      (by simpa [hcoord])
  have hnot_mem : step.pair ∉ rest :=
    (List.nodup_cons.mp (by simpa [hassign_cons] using bundle.nodup)).1
  have : step.pair ∈ rest := by simpa [hpair_eq] using hrest
  exact hnot_mem this

/--
  Пакет, построенный непосредственно из списка `selectorTailAssignments β γ`.
  Все свойства следуют из лемм этого файла.
-/
def ofSelectorTailAssignments : TailAssignmentBundle (n := n) β γ :=
  { assignments := selectorTailAssignments (n := n) β γ
    assignMany_eq := assignMany_selectorTailAssignments
      (n := n) (β := β) (γ := γ)
    nodup := selectorTailAssignments_nodup (n := n) (β := β) (γ := γ)
    coord_unique := by
      intro pair₁ pair₂ h₁ h₂ hcoord
      exact selectorTailAssignments_coordUnique
        (n := n) (β := β) (γ := γ) h₁ h₂ hcoord
    coord_free := by
      intro pair hpair
      exact selectorTailAssignments_coord_free
        (n := n) (β := β) (γ := γ) (pair := pair) hpair }

@[simp] lemma assignments_ofSelectorTailAssignments :
    (ofSelectorTailAssignments (n := n) (β := β) (γ := γ)).assignments
      = selectorTailAssignments (n := n) β γ := rfl

@[simp] lemma assignMany_eq_ofSelectorTailAssignments :
    (ofSelectorTailAssignments (n := n) (β := β) (γ := γ)).assignMany_eq
      = assignMany_selectorTailAssignments (n := n) (β := β) (γ := γ) := rfl

@[simp] lemma coord_free_ofSelectorTailAssignments {pair : BitFix n}
    (hpair : pair ∈ selectorTailAssignments (n := n) β γ) :
    β pair.1 = none :=
  (ofSelectorTailAssignments (n := n) (β := β) (γ := γ)).coord_free hpair

/--
  Результат выделения головы списка присваиваний внутри пакета.  Мы фиксируем
  саму пару `(i, b)`, новый базовый подкуб `β'`, получающийся после её
  применения, и остаточный пакет, отвечающий за хвост.  Такая структура
  понадобится при рекурсивном построении глобальных хвостов.
-/
structure HeadStep where
  /-- Пара, снятая с головы списка. -/
  pair : BitFix n
  /-- Новый базовый подкуб после применения головы. -/
  next : Subcube n
  /-- Явное равенство с результатом `Subcube.assign`. -/
  assign_eq : Subcube.assign β pair.1 pair.2 = some next
  /-- Пакет для хвоста списка присваиваний. -/
  tail : TailAssignmentBundle (n := n) next γ

/--
  Разложение пакета на голову и хвост.  Если список присваиваний пуст, ничего
  не делаем.  Иначе снимаем первую пару и переносим все инварианты на хвост.
-/
noncomputable def popHead
    (bundle : TailAssignmentBundle (n := n) β γ) : Option (HeadStep (β := β) (γ := γ)) :=
  match bundle.assignments with
  | [] => none
  | pair :: rest =>
      classical
      have hfree : β pair.1 = none :=
        bundle.coord_free (by
          have : pair ∈ pair :: rest := by simp
          exact this)
      have hassign_step :
          Subcube.assign β pair.1 pair.2
            = some (fun j : Fin n => if j = pair.1 then some pair.2 else β j) :=
        assign_of_none (β := β) (i := pair.1) (b := pair.2) hfree
      have hassoc :
          Subcube.assignMany
              (fun j : Fin n => if j = pair.1 then some pair.2 else β j) rest
            = some γ := by
        have := bundle.assignMany_eq
        simpa [hassign_step]
          using this
      let β' : Subcube n := fun j => if j = pair.1 then some pair.2 else β j
      have hnodup_rest : rest.Nodup := by
        have := bundle.nodup
        simpa using (List.nodup_cons.mp this).2
      have hcoord_unique_rest :
          ∀ {pair₁ pair₂}, pair₁ ∈ rest → pair₂ ∈ rest →
              pair₁.1 = pair₂.1 → pair₁ = pair₂ := by
        intro pair₁ pair₂ h₁ h₂ hcoord
        have h₁' : pair₁ ∈ pair :: rest := List.mem_cons_of_mem _ h₁
        have h₂' : pair₂ ∈ pair :: rest := List.mem_cons_of_mem _ h₂
        exact bundle.coord_unique h₁' h₂' hcoord
      have hcoord_free_rest : ∀ {pair'}, pair' ∈ rest → β' pair'.1 = none := by
        intro pair' hpair'
        have hmem : pair' ∈ pair :: rest := List.mem_cons_of_mem _ hpair'
        have hfree' : β pair'.1 = none := bundle.coord_free hmem
        have hneq : pair'.1 ≠ pair.1 := by
          intro hidx
          have hpair_eq :=
            bundle.coord_unique (by simp) hmem hidx
          have : pair ∈ rest := by
            simpa [hpair_eq] using hpair'
          exact (List.nodup_cons.mp bundle.nodup).1 this
        have : β' pair'.1 = β pair'.1 := by
          simp [β', hneq]
        simpa [this, hfree']
      let tailBundle : TailAssignmentBundle (n := n) β' γ :=
        { assignments := rest
          assignMany_eq := hassoc
          nodup := hnodup_rest
          coord_unique := by
            intro pair₁ pair₂ h₁ h₂ hcoord
            exact hcoord_unique_rest h₁ h₂ hcoord
          coord_free := by
            intro pair' hpair'
            exact hcoord_free_rest hpair' }
      some
        { pair := pair
          next := β'
          assign_eq := hassign_step
          tail := tailBundle }

end TailAssignmentBundle

/--
  Рекурсивно строим хвостовое PDT, отвечающее конкретному селектору.
  База индукции даёт тривиальный лист, а переход "снимает" одну фиксацию
  и продолжает обработку оставшегося хвоста; корректность гарантирует
  лемма `popHead_tail_length_lt`, показывающая уменьшение длины списка.
-/
noncomputable def TailAssignmentBundle.toPDT
    {n : Nat} {β γ : Subcube n}
    (bundle : TailAssignmentBundle (n := n) β γ) : PDT n :=
  match hstep : bundle.popHead with
  | none =>
      -- Пустой список присваиваний: дерево состоит из одного листа `β`.
      have hnil : bundle.assignments = [] :=
        (TailAssignmentBundle.popHead_eq_none (n := n) (β := β) (γ := γ) bundle).1
          hstep
      have hγβ : γ = β := by
        -- Из `assignMany_eq` и пустого списка получаем равенство подкубов.
        simpa [hnil, Subcube.assignMany] using bundle.assignMany_eq
      simpa [hγβ] using (PDT.leaf β)
  | some step =>
      -- Непустой список: снимаем голову и продолжаем рекурсию.
      have hdata := TailAssignmentBundle.popHead_eq_some
        (n := n) (β := β) (γ := γ) (bundle := bundle) (step := step) hstep
      obtain ⟨pair, rest, hassign, hpair, htail⟩ := hdata
      have hpair_mem : step.pair ∈ bundle.assignments := by
        simpa [hassign, hpair] using (List.mem_cons_self _ rest)
      have hfree : β step.pair.1 = none := bundle.coord_free hpair_mem
      -- Конструкция для противоположного значения в корне.
      let βFlip : Subcube n := fun j => if j = step.pair.1 then some (Bool.not step.pair.2) else β j
      -- Продолжаем строить хвост вдоль совпадающей ветви.
      let tailTree := TailAssignmentBundle.toPDT (n := n) (β := step.next) (γ := γ) step.tail
      -- Ветвление по значению проверяемого бита.
      let zeroBranch : PDT n :=
        if step.pair.2 = false then tailTree else PDT.leaf βFlip
      let oneBranch : PDT n :=
        if step.pair.2 = true then tailTree else PDT.leaf βFlip
      PDT.node step.pair.1 zeroBranch oneBranch
termination_by TailAssignmentBundle.toPDT bundle => bundle.assignments.length
decreasing_by
  -- В каждом рекурсивном шаге длина списка уменьшается благодаря `popHead`.
  simpa [hstep] using TailAssignmentBundle.popHead_tail_length_lt
    (n := n) (β := β) (γ := γ) (bundle := bundle) (step := step) hstep

/--
  Список пакетов `TailAssignmentBundle` для всех селекторов, встречающихся на
  фиксированном листе `β`.  Каждый элемент списка — зависимая пара, в которой
  хранится сам селектор и его хвостовые присваивания.
-/
noncomputable def leafSelectorTailBundles
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    List (Sigma fun γ : Subcube n => TailAssignmentBundle (n := n) β γ) :=
  (leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C.witness.axis hβ).map
    (fun γ => ⟨γ, TailAssignmentBundle.ofSelectorTailAssignments
        (n := n) (β := β) (γ := γ)⟩)

@[simp] lemma mem_leafSelectorTailBundles_elim
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {entry : Sigma fun γ : Subcube n => TailAssignmentBundle (n := n) β γ} :
    entry ∈ leafSelectorTailBundles (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ ↔
      entry.1 ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C.witness.axis hβ := by
  classical
  unfold leafSelectorTailBundles
  constructor
  · intro hmem
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hmem
    simpa
  · intro hmem
    refine List.mem_map.2 ?_
    exact ⟨entry.1, hmem, by cases entry; rfl⟩

/--
  Каждый элемент из списка `leafSelectorTailBundles` даёт дерево `toPDT`, в
  котором исходный селектор присутствует среди листьев.  Мы комбинируем
  предыдущую лемму о `TailAssignmentBundle.mem_leaves_toPDT` с определением
  списка через `List.map`.-/
lemma mem_leafSelectorTailBundles_leaves
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {entry : Sigma fun γ : Subcube n => TailAssignmentBundle (n := n) β γ}
    (hentry : entry ∈ leafSelectorTailBundles (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ) :
    entry.1 ∈ PDT.leaves
      (TailAssignmentBundle.toPDT (n := n) (β := β) (γ := entry.1) entry.2) := by
  classical
  unfold leafSelectorTailBundles at hentry
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hentry
  -- После раскрытия определения остаётся воспользоваться базовой леммой.
  simpa using
    (TailAssignmentBundle.mem_leaves_toPDT
      (n := n) (β := β) (γ := γ)
      (bundle := TailAssignmentBundle.ofSelectorTailAssignments
        (n := n) (β := β) (γ := γ)))

/--
  Глубина любого дерева из `leafSelectorTailBundles` контролируется мощностью
  объединённой поддержки хвостовых присваиваний.  Это связывает локальные
  списки присваиваний с глобальным бюджетом координат и подготовит оценку
  глубины для будущего `globalTail`.-/
lemma leafSelectorTailBundles_depth_le_support
    {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {entry : Sigma fun γ : Subcube n => TailAssignmentBundle (n := n) β γ}
    (hentry : entry ∈ leafSelectorTailBundles (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ) :
    PDT.depth (TailAssignmentBundle.toPDT
        (n := n) (β := β) (γ := entry.1) entry.2)
      ≤ (leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C.witness.axis hβ).card := by
  classical
  -- Раскрываем определение списка пакетов и фиксируем исходный селектор.
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hentry
  -- Оценка глубины через длину списка присваиваний для выбранного селектора.
  have hlen :
      (selectorTailAssignments (n := n) β γ).length
        ≤ (leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C.witness.axis hβ).card :=
    length_selectorTailAssignments_le_leafSelectorSupport
      (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C hβ (γ := γ) hγ
  -- Переписываем длину через поле `assignments` выбранного пакета.
  have hassign_len :
      (TailAssignmentBundle.ofSelectorTailAssignments
          (n := n) (β := β) (γ := γ)).assignments.length
        = (selectorTailAssignments (n := n) β γ).length := by
    simp [TailAssignmentBundle.assignments_ofSelectorTailAssignments]
  have hassign_le :
      (TailAssignmentBundle.ofSelectorTailAssignments
          (n := n) (β := β) (γ := γ)).assignments.length
        ≤ (leafSelectorSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C.witness.axis hβ).card := by
    simpa [hassign_len] using hlen
  -- Применяем оценку глубины для фиксированного `TailAssignmentBundle`.
  refine (TailAssignmentBundle.depth_toPDT_le_length
      (n := n) (β := β) (γ := γ)
      (bundle := TailAssignmentBundle.ofSelectorTailAssignments
        (n := n) (β := β) (γ := γ))).trans ?_
  simpa using hassign_le

