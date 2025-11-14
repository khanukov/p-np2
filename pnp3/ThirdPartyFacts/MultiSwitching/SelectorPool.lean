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
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorTailAssignments (n := n) (M := M)
        (τ := τ) (w := w) (t := t) (packages := packages)
        C.witness.axis hβ) :
    selectorTailSupport (n := n) β entry.1
      ⊆ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ := by
  classical
  -- Распаковываем принадлежность из отображения `map`.
  unfold leafSelectorTailAssignments at hentry
  obtain ⟨γ, hγ_mem, rfl⟩ := List.mem_map.1 hentry
  -- `γ` лежит в исходном списке селекторов без повторений.
  have hγ_set : γ ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages)
      C.witness.axis hβ := hγ_mem
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
      (w := w) (t := t) (packages := packages) C hβ).2 ?_
  refine ⟨γ, ?_, ?_⟩
  · -- Переход от списка без повторений к finset-версии.
    have hfin :=
      (mem_leafSelectorFinset
        (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ (γ := γ)).2 hγ_set
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
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    {entry : Subcube n × List (BitFix n)}
    (hentry : entry ∈ leafSelectorTailAssignments (n := n) (M := M)
        (τ := τ) (w := w) (t := t) (packages := packages)
        C.witness.axis hβ) :
    (selectorTailSupport (n := n) β entry.1).card ≤
      (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ).card := by
  classical
  refine Finset.card_le_of_subset ?_
  exact selectorTailSupport_subset_leafSelectorTailSupport
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ hentry

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
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) : Finset (Fin n) :=
  (leafSelectorFinset (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C.witness.axis hβ).sup
    (fun γ => selectorTailSupport (n := n) β γ)

/--
  Список координат глобальной хвостовой поддержки.  Порядок фиксируется
  произвольным образом (через `Finset`), однако мы гарантируем отсутствие
  повторов, что позволяет безопасно использовать его в индуктивных процедурах
  вроде `Subcube.refineByCoords`.-/
noncomputable def leafSelectorTailSupportList {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) : List (Fin n) :=
  (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
      (packages := packages) C hβ).1.toList

lemma leafSelectorTailSupportList_nodup {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    (leafSelectorTailSupportList (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ).Nodup := by
  classical
  simpa [leafSelectorTailSupportList]
    using (leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ).2.nodup_toList

lemma leafSelectorTailSupportList_toFinset {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) :
    (leafSelectorTailSupportList (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ).toFinset
      = leafSelectorTailSupport (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C hβ := by
  classical
  ext i
  constructor
  · intro hi
    have hi_list : i ∈ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ).1.toList :=
      (List.mem_toFinset).1 hi
    have hi_multiset := (Multiset.mem_toList).1 hi_list
    exact (Finset.mem_def).2 hi_multiset
  · intro hi
    have hi_multiset : i ∈ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ).1 :=
      (Finset.mem_def).1 hi
    have hi_list : i ∈ (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ).1.toList :=
      Multiset.mem_toList.mpr hi_multiset
    exact (List.mem_toFinset).2 hi_list

lemma refineBySupport_assignMany {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β γ : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis)
    (hmem : γ ∈ Core.Subcube.refineByCoords β
        (leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C hβ)) :
    ∃ updates : List (BitFix n),
      updates.Nodup ∧
      (∀ pair ∈ updates, pair.1 ∈ leafSelectorTailSupport (n := n) (M := M)
          (τ := τ) (w := w) (t := t) (packages := packages) C hβ) ∧
      Subcube.assignMany β updates = some γ := by
  classical
  have hnodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ
  obtain ⟨updates, hnodup_updates, hsubset, hassign⟩ :=
    Core.Subcube.mem_refineByCoords_assignMany
      (β := β) (γ := γ)
      (coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
        (w := w) (t := t) (packages := packages) C hβ)
      hnodup hmem
  refine ⟨updates, hnodup_updates, ?subset, hassign⟩
  intro pair hpair
  have hfinset := hsubset pair hpair
  have hcoords := leafSelectorTailSupportList_toFinset
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ
  simpa [hcoords]

/--
  Дизъюнктная нормализация селекторов на листе `β`.  Мы разбиваем исходный
  подкуб `β` по всем координатам глобальной поддержки и сохраняем только те
  уточнения, которые лежат в одном из селекторов объединённого семейства.
  Полученный список попарно несовместен и служит входом для функции
  `PDT.ofDisjointLeaves` при построении `globalTail`.
-/
noncomputable def refineDisjoint {n M τ w t : Nat}
    [DecidableEq (Subcube n)] [DecidableEq (Fin n)]
    {packages : List (Budgeted (n := n) (M := M) (τ := τ) (w := w) (t := t))}
    (C : CombinedTailCertificate (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) C.witness.axis) : List (Subcube n) :=
  let coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ
  let base := Core.Subcube.refineByCoords β coords
  base.filter (fun γ =>
    ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C.witness.axis hβ,
      Core.Subcube.subset (n := n) γ selector)

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
          (w := w) (t := t) (packages := packages) C hβ)
        ∧ ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C.witness.axis hβ,
          Core.Subcube.subset (n := n) γ selector := by
  classical
  unfold refineDisjoint
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ with hcoords
  set base := Core.Subcube.refineByCoords β coords with hbase
  constructor
  · intro hmem
    have hmem_base : γ ∈ base := by
      have := List.mem_of_mem_filter hmem
      simpa [hbase] using this
    have hpredicate :
        ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w) (t := t)
            (packages := packages) C.witness.axis hβ,
          Core.Subcube.subset (n := n) γ selector := by
      obtain ⟨_, hcond⟩ := List.mem_filter.mp hmem
      simpa [hbase] using hcond
    simpa [hcoords, hbase]
      using And.intro (by simpa [hbase] using hmem_base) hpredicate
  · rintro ⟨hmem_base, hpredicate⟩
    have :
        γ ∈ base ∧
          ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ) (w := w)
              (t := t) (packages := packages) C.witness.axis hβ,
            Core.Subcube.subset (n := n) γ selector := by
      exact And.intro (by simpa [hcoords, hbase] using hmem_base) hpredicate
    simpa [hcoords, hbase] using List.mem_filter.mpr this

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
      Core.Subcube.mem (n := n) γ x := by
  classical
  obtain ⟨selector, hselector, hxselector⟩ := hx
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ with hcoords_def
  set base := Core.Subcube.refineByCoords β coords with hbase_def
  have hcoords_nodup := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ
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
              (w := w) (t := t) (packages := packages)
              C.witness.axis hβ :=
        mem_leafSelectorTailAssignments_of_mem_set
          (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) (A := C.witness.axis) hβ hselector
      have hi_global : i ∈ leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C hβ :=
        selectorTailSupport_subset_leafSelectorTailSupport
          (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C hβ hentry hi_support
      have hi_list : i ∈ coords := by
        have : coords =
            (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) C hβ).1.toList := by
          simpa [hcoords_def, leafSelectorTailSupportList]
        have himulti : i ∈
            (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
                (w := w) (t := t) (packages := packages) C hβ).1 :=
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
          (packages := packages) C.witness.axis hβ,
        Core.Subcube.subset (n := n) γ selector' :=
    ⟨selector, hselector, hsubset_γ_selector⟩
  have hmem_filter :
      γ ∈ refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C hβ := by
    have := List.mem_filter.mpr ⟨hγ_base, hpredicate⟩
    simpa [refineDisjoint, hcoords_def, hbase_def]
      using this
  exact ⟨γ, hmem_filter, hγx⟩

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
      (Core.Subcube.disjoint (n := n)) := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ
  have hpair := Core.Subcube.refineByCoords_pairwise_disjoint
      (n := n) (β := β) (coords := coords)
  have hsub := List.filter_sublist
      (l := Core.Subcube.refineByCoords β coords)
      (p := fun γ =>
        ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) C.witness.axis hβ,
          Core.Subcube.subset (n := n) γ selector)
  exact hpair.sublist hsub

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
    Core.Subcube.subset (n := n) γ β := by
  classical
  obtain ⟨hmem_base, -⟩ :=
    (mem_refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C (β := β) (γ := γ) hβ).1 hγ
  have hcoords := leafSelectorTailSupportList_nodup
    (n := n) (M := M) (τ := τ) (w := w) (t := t)
    (packages := packages) C hβ
  have := Core.Subcube.subset_of_mem_refineByCoords
    (n := n) (β := β) (γ := γ)
    (coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ)
    hcoords hmem_base
  simpa using this

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
      Core.Subcube.subset (n := n) γ selector := by
  classical
  obtain ⟨-, hsubset⟩ :=
    (mem_refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
        (packages := packages) C (β := β) (γ := γ) hβ).1 hγ
  exact hsubset

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
        (w := w) (t := t) (packages := packages) C hβ).card := by
  classical
  set coords := leafSelectorTailSupportList (n := n) (M := M) (τ := τ)
      (w := w) (t := t) (packages := packages) C hβ with hcoords
  set base := Core.Subcube.refineByCoords β coords with hbase
  have hfilter :
      (refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C hβ).length
        ≤ base.length := by
    simpa [refineDisjoint, hcoords, hbase]
      using List.length_filter_le base
        (fun γ =>
          ∃ selector ∈ leafSelectorSet (n := n) (M := M) (τ := τ)
              (w := w) (t := t) (packages := packages) C.witness.axis hβ,
            Core.Subcube.subset (n := n) γ selector)
  have hbase_len : base.length ≤ 2 ^ coords.length := by
    simpa [hbase]
      using Core.Subcube.length_refineByCoords_le_pow_two
        (n := n) (β := β) (coords := coords)
  have hcard :
      coords.length
        = (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) C hβ).card := by
    classical
    have : coords =
        (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
            (w := w) (t := t) (packages := packages) C hβ).1.toList := by
      simpa [hcoords, leafSelectorTailSupportList]
    subst this
    simpa [Finset.card, Multiset.card] using
      (leafSelectorTailSupport (n := n) (M := M) (τ := τ)
          (w := w) (t := t) (packages := packages) C hβ).1.length_toList
  have htotal :
      (refineDisjoint (n := n) (M := M) (τ := τ) (w := w) (t := t)
          (packages := packages) C hβ).length
        ≤ 2 ^ coords.length :=
    hfilter.trans hbase_len
  simpa [hcard] using htotal

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

/-- Координата каждого присваивания действительно не зафиксирована в `β`. -/
lemma selectorTailAssignments_coord_free {n : Nat}
    {β γ : Subcube n} {pair : BitFix n} :
    pair ∈ selectorTailAssignments (n := n) β γ → β pair.1 = none :=
  fun h => (mem_selectorTailAssignments (β := β) (γ := γ) (pair := pair)).1 h |>.2

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
  Лист, соответствующий селектору `γ`, действительно присутствует в дереве,
  построенном функцией `TailAssignmentBundle.toPDT`.  Доказательство идёт по
  длине списка присваиваний: базовый случай сводится к пустому списку и
  равенству `γ = β`, а переход использует информацию `popHead` и индуктивную
  гипотезу для хвостового пакета.-/
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

