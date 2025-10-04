/-
  pnp3/Core/Atlas.lean

  Атлас = общий словарь подкубов + допустимая ошибка ε.
  Предикат WorksFor: для каждого f из семейства есть поднабор словаря, аппроксимирующий f с ошибкой ≤ ε.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Core.BooleanBasics
import Core.PDT

namespace Pnp3
namespace Core

structure Atlas (n : Nat) where
  dict    : List (Subcube n)
  epsilon : Q
deriving Repr

/-- Подмножество (как предикат) списка: каждый элемент xs присутствует в ys. -/
def listSubset {α} [DecidableEq α] (xs ys : List α) : Prop :=
  ∀ a, xs.contains a = true → ys.contains a = true

/-- Преобразуем членство в списке в равносильное утверждение про `contains`. -/
lemma contains_of_mem {α} [DecidableEq α] {xs : List α} {a : α}
    (ha : a ∈ xs) : xs.contains a = true := by
  classical
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
      by_cases hba : a = b
      · subst hba; simp
      · have hmem : a ∈ xs := by
          simpa [List.mem_cons, hba] using ha
        have hcontains : xs.contains a = true := ih hmem
        simpa [List.contains_cons, hba, hcontains]

/-- Обратное направление: `contains = true` означает обычное членство. -/
lemma mem_of_contains {α} [DecidableEq α] {xs : List α} {a : α}
    (ha : xs.contains a = true) : a ∈ xs := by
  classical
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
      by_cases hba : a = b
      · subst hba; simpa using List.mem_cons_self b xs
      · have htail : xs.contains a = true := by
          simpa [List.contains_cons, hba] using ha
        have hmem := ih htail
        simpa [List.mem_cons, hba] using hmem

/-- Пустой список содержится в любом другом. -/
lemma listSubset_nil {α} [DecidableEq α] (ys : List α) :
    listSubset ([] : List α) ys := by
  intro a ha
  simp at ha

/-- Рефлексивность: любой список является подсписком самого себя. -/
lemma listSubset_refl {α} [DecidableEq α] (xs : List α) :
    listSubset xs xs := by
  intro a ha; simpa using ha

/-- Транзитивность отношения `listSubset`. -/
lemma listSubset_trans {α} [DecidableEq α]
    {xs ys zs : List α} (hxy : listSubset xs ys) (hyz : listSubset ys zs) :
    listSubset xs zs := by
  intro a ha
  exact hyz _ (hxy _ ha)

/-- Из соотношения `listSubset xs ys` следует включение по обычному членству. -/
lemma listSubset.mem {α} [DecidableEq α]
    {xs ys : List α} (h : listSubset xs ys) {a : α} (ha : a ∈ xs) :
    a ∈ ys := by
  classical
  have hcontains : xs.contains a = true := contains_of_mem (xs := xs) ha
  have hcontains' := h a hcontains
  exact mem_of_contains (xs := ys) hcontains'


/-- Добавление элемента, уже содержащегося в `ys`, сохраняет отношение `listSubset`. -/
lemma listSubset_cons_of_mem {α} [DecidableEq α]
    {xs ys : List α} {a : α}
    (ha : ys.contains a = true) (h : listSubset xs ys) :
    listSubset (a :: xs) ys := by
  intro b hb
  classical
  by_cases hba : b = a
  · subst hba; simpa using ha
  · have hb' : xs.contains b = true := by
      simpa [List.contains_cons, hba] using hb
    exact h _ hb'

/--
  Удаление дубликатов в левой части отношения `listSubset` сохраняет его.
  Это позволит пользоваться «очищенными» списками при оценке бюджета
  листьев, не теряя информацию о подмножественном включении.
-/
lemma listSubset_dedup {α} [DecidableEq α]
    {xs ys : List α} (h : listSubset xs ys) :
    listSubset xs.dedup ys := by
  intro a ha
  classical
  have hmem : a ∈ xs.dedup := mem_of_contains (xs := xs.dedup) ha
  have hmem_xs : a ∈ xs := (List.mem_dedup.mp hmem)
  have hcontains : xs.contains a = true := contains_of_mem (xs := xs) hmem_xs
  exact h _ hcontains

/--
  Переводим утверждение о подсписке в включение финитных множеств.
  В частности, если `xs` содержится в `ys`, то и множество элементов
  `xs.toFinset` входит в `ys.toFinset`.
-/
lemma listSubset_toFinset_subset {α} [DecidableEq α]
    {xs ys : List α} (h : listSubset xs ys) :
    xs.toFinset ⊆ ys.toFinset :=
  by
    classical
    intro a ha
    have hmem : a ∈ xs := by
      simpa [List.mem_toFinset] using ha
    have hcontains : xs.contains a = true :=
      contains_of_mem (xs := xs) hmem
    have hcontains' := h a hcontains
    have hmem' : a ∈ ys :=
      mem_of_contains (xs := ys) hcontains'
    simpa [List.mem_toFinset] using hmem'

/--
  Для конечного подмножества элементов подтипа списочное представление
  `toList.map Subtype.val` содержит те же уникальные элементы, что и образ
  финсета под отображением `Subtype.val`.  Это даёт удобный мост между
  `Finset`-представлением словаря и списками, которыми пользуется `coveredB`.
-/
lemma toList_mapSubtype_val_toFinset {α} [DecidableEq α]
    {p : α → Prop} [DecidablePred p]
    (S : Finset {a : α // p a}) :
    (S.toList.map Subtype.val).toFinset
      = S.image (fun x => x.1) := by
  classical
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have ha_list : a ∈ S.toList.map Subtype.val := by
      simpa [List.mem_toFinset] using ha
    rcases List.mem_map.1 ha_list with ⟨x, hx, rfl⟩
    have hx_fin : x ∈ S := by
      simpa [Finset.mem_toList] using hx
    exact Finset.mem_image.2 ⟨x, hx_fin, rfl⟩
  · intro ha
    rcases Finset.mem_image.1 ha with ⟨x, hxS, rfl⟩
    have hx_list : x ∈ S.toList := by
      simpa [Finset.mem_toList] using hxS
    have hx_map : x.val ∈ S.toList.map Subtype.val :=
      List.mem_map.2 ⟨x, hx_list, rfl⟩
    exact (List.mem_toFinset.mpr hx_map)

/--
  Мощность множества уникальных элементов списка не превосходит длину
  исходного списка.  Техническое неравенство используется при оценке
  бюджета листьев через `List.toFinset`.
-/
lemma toFinset_card_le_length {α} [DecidableEq α] :
    ∀ xs : List α, xs.toFinset.card ≤ xs.length
  | [] => by
      simp
  | (a :: xs) =>
      by
        classical
        have hrec := toFinset_card_le_length xs
        by_cases hmem : a ∈ xs
        · -- Вставка существующего элемента не меняет мощность множества.
          have hset : (a :: xs).toFinset = xs.toFinset := by
            simpa [List.toFinset_cons, hmem]
          have hle : xs.toFinset.card ≤ xs.length := hrec
          have : xs.toFinset.card ≤ (a :: xs).length := by
            simpa [List.length_cons] using
              Nat.le_trans hle (Nat.le_succ _)
          simpa [hset]
        · -- Добавление нового элемента увеличивает мощность на единицу.
          have hnot : a ∉ xs.toFinset := by
            simpa [List.mem_toFinset] using hmem
          have hset :
              (a :: xs).toFinset = insert a xs.toFinset := by
            simpa [List.toFinset_cons, hmem]
          have hcard :
              (a :: xs).toFinset.card = xs.toFinset.card + 1 := by
            simpa [hset, hnot] using card_insert (s := xs.toFinset) (a := a)
          have hcard' :
              (insert a xs.toFinset).card = xs.toFinset.card + 1 := by
            simpa [hset]
              using hcard
          have hlen := Nat.succ_le_succ hrec
          simpa [List.length_cons, hcard', Nat.succ_eq_add_one] using hlen

/-- Атлас "работает" для семейства F:
    для каждого f ∈ F существует подсписок R_f ⊆ dict, такой что errU f R_f ≤ ε. -/
def WorksFor {n : Nat}
    (A : Atlas n) (F : List (BitVec n → Bool)) : Prop :=
  ∀ f, f ∈ F →
    ∃ (Rf : List (Subcube n)),
      listSubset Rf A.dict ∧
      errU f Rf ≤ A.epsilon

/-- Атлас, построенный из PDT: словарь = листья PDT. -/
def Atlas.ofPDT {n : Nat} (t : PDT n) (ε : Q) : Atlas n :=
  { dict := PDT.leaves t, epsilon := ε }

end Core
end Pnp3
