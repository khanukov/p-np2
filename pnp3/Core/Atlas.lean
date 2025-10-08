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

/-- Подмножество (как предикат) списка: каждый элемент `xs` присутствует в `ys`. -/
def listSubset {α} (xs ys : List α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ xs → a ∈ ys

/-- Пустой список содержится в любом другом. -/
lemma listSubset_nil {α} (ys : List α) :
    listSubset ([] : List α) ys := by
  intro a ha
  cases ha

/-- Рефлексивность: любой список является подсписком самого себя. -/
lemma listSubset_refl {α} (xs : List α) :
    listSubset xs xs := by
  intro a ha
  exact ha

/-- Транзитивность отношения `listSubset`. -/
lemma listSubset_trans {α}
    {xs ys zs : List α} (hxy : listSubset xs ys) (hyz : listSubset ys zs) :
    listSubset xs zs := by
  intro a ha
  exact hyz (hxy ha)

/-- Из соотношения `listSubset xs ys` следует включение по обычному членству. -/
lemma listSubset.mem {α}
    {xs ys : List α} (h : listSubset xs ys) {a : α} (ha : a ∈ xs) :
    a ∈ ys := h ha

/--
  Если каждый элемент `xs` принадлежит `ys` (в обычном смысле списочного
  членства), то выполняется и отношение `listSubset`.  Эта вспомогательная
  лемма позволяет работать с привычными "математическими" включениями, не
  заботясь о том, какая конкретная реализация `DecidableEq` используется для
  функций `contains`.
-/
lemma listSubset_of_mem {α}
    {xs ys : List α} (h : ∀ ⦃a : α⦄, a ∈ xs → a ∈ ys) :
    listSubset xs ys := h

/-- Эквивалентность между определением `listSubset` и привычным включением. -/
lemma listSubset_iff_mem {α} (xs ys : List α) :
    listSubset xs ys ↔ ∀ ⦃a : α⦄, a ∈ xs → a ∈ ys := Iff.rfl

/-- Добавление элемента, уже содержащегося в `ys`, сохраняет отношение `listSubset`. -/
lemma listSubset_cons_of_mem {α}
    {xs ys : List α} {a : α}
    (ha : a ∈ ys) (h : listSubset xs ys) :
    listSubset (a :: xs) ys := by
  intro b hb
  have hcases : b = a ∨ b ∈ xs := List.mem_cons.mp hb
  cases hcases with
  | inl hba =>
      subst hba
      exact ha
  | inr hmem => exact h hmem

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
  have hmem_xs : a ∈ xs := (List.dedup_sublist (l := xs)).mem ha
  exact h hmem_xs

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
    have hmem : a ∈ xs := List.mem_toFinset.mp ha
    have hmem' : a ∈ ys := h hmem
    exact List.mem_toFinset.mpr hmem'

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
    have ha_list : a ∈ S.toList.map Subtype.val :=
      List.mem_toFinset.mp ha
    rcases List.mem_map.1 ha_list with ⟨x, hx, rfl⟩
    have hx_fin : x ∈ S := (Finset.mem_toList.mp hx)
    exact Finset.mem_image.2 ⟨x, hx_fin, rfl⟩
  · intro ha
    rcases Finset.mem_image.1 ha with ⟨x, hxS, rfl⟩
    have hx_list : x ∈ S.toList := (Finset.mem_toList.mpr hxS)
    have hx_map : x.val ∈ S.toList.map Subtype.val :=
      List.mem_map.2 ⟨x, hx_list, rfl⟩
    exact List.mem_toFinset.mpr hx_map

/--
  Мощность множества уникальных элементов списка не превосходит длину
  исходного списка.  Техническое неравенство используется при оценке
  бюджета листьев через `List.toFinset`.
-/
lemma toFinset_card_le_length {α} [DecidableEq α] :
    ∀ xs : List α, xs.toFinset.card ≤ xs.length
  | [] => by
      simp
  | a :: xs => by
      classical
      have hrec := toFinset_card_le_length xs
      by_cases hmem : a ∈ xs
      · -- Если элемент уже был в списке, множество не меняется.
        have hset : (a :: xs).toFinset = xs.toFinset := by
          simp [List.toFinset_cons, hmem]
        have hsucc : xs.toFinset.card ≤ xs.length + 1 := by
          have htmp : xs.toFinset.card ≤ Nat.succ xs.length :=
            Nat.le_succ_of_le hrec
          have htmp' := htmp
          rw [Nat.succ_eq_add_one] at htmp'
          exact htmp'
        have hlen_cons : (a :: xs).length = xs.length + 1 := by
          simp [List.length_cons]
        have hbound : xs.toFinset.card ≤ (a :: xs).length :=
          hlen_cons.symm ▸ hsucc
        have hcard_eq : (a :: xs).toFinset.card = xs.toFinset.card :=
          congrArg Finset.card hset
        exact hcard_eq ▸ hbound
      · -- Новый элемент увеличивает мощность на единицу.
        have hnot : a ∉ xs.toFinset := by
          intro hfin
          have hlist : a ∈ xs := List.mem_toFinset.mp hfin
          exact hmem hlist
        have hset : (a :: xs).toFinset = insert a xs.toFinset := by
          simp [List.toFinset_cons, hmem]
        have hcard_insert :
            (insert a xs.toFinset).card = xs.toFinset.card + 1 :=
          Finset.card_insert_of_notMem (s := xs.toFinset) (a := a) hnot
        have hcard_eq :
            (a :: xs).toFinset.card = xs.toFinset.card + 1 := by
          have hcongr := congrArg Finset.card hset
          exact hcongr.trans hcard_insert
        have hlen_cons : (a :: xs).length = xs.length + 1 := by
          simp [List.length_cons]
        have hsucc : xs.toFinset.card + 1 ≤ xs.length + 1 := by
          have htmp : Nat.succ (xs.toFinset.card) ≤ Nat.succ xs.length :=
            Nat.succ_le_succ hrec
          have htmp' := htmp
          rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at htmp'
          exact htmp'
        have hbound : xs.toFinset.card + 1 ≤ (a :: xs).length :=
          hlen_cons.symm ▸ hsucc
        exact hcard_eq ▸ hbound

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
