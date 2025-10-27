/--
  pnp3/ThirdPartyFacts/Depth1_Switching.lean

  Этот модуль подготавливает инфраструктуру для вероятностного анализа
  switching-леммы глубины 1.  Мы фиксируем равномерное распределение на
  exact-ℓ рестрикциях (`RandomRestriction.restrictionUniform`) и вводим
  вспомогательные определения:

  * `BadRestriction` — предикат того, что CNF ширины `w` порождает хвост
    глубины > `t` после применения точного ограничения.
  * `badSet` и `badMass` — список «плохих» рестрикций и их суммарная масса
    в равномерном распределении.

  Затем выводим первые арифметические факты: масса «плохого» множества
  выражается через его мощность, а также связываем эту мощность с числом
  клауз формулы.  Эти леммы не закрывают саму switching-оценку, но дают
  удобную отправную точку для вероятностной индукции по числу литералов.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Mathlib.Topology.Instances.ENNReal
import Core.BooleanBasics
import ThirdPartyFacts.RandomRestriction
import Pnp3.Counting.BinomialBounds

open scoped ENNReal

namespace Pnp3
namespace ThirdPartyFacts

/-- Множество индексов переменных, встречающихся в клаузе. -/
@[simp] def clauseIndexFinset (C : Core.CnfClause n) : Finset (Fin n) :=
  (C.literals.map (fun ℓ => ℓ.idx)).toFinset

lemma clauseIndexFinset_mem {C : Core.CnfClause n} {i : Fin n} :
    i ∈ clauseIndexFinset (n := n) C ↔ ∃ ℓ ∈ C.literals, ℓ.idx = i := by
  classical
  simp [clauseIndexFinset]

/-- Мощность множества индексов клаузы совпадает с её шириной.  Используем
`C.nodupIdx`, чтобы заменить сумматор `toFinset` на исходный список
литералов. -/
lemma clauseIndexFinset_card (C : Core.CnfClause n) :
    (clauseIndexFinset (n := n) C).card = C.width := by
  classical
  -- Раскрываем определения и используем стандартную формулу для `List.toFinset`.
  simpa [clauseIndexFinset, Core.CnfClause.width]
    using List.toFinset_card_of_nodup
      (l := C.literals.map fun ℓ : Core.Literal n => ℓ.idx) C.nodupIdx

/--
Каждая клауза формулы `F : CNF n w` содержит не больше `w` различных индексов
переменных.  Это прямое следствие ограничения ширины в структуре `CNF` и
равенства между шириной и мощностью множества индексов.-/
lemma clauseIndexFinset_card_le_width_of_mem {F : Core.CNF n w}
    {C : Core.CnfClause n} (hC : C ∈ F.clauses) :
    (clauseIndexFinset (n := n) C).card ≤ w := by
  classical
  have hwidth : C.width ≤ w := F.width_le C hC
  simpa [clauseIndexFinset_card (n := n) (C := C)] using hwidth

/-- Любое подмножество индексов клаузы не может превышать её ширину. -/
lemma clauseSubsetCandidates_card_le_width {C : Core.CnfClause n}
    {ℓ t : Nat} {F : Finset (Fin n)}
    (hF : F ∈ clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C) :
    F.card ≤ C.width := by
  classical
  -- Элемент семейства `clauseSubsetCandidates` по определению содержится в
  -- `clauseIndexFinset`, значит, его мощность не превосходит мощности клаузы.
  have hsubset : F ⊆ clauseIndexFinset (n := n) C := by
    exact (Finset.mem_filter.mp hF).1 |> Finset.mem_powerset.mp
  have hle := Finset.card_le_of_subset hsubset
  -- Осталось переписать мощность оси через ширину клаузы.
  simpa [clauseIndexFinset_card (n := n) (C := C)] using hle

/-- Вспомогательная функция: для списка литералов возвращает назначение,
которое делает каждый литерал ложным. -/
def clauseFalseAssignmentList : List (Core.Literal n) → Fin n → Bool
  | [] => fun _ => false
  | ℓ :: rest => fun i =>
      if hi : i = ℓ.idx then !ℓ.value else clauseFalseAssignmentList rest i

lemma clauseFalseAssignmentList_mem
    {lit : Core.Literal n} {lst : List (Core.Literal n)}
    (hmem : lit ∈ lst)
    (hnodup : (lst.map fun ℓ => ℓ.idx).Nodup) :
    clauseFalseAssignmentList (n := n) lst lit.idx = !lit.value := by
  classical
  induction lst with
  | nil => cases hmem
  | cons head tail ih =>
      have hnodup_cons := (List.nodup_cons).1 hnodup
      have hnotIn : head.idx ∉ tail.map (fun ℓ => ℓ.idx) := hnodup_cons.1
      have htail := hnodup_cons.2
      have hcases := List.mem_cons.1 hmem
      cases hcases with
      | inl hEq =>
          subst hEq
          simp [clauseFalseAssignmentList]
      | inr htailMem =>
          have hneq : lit.idx ≠ head.idx := by
            intro hEq
            have : head.idx ∈ tail.map (fun ℓ => ℓ.idx) := by
              refine List.mem_map.mpr ?_
              exact ⟨lit, htailMem, by simpa [hEq]⟩
            exact hnotIn this
          have hind := ih htailMem htail
          simp [clauseFalseAssignmentList, hneq, hind]

/-- Назначение, делающие каждый литерал клаузы ложным. -/
def clauseFalseAssignment (C : Core.CnfClause n) : Fin n → Bool :=
  clauseFalseAssignmentList (n := n) C.literals

lemma clauseFalseAssignment_eval {C : Core.CnfClause n}
    {lit : Core.Literal n} (hmem : lit ∈ C.literals) :
    clauseFalseAssignment (n := n) C lit.idx = !lit.value := by
  classical
  simpa [clauseFalseAssignment]
    using clauseFalseAssignmentList_mem
      (n := n) (lit := lit) (lst := C.literals) hmem C.nodupIdx

/-- Разность между множеством индексов клаузы и подмножеством `F`. -/
@[simp] def clauseAssignedSet (C : Core.CnfClause n) (F : Finset (Fin n)) :
    Finset (Fin n) := clauseIndexFinset (n := n) C \ F

lemma clauseAssignedSet_disjoint {C : Core.CnfClause n}
    {F : Finset (Fin n)} (hF : F ⊆ clauseIndexFinset (n := n) C) :
    Disjoint F (clauseAssignedSet (n := n) C F) := by
  classical
  exact Finset.disjoint_right.2 (by
    intro i hiF hiAssigned
    rcases Finset.mem_sdiff.mp hiAssigned with ⟨_, hiNot⟩
    exact hiNot (hF hiF))

lemma clauseAssignedSet_card {C : Core.CnfClause n}
    {F : Finset (Fin n)} (hF : F ⊆ clauseIndexFinset (n := n) C) :
    (clauseAssignedSet (n := n) C F).card
      = (clauseIndexFinset (n := n) C).card - F.card := by
  classical
  have hsubset : clauseAssignedSet (n := n) C F ⊆ clauseIndexFinset (n := n) C := by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hiIdx, _⟩
    exact hiIdx
  have := Finset.card_sdiff hsubset
  simpa [clauseAssignedSet, Finset.card_sdiff, hF]

lemma clauseRestriction_card {C : Core.CnfClause n} {F : Finset (Fin n)}
    (hFsubset : F ⊆ clauseIndexFinset (n := n) C) (hℓ : F.card ≤ ℓ) :
    Fintype.card
        {ρ : ExactRestriction n ℓ //
          F ⊆ ρ.axis.support ∧
          Disjoint (clauseAssignedSet (n := n) C F) ρ.axis.support ∧
          ∀ i ∈ clauseAssignedSet (n := n) C F,
            ρ.values i = clauseFalseAssignment (n := n) C i}
      = Nat.choose
          (n - (clauseIndexFinset (n := n) C).card)
          (ℓ - F.card)
          * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + F.card) := by
  classical
  have hdis := clauseAssignedSet_disjoint
    (n := n) (C := C) (F := F) hFsubset
  have hcard := clauseAssignedSet_card
    (n := n) (C := C) (F := F) hFsubset
  have hchoose_simplify :
      n - F.card - (clauseAssignedSet (n := n) C F).card
        = n - (clauseIndexFinset (n := n) C).card := by
    simpa [hcard, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]
      using congrArg (fun x => n - x) hcard
  have hpow_simplify :
      n - (clauseAssignedSet (n := n) C F).card
        = n - (clauseIndexFinset (n := n) C).card + F.card := by
    simpa [hcard, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]
      using congrArg (fun x => n - x) hcard
  simpa [clauseAssignedSet, clauseFalseAssignment, hcard,
        hchoose_simplify, hpow_simplify]
    using RandomRestriction.superset_disjoint_values_card
      (n := n) (ℓ := ℓ) (S := F)
      (T := clauseAssignedSet (n := n) C F)
      (assign := clauseFalseAssignment (n := n) C)
      hℓ hdis

/-!
### Разбиение «плохих» рестрикций по подмножествам клаузы

Ниже мы фиксируем набор служебных определений, позволяющих группировать
рестрикции по конкретному подмножеству литералов клаузы, которые остаются
свободными после применения ограничения.  Это разбиение обеспечивает точный
контроль над мощностью «плохих» семейств и напрямую использует
`clauseRestriction_card`.
-/

/-- Свойство, описывающее рестрикции, которые оставляют свободным поднабор `F`
из литералов клаузы `C` и одновременно делают все остальные литералы ложными. -/
@[simp] def clauseWitnessCondition (C : Core.CnfClause n)
    (F : Finset (Fin n)) (ρ : ExactRestriction n ℓ) : Prop :=
  F ⊆ clauseIndexFinset (n := n) C ∧
  F ⊆ ρ.axis.support ∧
  Disjoint (clauseAssignedSet (n := n) C F) ρ.axis.support ∧
  ∀ i ∈ clauseAssignedSet (n := n) C F,
    ρ.values i = clauseFalseAssignment (n := n) C i

lemma clauseWitnessCondition_subset_clause {C : Core.CnfClause n}
    {F : Finset (Fin n)} {ρ : ExactRestriction n ℓ}
    (hρ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ) :
    F ⊆ clauseIndexFinset (n := n) C := hρ.1

lemma clauseWitnessCondition_subset_axis {C : Core.CnfClause n}
    {F : Finset (Fin n)} {ρ : ExactRestriction n ℓ}
    (hρ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ) :
    F ⊆ ρ.axis.support := hρ.2.1

lemma clauseWitnessCondition_disjoint {C : Core.CnfClause n}
    {F : Finset (Fin n)} {ρ : ExactRestriction n ℓ}
    (hρ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ) :
    Disjoint (clauseAssignedSet (n := n) C F) ρ.axis.support := hρ.2.2.1

lemma clauseWitnessCondition_values {C : Core.CnfClause n}
    {F : Finset (Fin n)} {ρ : ExactRestriction n ℓ}
    (hρ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ)
    {i : Fin n} (hi : i ∈ clauseAssignedSet (n := n) C F) :
    ρ.values i = clauseFalseAssignment (n := n) C i := hρ.2.2.2 i hi

lemma clauseWitnessCondition_inter_eq {C : Core.CnfClause n}
    {F : Finset (Fin n)} {ρ : ExactRestriction n ℓ}
    (hρ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ) :
    ρ.axis.support ∩ clauseIndexFinset (n := n) C = F := by
  classical
  apply Finset.ext
  intro i
  constructor
  · intro hi
    rcases Finset.mem_inter.mp hi with ⟨hiaxis, hicla⟩
    by_contra hnot
    have hmem : i ∈ clauseAssignedSet (n := n) C F := by
      refine Finset.mem_sdiff.mpr ?_
      exact ⟨hicla, hnot⟩
    have hdis := clauseWitnessCondition_disjoint
      (n := n) (ℓ := ℓ) (C := C) (F := F) (ρ := ρ) hρ
    have : i ∉ ρ.axis.support := by
      exact (Finset.disjoint_right.mp hdis) hmem
        (by
          exact hiaxis)
    exact this hiaxis
  · intro hi
    have hsubset := clauseWitnessCondition_subset_axis
      (n := n) (ℓ := ℓ) (C := C) (F := F) (ρ := ρ) hρ
    have hclause := clauseWitnessCondition_subset_clause
      (n := n) (ℓ := ℓ) (C := C) (F := F) (ρ := ρ) hρ
    have haxis := hsubset hi
    have hcl := hclause hi
    exact Finset.mem_inter.mpr ⟨haxis, hcl⟩

/-- Семейство рестрикций, соответствующее фиксированному подмножеству `F`
свободных литералов клаузы `C`. -/
@[simp] def clauseWitnessFamily (C : Core.CnfClause n)
    (F : Finset (Fin n)) (ℓ : Nat) : Finset (ExactRestriction n ℓ) :=
  (Finset.univ.filter fun ρ : ExactRestriction n ℓ =>
    clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ)

lemma clauseWitnessFamily_card {C : Core.CnfClause n}
    {F : Finset (Fin n)} (hFsubset : F ⊆ clauseIndexFinset (n := n) C)
    (hℓ : F.card ≤ ℓ) :
    (clauseWitnessFamily (n := n) (ℓ := ℓ) C F).card
      = Nat.choose
          (n - (clauseIndexFinset (n := n) C).card)
          (ℓ - F.card)
          * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + F.card) := by
  classical
  have hcard := clauseRestriction_card
    (n := n) (ℓ := ℓ) (C := C) (F := F) hFsubset hℓ
  have hfilter :
      (clauseWitnessFamily (n := n) (ℓ := ℓ) C F).card
        = Fintype.card
            {ρ : ExactRestriction n ℓ //
              clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ} := by
    simpa [clauseWitnessFamily]
      using (Fintype.card_subtype
        (p := fun ρ : ExactRestriction n ℓ =>
          clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ)).symm
  simpa [clauseWitnessCondition, hfilter, hFsubset]
    using hcard

lemma clauseWitnessFamily_subset_mem {C : Core.CnfClause n}
    {F : Finset (Fin n)} {ρ : ExactRestriction n ℓ}
    (hρ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F ρ) :
    ρ ∈ clauseWitnessFamily (n := n) (ℓ := ℓ) C F := by
  classical
  simpa [clauseWitnessFamily]
    using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρ⟩)

lemma clauseWitnessFamily_disjoint {C : Core.CnfClause n}
    {F₁ F₂ : Finset (Fin n)} (hF₁ : F₁ ⊆ clauseIndexFinset (n := n) C)
    (hF₂ : F₂ ⊆ clauseIndexFinset (n := n) C)
    (hneq : F₁ ≠ F₂) :
    Disjoint (clauseWitnessFamily (n := n) (ℓ := ℓ) C F₁)
      (clauseWitnessFamily (n := n) (ℓ := ℓ) C F₂) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro ρ hρ₁ hρ₂
  have hcond₁ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F₁ ρ := by
    have := Finset.mem_filter.mp hρ₁
    simpa [clauseWitnessFamily] using this.2
  have hcond₂ : clauseWitnessCondition (n := n) (ℓ := ℓ) C F₂ ρ := by
    have := Finset.mem_filter.mp hρ₂
    simpa [clauseWitnessFamily] using this.2
  have hinter₁ := clauseWitnessCondition_inter_eq
    (n := n) (ℓ := ℓ) (C := C) (F := F₁) (ρ := ρ) hcond₁
  have hinter₂ := clauseWitnessCondition_inter_eq
    (n := n) (ℓ := ℓ) (C := C) (F := F₂) (ρ := ρ) hcond₂
  have hsub₁ := clauseWitnessCondition_subset_clause
    (n := n) (ℓ := ℓ) (C := C) (F := F₁) (ρ := ρ) hcond₁
  have hsub₂ := clauseWitnessCondition_subset_clause
    (n := n) (ℓ := ℓ) (C := C) (F := F₂) (ρ := ρ) hcond₂
  have : F₁ = F₂ := by
    simpa [hinter₁, hinter₂]
  exact hneq this

/-- Кандидатные множества свободных литералов: все подмножества клаузы, у
которых как минимум `t` элементов и не больше `ℓ` (иначе в точной рестрикции
им просто не хватит свободных координат). -/
@[simp] def clauseSubsetCandidates (C : Core.CnfClause n)
    (ℓ t : Nat) : Finset (Finset (Fin n)) :=
  ((clauseIndexFinset (n := n) C).powerset.filter fun F =>
    t ≤ F.card ∧ F.card ≤ ℓ)

lemma clauseSubsetCandidates_mem {C : Core.CnfClause n}
    {ℓ t : Nat} {F : Finset (Fin n)}
    (hmem : F ∈ clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C) :
    F ⊆ clauseIndexFinset (n := n) C := by
  classical
  obtain ⟨hsubset, _⟩ := Finset.mem_filter.mp hmem
  exact (Finset.mem_powerset.mp hsubset)

lemma clauseSubsetCandidates_card_le {C : Core.CnfClause n}
    {ℓ t : Nat} {F : Finset (Fin n)}
    (hmem : F ∈ clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C) :
    F.card ≤ ℓ := by
  classical
  obtain ⟨_, hcond⟩ := Finset.mem_filter.mp hmem
  exact (and.right hcond)

/--
  В удобных обозначениях `clauseSubsetCandidates` — это семейство подмножеств
  клаузы, у которых мощность лежит в отрезке `[t, ℓ]`.  Фильтрация по точной
  мощности `k` совпадает с фильтрацией на полном `powerset`, если `k` лежит в
  указанном диапазоне.  Это наблюдение позволяет выражать число кандидатов
  через биномиальные коэффициенты.
-/
lemma clauseSubsetCandidates_filter_card_eq
    {C : Core.CnfClause n} {ℓ t k : Nat}
    (ht : t ≤ k) (hkℓ : k ≤ ℓ) :
    ((clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C)
        .filter fun F : Finset (Fin n) => F.card = k)
      = ((clauseIndexFinset (n := n) C).powerset
          .filter fun F : Finset (Fin n) => F.card = k) := by
  classical
  unfold clauseSubsetCandidates
  ext F; constructor <;> intro hF
  · obtain ⟨hmem, hcard⟩ := Finset.mem_filter.mp hF
    obtain ⟨hpow, _⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨hpow, hcard⟩
  · obtain ⟨hpow, hcard⟩ := Finset.mem_filter.mp hF
    have hbounds : t ≤ F.card ∧ F.card ≤ ℓ := by
      have hk : F.card = k := hcard
      exact ⟨by simpa [hk] using ht, by simpa [hk] using hkℓ⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hpow, hbounds⟩, hcard⟩

/--
  Число кандидатов мощности `k` совпадает с биномиальным коэффициентом
  `\binom{width}{k}`.  Условие `k ≤ width` не нужно явно указывать: при
  `k > width` биномиальный коэффициент автоматически обнуляется.
-/
lemma clauseSubsetCandidates_filter_card_card
    {C : Core.CnfClause n} {ℓ t k : Nat}
    (ht : t ≤ k) (hkℓ : k ≤ ℓ) :
    ((clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C)
        .filter fun F : Finset (Fin n) => F.card = k).card
      = Nat.choose C.width k := by
  classical
  have hfilter := clauseSubsetCandidates_filter_card_eq
    (n := n) (C := C) (ℓ := ℓ) (t := t) (k := k) ht hkℓ
  have hpow_filter :
      ((clauseIndexFinset (n := n) C).powerset
          .filter fun F : Finset (Fin n) => F.card = k)
        = (clauseIndexFinset (n := n) C).powersetCard k := by
    ext F; constructor <;> intro hF
    · obtain ⟨hsubset, hcard⟩ := Finset.mem_filter.mp hF
      exact Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩
    · obtain ⟨hsubset, hcard⟩ := Finset.mem_powersetCard.mp hF
      exact Finset.mem_filter.mpr ⟨hsubset, hcard⟩
  have hcard_powerset := Finset.card_powersetCard k
    (clauseIndexFinset (n := n) C)
  simpa [hfilter, hpow_filter, clauseIndexFinset_card (n := n) (C := C)]
    using hcard_powerset

/--
Если фиксированный параметр `k` лежит в диапазоне
`[t, min ℓ (|C|)]`, то он автоматически не превосходит глобальную ширину `w`
формулы.  Этот факт позволит позже подменять биномиальные коэффициенты
`\binom{|C|}{k}` на более грубые оценки через `w`.-/
lemma clauseCandidate_index_le_width {F : Core.CNF n w}
    {C : Core.CnfClause n} (hC : C ∈ F.clauses)
    {ℓ t k : Nat}
    (hk : k ∈ Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card)) :
    k ≤ w := by
  classical
  have hk_le : k ≤ Nat.min ℓ (clauseIndexFinset (n := n) C).card :=
    (Finset.mem_Icc.mp hk).2
  have hcard := clauseIndexFinset_card_le_width_of_mem
    (n := n) (w := w) (F := F) (C := C) hC
  have hmin_le : Nat.min ℓ (clauseIndexFinset (n := n) C).card ≤ w :=
    le_trans (Nat.min_le_right _ _) hcard
  exact le_trans hk_le hmin_le

/--
Биномиальный коэффициент для конкретной клаузы можно оценить через глобальную
ширину `w`: если `k` находится в допустимом диапазоне, то
`\binom{|C|}{k} ≤ (max 1 w)^k`.  Эта форма готовит почву для перевода сумм по
клаузам в стандартные оценки switching-леммы.-/
lemma clause_choose_le_pow_max {F : Core.CNF n w}
    {C : Core.CnfClause n} (hC : C ∈ F.clauses)
    {ℓ t k : Nat}
    (hk : k ∈ Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card)) :
    Nat.choose (clauseIndexFinset (n := n) C).card k
      ≤ (Nat.max 1 w) ^ k := by
  classical
  -- Сначала применяем общую оценку `choose ≤ (max 1 D)^k` из блока
  -- `Counting.BinomialBounds`.
  have hchoose := Counting.choose_le_pow_max
    (D := (clauseIndexFinset (n := n) C).card) (i := k)
  -- Учитываем, что `|C| ≤ w`, поэтому база степени также не превосходит
  -- `max 1 w`.
  have hbase_le : Nat.max 1 (clauseIndexFinset (n := n) C).card
      ≤ Nat.max 1 w := by
    have hcard := clauseIndexFinset_card_le_width_of_mem
      (n := n) (w := w) (F := F) (C := C) hC
    exact max_le_max le_rfl hcard
  -- Монотонность степени по основанию переводит полученное неравенство в нужный вид.
  have hpos : 1 ≤ Nat.max 1 (clauseIndexFinset (n := n) C).card :=
    le_max_left _ _
  have hmono := Nat.pow_le_pow_of_le_left hpos hbase_le k
  -- Собираем цепочку оценок.
  exact hchoose.trans hmono

/--
  Сумму по всем кандидатам можно перегруппировать по мощности и выразить через
  биномиальные коэффициенты.  Это главный технический шаг перед оценкой
  вероятности.
-/
lemma clauseBadFamily_card_sum_by_card {C : Core.CnfClause n} {ℓ t : Nat} :
    ∑ F in clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C,
        Nat.choose (n - (clauseIndexFinset (n := n) C).card)
          (ℓ - F.card)
          * Nat.pow 2
              (n - (clauseIndexFinset (n := n) C).card + F.card)
      = ∑ k in Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
          Nat.choose (clauseIndexFinset (n := n) C).card k
            * (Nat.choose (n - (clauseIndexFinset (n := n) C).card)
                (ℓ - k)
                * Nat.pow 2
                    (n - (clauseIndexFinset (n := n) C).card + k)) := by
  classical
  set S := clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C
  set m := Nat.min ℓ (clauseIndexFinset (n := n) C).card
  let g : Nat → Nat :=
    fun k =>
      Nat.choose (n - (clauseIndexFinset (n := n) C).card) (ℓ - k)
        * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + k)
  have hcard_range : ∀ F ∈ S, F.card ∈ Finset.Icc t m := by
    intro F hF
    obtain ⟨hsubset, hbounds⟩ := Finset.mem_filter.mp hF
    have hwidth : F.card ≤ (clauseIndexFinset (n := n) C).card :=
      Finset.card_le_of_subset (Finset.mem_powerset.mp hsubset)
    have hℓ : F.card ≤ ℓ := (and.right hbounds)
    have ht : t ≤ F.card := (and.left hbounds)
    refine Finset.mem_Icc.mpr ?_
    constructor
    · exact ht
    · have hmin :
        F.card ≤ Nat.min ℓ (clauseIndexFinset (n := n) C).card :=
          Nat.le_min hℓ hwidth
      simpa [m] using hmin
  have hsum_decompose :
      ∑ F in S, g F.card
        = ∑ k in Finset.Icc t m,
            g k * ((S.filter fun F : Finset (Fin n) => F.card = k).card) := by
    have hrewrite : ∀ F ∈ S,
        g F.card
          = ∑ k in Finset.Icc t m, g k * (if F.card = k then 1 else 0) := by
      intro F hF
      have hmem := hcard_range F hF
      have hbasic :
          ∑ k in Finset.Icc t m, (if F.card = k then g k else 0) = g F.card := by
        refine Finset.sum_eq_single_of_mem hmem ?_
        intro k hk hkneq
        simp [hkneq.symm]
      have hmul :
          ∑ k in Finset.Icc t m, g k * (if F.card = k then 1 else 0)
            = ∑ k in Finset.Icc t m, (if F.card = k then g k else 0) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        split_ifs with h
        · simp [h]
        · simp [h]
      exact (hmul.trans hbasic).symm
    have hrewrite_sum :
        ∑ F in S, g F.card
          = ∑ F in S, ∑ k in Finset.Icc t m, g k * (if F.card = k then 1 else 0) := by
      refine Finset.sum_congr rfl ?_
      intro F hF; exact (hrewrite F hF).symm
    have hswap := Finset.sum_comm
      (s := S) (t := Finset.Icc t m)
      (f := fun F k => g k * (if F.card = k then 1 else 0))
    have hpull :
        ∑ k in Finset.Icc t m, ∑ F in S, g k * (if F.card = k then 1 else 0)
          = ∑ k in Finset.Icc t m, g k *
              (∑ F in S, if F.card = k then 1 else 0) := by
      simp [Finset.mul_sum]
    have hcount :
        ∑ F in S, if F.card = k then 1 else 0
          = (S.filter fun F : Finset (Fin n) => F.card = k).card := by
      simpa [Finset.card_filter] using
        (Finset.card_filter (s := S) (p := fun F : Finset (Fin n) => F.card = k)).symm
    have hfinal :
        ∑ k in Finset.Icc t m, g k *
              (∑ F in S, if F.card = k then 1 else 0)
          = ∑ k in Finset.Icc t m, g k *
              ((S.filter fun F : Finset (Fin n) => F.card = k).card) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact congrArg (fun x => g k * x) (hcount (k := k))
    calc
      ∑ F in S, g F.card
          = ∑ F in S, ∑ k in Finset.Icc t m, g k * (if F.card = k then 1 else 0) :=
            hrewrite_sum
      _ = ∑ k in Finset.Icc t m, ∑ F in S, g k * (if F.card = k then 1 else 0) :=
            hswap
      _ = ∑ k in Finset.Icc t m, g k *
              (∑ F in S, if F.card = k then 1 else 0) := hpull
      _ = ∑ k in Finset.Icc t m, g k *
              ((S.filter fun F : Finset (Fin n) => F.card = k).card) := hfinal
  have hrewrite_sum :
      ∑ k in Finset.Icc t m, g k *
          ((S.filter fun F : Finset (Fin n) => F.card = k).card)
        = ∑ k in Finset.Icc t m,
            Nat.choose (clauseIndexFinset (n := n) C).card k * g k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_bounds : t ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_min := (Finset.mem_Icc.mp hk).2
    have hkℓ : k ≤ ℓ := (Nat.le_min_iff.1 hk_min).1
    have hcard := clauseSubsetCandidates_filter_card_card
      (n := n) (C := C) (ℓ := ℓ) (t := t) (k := k) hk_bounds hkℓ
    simpa [S, g, clauseIndexFinset_card (n := n) (C := C), Nat.mul_comm] using hcard.symm
  simpa [S, g, m, clauseIndexFinset_card (n := n) (C := C)]
    using (hsum_decompose.trans hrewrite_sum)

lemma clauseBadFamily_card_eq_cardDecomposed {C : Core.CnfClause n} {ℓ t : Nat} :
    (clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card
      = ∑ k in Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
          Nat.choose (clauseIndexFinset (n := n) C).card k
            * Nat.choose (n - (clauseIndexFinset (n := n) C).card) (ℓ - k)
            * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + k) := by
  classical
  have hsum := clauseBadFamily_card_eq_sum
    (n := n) (ℓ := ℓ) (t := t) (C := C)
  have hdecompose := clauseBadFamily_card_sum_by_card
    (n := n) (ℓ := ℓ) (t := t) (C := C)
  have hrewrite :
      ∑ k in Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
          Nat.choose (clauseIndexFinset (n := n) C).card k *
            (Nat.choose (n - (clauseIndexFinset (n := n) C).card) (ℓ - k)
              * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + k))
        = ∑ k in Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
            Nat.choose (clauseIndexFinset (n := n) C).card k
              * Nat.choose (n - (clauseIndexFinset (n := n) C).card) (ℓ - k)
              * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
  exact hsum.trans (hrewrite.trans hdecompose)


lemma clauseBadFamily_card_eq_sum {C : Core.CnfClause n} {ℓ t : Nat} :
    (clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card
      = ∑ F in clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C,
          Nat.choose
              (n - (clauseIndexFinset (n := n) C).card)
              (ℓ - F.card)
              * Nat.pow 2
                  (n - (clauseIndexFinset (n := n) C).card + F.card) := by
  classical
  have hdisjoint :
      (clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C).PairwiseDisjoint
        (fun F => clauseWitnessFamily (n := n) (ℓ := ℓ) C F) := by
    refine Finset.pairwiseDisjoint_iff.mpr ?_
    intro F₁ hF₁ F₂ hF₂ hneq
    have hsub₁ := clauseSubsetCandidates_mem
      (n := n) (ℓ := ℓ) (t := t) (C := C) (F := F₁) hF₁
    have hsub₂ := clauseSubsetCandidates_mem
      (n := n) (ℓ := ℓ) (t := t) (C := C) (F := F₂) hF₂
    exact clauseWitnessFamily_disjoint
      (n := n) (ℓ := ℓ) (C := C) (F₁ := F₁) (F₂ := F₂)
      hsub₁ hsub₂ hneq
  have hcard_bind := Finset.card_bind
    (s := clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C)
    (t := fun F => clauseWitnessFamily (n := n) (ℓ := ℓ) C F)
    hdisjoint
  -- `Finset.card_bind` уже даёт нужное равенство в натуральных числах.
  -- Просто раскрываем сокращения и используем ранее доказанную формулу для
  -- каждой фиксированной `F`.
  have hcard_explicit :
      (clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card
        = ∑ F in clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C,
            (clauseWitnessFamily (n := n) (ℓ := ℓ) C F).card := by
    simpa [clauseBadFamily]
      using hcard_bind
  refine hcard_explicit.trans ?_
  refine Finset.sum_congr rfl ?_
  intro F hF
  have hsubset := clauseSubsetCandidates_mem
    (n := n) (ℓ := ℓ) (t := t) (C := C) (F := F) hF
  have hle := clauseSubsetCandidates_card_le
    (n := n) (ℓ := ℓ) (t := t) (C := C) (F := F) hF
  simpa using clauseWitnessFamily_card
    (n := n) (ℓ := ℓ) (C := C) (F := F) hsubset hle

lemma clauseBadFamily_uniformMass {C : Core.CnfClause n} {ℓ t : Nat} :
    ∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C,
        restrictionUniform n ℓ ρ
      = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞) := by
  classical
  set mass : ℝ≥0∞ :=
      (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) with hmass_def
  have hmass_apply :
      ∀ ρ : ExactRestriction n ℓ, restrictionUniform n ℓ ρ = mass := by
    intro ρ
    simpa [mass, hmass_def] using uniform_mass_const (n := n) (ℓ := ℓ) ρ
  have hconst_sum :
      ∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C, mass
        = ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞)
            * mass := by
    simpa [nsmul_eq_mul]
      using Finset.sum_const
        (s := clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C) (a := mass)
  have hrewrite :
      (∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C,
          restrictionUniform n ℓ ρ)
        = ∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C, mass := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    exact hmass_apply ρ
  simpa [mass, hmass_def, hrewrite]
    using hconst_sum

namespace Depth1Switching

open Core
open RandomRestriction

variable {n ℓ w : Nat}

/--
  Для каждой pending-клаузы удобно выделить множество её свободных индексов в
  виде конечного множества.  Мы берём список `freeLiterals`, возвращаемых
  инфраструктурой `Core.Restriction`, и забываем про порядок, оставляя только
  индексы.
-/
@[simp] def pendingFreeSet (ρ : ExactRestriction n ℓ)
    (C : Core.CnfClause n) : Finset (Fin n) :=
  ((ρ.toRestriction.freeLiterals C).map (fun ℓ => ℓ.idx)).toFinset

lemma pendingFreeSet_subset_clause {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n} :
    pendingFreeSet (n := n) (ℓ := ℓ) ρ C ⊆ clauseIndexFinset (n := n) C := by
  classical
  intro i hi
  obtain ⟨ℓ, hmemFree, hidx⟩ :=
    List.mem_toFinset.mp hi
  have hmemClause : ℓ ∈ C.literals :=
    (Core.Restriction.mem_freeLiterals (ρ := ρ.toRestriction)
      (C := C) (ℓ := ℓ)).1 hmemFree |>.1
  have : ℓ.idx ∈ clauseIndexFinset (n := n) C := by
    simpa [clauseIndexFinset]
      using List.mem_toFinset.mpr
        (List.mem_map.2 ⟨ℓ, hmemClause, rfl⟩)
  simpa [pendingFreeSet, hidx]
    using this

lemma pendingFreeSet_subset_axis {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n} :
    pendingFreeSet (n := n) (ℓ := ℓ) ρ C ⊆ ρ.axis.support := by
  classical
  intro i hi
  obtain ⟨ℓ, hmemFree, hidx⟩ := List.mem_toFinset.mp hi
  have hstatus : ρ.toRestriction.literalStatus ℓ
      = Core.LiteralStatus.unassigned :=
    (Core.Restriction.mem_freeLiterals (ρ := ρ.toRestriction)
        (C := C) (ℓ := ℓ)).1 hmemFree |>.2
  have hmask := (Core.Restriction.literalStatus_eq_unassigned
      (ρ := ρ.toRestriction) (ℓ := ℓ)).1 hstatus
  have hlist : ℓ.idx ∈ ρ.toRestriction.freeIndicesList :=
    (Core.Restriction.mem_freeIndicesList (ρ := ρ.toRestriction)
      (i := ℓ.idx)).2 hmask
  have hfinset : ℓ.idx ∈ ρ.toRestriction.freeIndicesList.toFinset :=
    List.mem_toFinset.mpr hlist
  simpa [pendingFreeSet, hidx,
        ExactRestriction.toRestriction_freeIndicesList_toFinset]
    using hfinset

lemma pendingFreeSet_card {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n} :
    (pendingFreeSet (n := n) (ℓ := ℓ) ρ C).card
      = (ρ.toRestriction.freeLiterals C).length := by
  classical
  have hsub : (ρ.toRestriction.freeLiterals C)
      .Sublist C.literals := by
    -- `freeLiterals` строится фильтрацией исходного списка клауз.
    simpa [Core.Restriction.freeLiterals]
      using List.filter_sublist
        (l := C.literals)
        (p := fun ℓ =>
          decide (ρ.toRestriction.literalStatus ℓ
            = Core.LiteralStatus.unassigned))
  have hnodup :
      ( (ρ.toRestriction.freeLiterals C).map fun ℓ => ℓ.idx).Nodup := by
    have hmapSub :
        ((ρ.toRestriction.freeLiterals C).map fun ℓ => ℓ.idx)
          .Sublist (C.literals.map fun ℓ => ℓ.idx) :=
      List.Sublist.map fun ℓ => ℓ.idx hsub
    have hclause :
        (C.literals.map fun ℓ => ℓ.idx).Nodup := C.nodupIdx
    exact List.Sublist.nodup hmapSub hclause
  have hcard := List.card_toFinset
    ((ρ.toRestriction.freeLiterals C).map fun ℓ => ℓ.idx)
  have hdedup :
      ((ρ.toRestriction.freeLiterals C).map fun ℓ => ℓ.idx).dedup
        = (ρ.toRestriction.freeLiterals C).map fun ℓ => ℓ.idx :=
    (List.dedup_eq_self).2 hnodup
  have hlen := congrArg List.length hdedup
  have hrewrite :
      (pendingFreeSet (n := n) (ℓ := ℓ) ρ C).card =
        ((ρ.toRestriction.freeLiterals C).map fun ℓ => ℓ.idx).length := by
    simpa [pendingFreeSet, hdedup] using hcard
  -- Преобразуем длину списка индексов в длину исходного списка литералов.
  have := List.length_map (ρ.toRestriction.freeLiterals C)
      (fun ℓ : Core.Literal n => ℓ.idx)
  simpa [hrewrite] using this.symm

/--
Количество свободных литералов в pending-клаузе не превосходит числа свободных
переменных в точном ограничении.  Это прямое следствие того, что множество
`pendingFreeSet` включено в опору оси точной рестрикции.-/
lemma pendingFreeSet_card_le_freeCount {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n} :
    (pendingFreeSet (n := n) (ℓ := ℓ) ρ C).card
      ≤ ρ.toRestriction.freeCount := by
  classical
  have hsubset := pendingFreeSet_subset_axis
    (n := n) (ℓ := ℓ) (ρ := ρ) (C := C)
  have haxis : (pendingFreeSet (n := n) (ℓ := ℓ) ρ C).card
      ≤ (ρ.axis.support).card :=
    Finset.card_le_of_subset hsubset
  have hcount' : (ρ.axis.support).card = ρ.toRestriction.freeCount := by
    simpa [RandomRestriction.toRestriction_freeCount (ρ := ρ)]
      using RandomRestriction.freeCount (ρ := ρ)
  have htarget : (pendingFreeSet (n := n) (ℓ := ℓ) ρ C).card
      ≤ ρ.toRestriction.freeCount := by
    simpa [hcount'] using haxis
  exact htarget

/--
Длину списка свободных литералов pending-клаузы можно ограничить сверху через
глобальный счётчик свободных координат точного ограничения.-/
lemma pendingFreeLiterals_length_le_freeCount {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n} :
    (ρ.toRestriction.freeLiterals C).length
      ≤ ρ.toRestriction.freeCount := by
  classical
  have hcard := pendingFreeSet_card
    (n := n) (ℓ := ℓ) (ρ := ρ) (C := C)
  have hbound := pendingFreeSet_card_le_freeCount
    (n := n) (ℓ := ℓ) (ρ := ρ) (C := C)
  simpa [hcard] using hbound

lemma pendingFreeSet_subset_clauseAssigned {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n} {i : Fin n}
    (hi : i ∈ pendingFreeSet (n := n) (ℓ := ℓ) ρ C) :
    i ∈ clauseIndexFinset (n := n) C :=
  (pendingFreeSet_subset_clause (ρ := ρ) (C := C)) hi

/--
  Pending-клауза задаёт ровно те условия, которые описаны в
  `clauseWitnessCondition`: множество свободных индексов совпадает с
  `pendingFreeSet`, остальные литералы принудительно выставлены в ложь.
-/
lemma pendingWitness_condition {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n}
    {w : Core.Restriction.ClausePendingWitness ρ.toRestriction C}
    (hstatus : ρ.toRestriction.clauseStatus C
        = Core.Restriction.ClauseStatus.pending w) :
    clauseWitnessCondition (n := n) (ℓ := ℓ) (C := C)
        (F := pendingFreeSet (n := n) (ℓ := ℓ) ρ C) ρ := by
  classical
  refine ⟨pendingFreeSet_subset_clause (ρ := ρ) (C := C), ?_⟩
  have hsubsetAxis := pendingFreeSet_subset_axis
    (ρ := ρ) (C := C)
  refine ⟨hsubsetAxis, ?_, ?_⟩
  · -- Достаточно сослаться на уже доказанное свойство дизъюнктности.
    exact clauseAssignedSet_disjoint (n := n) (C := C)
      (F := pendingFreeSet (n := n) (ℓ := ℓ) ρ C)
      (pendingFreeSet_subset_clause (ρ := ρ) (C := C))
  · intro i hiAssigned
    obtain ⟨hiClause, hiNotFree⟩ := Finset.mem_sdiff.mp hiAssigned
    -- Найдём соответствующий литерал клаузы.
    obtain ⟨ℓlit, hℓClause, hidx⟩ :=
      (clauseIndexFinset_mem (n := n) (C := C) (i := i)).1 hiClause
    -- Литерал не входит в список свободных.
    have hnotFree : ℓlit ∉ ρ.toRestriction.freeLiterals C := by
      intro hmem
      have : ℓlit.idx ∈ pendingFreeSet (n := n) (ℓ := ℓ) ρ C := by
        refine List.mem_toFinset.mpr ?_
        exact ⟨ℓlit, hmem, rfl⟩
      have : i ∈ pendingFreeSet (n := n) (ℓ := ℓ) ρ C := by
        simpa [pendingFreeSet, hidx]
          using this
      exact hiNotFree this
    -- Следовательно, статус литерала — `falsified`.
    have hstatusLit :
        ρ.toRestriction.literalStatus ℓlit = Core.LiteralStatus.falsified := by
      have hnotUnassigned :
          ρ.toRestriction.literalStatus ℓlit
            ≠ Core.LiteralStatus.unassigned := by
        intro hfree
        have hmem : ℓlit ∈ ρ.toRestriction.freeLiterals C := by
          refine (Core.Restriction.mem_freeLiterals (ρ := ρ.toRestriction)
            (C := C) (ℓ := ℓlit)).2 ?_
          exact ⟨hℓClause, hfree⟩
        exact hnotFree hmem
      have hnoSat := w.noSatisfied ℓlit hℓClause
      have hcases :=
        Core.LiteralStatus.eq_satisfied_or_eq_falsified_or_eq_unassigned
          (ρ.toRestriction.literalStatus ℓlit)
      rcases hcases with hsat | hsat | hunsat
      · exact (hnoSat hsat).elim
      · exact hsat
      · exact (hnotUnassigned hunsat).elim
    -- Расшифровываем статус `falsified` в терминах маски.
    obtain ⟨b, hmask, hbneq⟩ :=
      (Core.Restriction.literalStatus_eq_falsified
        (ρ := ρ.toRestriction) (ℓ := ℓlit)).1 hstatusLit
    -- На фиксированных координатах маска точного ограничения совпадает с `ρ.values`.
    have hnotSupport : i ∉ ρ.axis.support := by
      intro hmem
      have : i ∈ pendingFreeSet (n := n) (ℓ := ℓ) ρ C :=
        hsubsetAxis hmem
      exact hiNotFree this
    have hmaskValues : ρ.toRestriction.mask i = some (ρ.values i) :=
      ExactRestriction.toRestriction_mask_not_mem_support
        (ρ := ρ) (i := i) hnotSupport
    have hmaskValues' : ρ.toRestriction.mask ℓlit.idx = some (ρ.values i) := by
      simpa [ExactRestriction.toRestriction_mask, hidx]
        using hmaskValues
    have hmask_eq : some (ρ.values i) = some b := by
      have := Eq.trans hmaskValues' (Eq.symm hmask)
      simpa [ExactRestriction.toRestriction_mask, hidx] using this
    have hvalues_eq : ρ.values i = b := Option.some.inj hmask_eq
    have hvalues_compl : ρ.values i = !ℓlit.value := by
      cases hval : ℓlit.value with
      | false =>
          have hbtrue : b = true := by
            cases hb : b with
            | false =>
                have : False := by simpa [hb, hval] using hbneq
                cases this
            | true => rfl
          simpa [hvalues_eq, hval, hbtrue]
      | true =>
          have hbfalse : b = false := by
            cases hb : b with
            | false => rfl
            | true =>
                have : False := by simpa [hb, hval] using hbneq
                cases this
          simpa [hvalues_eq, hval, hbfalse]
    -- Сопоставляем с заранее определённым назначением `clauseFalseAssignment`.
    have hfalse := clauseFalseAssignment_eval
      (n := n) (C := C) (lit := ℓlit) hℓClause
    have hfalse' : clauseFalseAssignment (n := n) (C := C) i
        = !ℓlit.value := by
      simpa [hidx] using hfalse
    -- Заключаем требуемое равенство значений.
    simpa [hfalse', hvalues_compl]

lemma pendingWitness_mem_clauseWitnessFamily {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n}
    {w : Core.Restriction.ClausePendingWitness ρ.toRestriction C}
    (hstatus : ρ.toRestriction.clauseStatus C
        = Core.Restriction.ClauseStatus.pending w) :
    ρ ∈ clauseWitnessFamily (n := n) (ℓ := ℓ) C
        (pendingFreeSet (n := n) (ℓ := ℓ) ρ C) := by
  classical
  have hcond := pendingWitness_condition
    (ρ := ρ) (C := C) (w := w) hstatus
  exact clauseWitnessFamily_subset_mem (n := n) (ℓ := ℓ)
    (C := C) (F := pendingFreeSet (n := n) (ℓ := ℓ) ρ C) hcond

lemma pendingWitness_mem_clauseBadFamily {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n}
    {w : Core.Restriction.ClausePendingWitness ρ.toRestriction C}
    {t : Nat}
    (hstatus : ρ.toRestriction.clauseStatus C
        = Core.Restriction.ClauseStatus.pending w)
    (ht : t ≤ (ρ.toRestriction.freeLiterals C).length) :
    ρ ∈ clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C := by
  classical
  set F := pendingFreeSet (n := n) (ℓ := ℓ) ρ C
  have hsubsetClause := pendingFreeSet_subset_clause
    (ρ := ρ) (C := C)
  have hsubsetAxis := pendingFreeSet_subset_axis
    (ρ := ρ) (C := C)
  have hcard_eq : F.card = (ρ.toRestriction.freeLiterals C).length :=
    pendingFreeSet_card (ρ := ρ) (C := C)
  have hcard_le : F.card ≤ ℓ := by
    have hle := Finset.card_le_of_subset hsubsetAxis
    simpa [F, ExactRestriction.freeCount (ρ := ρ)] using hle
  have hcard_ge : t ≤ F.card := by
    simpa [F, hcard_eq] using ht
  have hmemCandidates :
      F ∈ clauseSubsetCandidates (n := n) (ℓ := ℓ) (t := t) C := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · refine Finset.mem_powerset.mpr ?_
      exact hsubsetClause
    · exact ⟨hcard_ge, hcard_le⟩
  refine Finset.mem_bind.mpr ?_
  refine ⟨F, hmemCandidates, ?_⟩
  exact pendingWitness_mem_clauseWitnessFamily
    (ρ := ρ) (C := C) (w := w) hstatus

/-- Рестрикция считается «плохой», если глубина PDT после неё превышает `t`. -/
@[simp] def BadRestriction (F : Core.CNF n w) (t : Nat)
    (ρ : ExactRestriction n ℓ) : Prop :=
  Restriction.hasDecisionTreeOfDepth ρ.toRestriction F.eval t = false

@[simp] lemma badRestriction_iff (F : Core.CNF n w) (t : Nat)
    (ρ : ExactRestriction n ℓ) :
    BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ ↔
      Restriction.hasDecisionTreeOfDepth ρ.toRestriction F.eval t = false :=
  Iff.rfl

/-- Носитель «плохих» рестрикций как конечное множество. -/
@[simp] def badSet (F : Core.CNF n w) (ℓ t : Nat) :
    Finset (ExactRestriction n ℓ) :=
  Finset.univ.filter (fun ρ =>
    Restriction.hasDecisionTreeOfDepth ρ.toRestriction F.eval t = false)

@[simp] lemma mem_badSet {F : Core.CNF n w} {ℓ t : Nat}
    {ρ : ExactRestriction n ℓ} :
    ρ ∈ badSet (n := n) (w := w) F ℓ t ↔ BadRestriction (F := F) (t := t) ρ := by
  classical
  unfold badSet BadRestriction
  simp

/--
  Из факта «глубина дерева больше `t`» можно извлечь pending-клаузу и явного
  свидетеля `ClausePendingWitness`.  Вспомогательный namespace `Internal`
  содержит технические леммы для этого перехода.
-/
namespace Internal

open Core

/-- Вспомогательный конструктор: из расширений `xFalse` и `yTrue` строит
pending-клаузу с явным свидетелем. -/
private lemma mk_pendingClause
    {F : Core.CNF n w} {ρ : Core.Restriction n}
    {xFalse yTrue : Core.BitVec n}
    (hxFalse : ρ.restrict F.eval xFalse = false)
    (hyTrue : ρ.restrict F.eval yTrue = true) :
    ∃ C ∈ F.clauses,
      ∃ witness : Core.Restriction.ClausePendingWitness ρ C,
        ρ.clauseStatus C = Core.Restriction.ClauseStatus.pending witness := by
  classical
  have hxEval : F.eval (ρ.override xFalse) = false := by
    simpa [Core.Restriction.restrict] using hxFalse
  have hyEval : F.eval (ρ.override yTrue) = true := by
    simpa [Core.Restriction.restrict] using hyTrue
  obtain ⟨C, hCmem, hCfalse⟩ :=
    List.all_eq_false.mp (by simpa [Core.CNF.eval] using hxEval)
  have hallTrue :=
    List.all_eq_true.mp (by simpa [Core.CNF.eval] using hyEval)
  have hCtrue : Core.CnfClause.eval C (ρ.override yTrue) = true :=
    hallTrue C hCmem
  have hfalseLit :=
    (Core.CnfClause.eval_eq_false_iff (C := C) (x := ρ.override xFalse)).1 hCfalse
  obtain ⟨ℓtrue, hℓtrue_mem, hℓtrue_eval⟩ :=
    (Core.CnfClause.eval_eq_true_iff (C := C) (x := ρ.override yTrue)).1 hCtrue
  have hnoSatisfied : ∀ ℓ ∈ C.literals,
      ρ.literalStatus ℓ ≠ Core.LiteralStatus.satisfied := by
    intro ℓ hℓ hstatus
    have htrue := Core.Restriction.literalStatus_eval_override_true
      (ρ := ρ) (ℓ := ℓ) (x := xFalse) hstatus
    have : False := by simpa [htrue] using hfalseLit ℓ hℓ
    exact this.elim
  have hℓtrue_status : ρ.literalStatus ℓtrue = Core.LiteralStatus.unassigned := by
    classical
    have hnotSat := hnoSatisfied ℓtrue hℓtrue_mem
    cases hstatus : ρ.literalStatus ℓtrue with
    | satisfied => exact (hnotSat rfl).elim
    | falsified =>
        have hfalse := Core.Restriction.literalStatus_eval_override_false
          (ρ := ρ) (ℓ := ℓtrue) (x := yTrue) hstatus
        have : False := by simpa [hfalse] using hℓtrue_eval
        exact this.elim
    | unassigned => rfl
  have hfree_mem : ℓtrue ∈ ρ.freeLiterals C :=
    (Core.Restriction.mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓtrue)).2
      ⟨hℓtrue_mem, hℓtrue_status⟩
  have hfree_nonempty : ρ.freeLiterals C ≠ [] := by
    intro hnil
    have : ℓtrue ∈ ([] : List (Core.Literal n)) := by
      simpa [hnil] using hfree_mem
    exact (List.not_mem_nil _ this)
  let witness : Core.Restriction.ClausePendingWitness ρ C :=
    { free := ρ.freeLiterals C
      , subset := by
          intro ℓ hℓ
          obtain ⟨hclause, _⟩ :=
            (Core.Restriction.mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓ)).1 hℓ
          exact hclause
      , unassigned := by
          intro ℓ hℓ
          obtain ⟨_, hfree⟩ :=
            (Core.Restriction.mem_freeLiterals (ρ := ρ) (C := C) (ℓ := ℓ)).1 hℓ
          exact hfree
      , nonempty := hfree_nonempty
      , noSatisfied := by
          intro ℓ hℓ
          exact hnoSatisfied ℓ hℓ }
  have hnoSatAll : ¬ ∃ ℓ ∈ C.literals,
      ρ.literalStatus ℓ = Core.LiteralStatus.satisfied := by
    intro hex
    obtain ⟨ℓ, hℓ, hstatus⟩ := hex
    exact (hnoSatisfied ℓ hℓ hstatus).elim
  refine ⟨C, hCmem, witness, ?_⟩
  unfold Core.Restriction.clauseStatus
  simp [hnoSatAll, hfree_nonempty, witness]

/--
Если формула после ограничения не стала константой, то существует pending-клауза
с явным свидетелем.
-/
lemma exists_pendingClause_of_nonconstant
    {F : Core.CNF n w} {ρ : Core.Restriction n}
    (hconst : ρ.isConstantOn F.eval = false) :
    ∃ C ∈ F.clauses,
      ∃ witness : Core.Restriction.ClausePendingWitness ρ C,
        ρ.clauseStatus C = Core.Restriction.ClauseStatus.pending witness := by
  classical
  have hprop : ¬ (∀ x y : Core.BitVec n,
      ρ.restrict F.eval x = ρ.restrict F.eval y) := by
    simpa [Core.Restriction.isConstantOn]
      using (decide_eq_false_iff
        (p := ∀ x y : Core.BitVec n,
          ρ.restrict F.eval x = ρ.restrict F.eval y)).1 hconst
  obtain ⟨x, hx⟩ := not_forall.mp hprop
  have hx' : ¬ (∀ y, ρ.restrict F.eval x = ρ.restrict F.eval y) := hx
  obtain ⟨y, hneq⟩ := not_forall.mp hx'
  cases hxVal : ρ.restrict F.eval x with
  | false =>
      have hyVal : ρ.restrict F.eval y = true := by
        cases hyVal : ρ.restrict F.eval y with
        | false =>
            have : ρ.restrict F.eval x = ρ.restrict F.eval y := by
              simpa [hxVal, hyVal]
            exact (hneq this).elim
        | true => rfl
      exact mk_pendingClause (F := F) (ρ := ρ)
        (xFalse := x) (yTrue := y)
        (by simpa [hxVal]) (by simpa [hyVal])
  | true =>
      have hyVal : ρ.restrict F.eval y = false := by
        cases hyVal : ρ.restrict F.eval y with
        | false => rfl
        | true =>
            have : ρ.restrict F.eval x = ρ.restrict F.eval y := by
              simpa [hxVal, hyVal]
            exact (hneq this).elim
      exact mk_pendingClause (F := F) (ρ := ρ)
        (xFalse := y) (yTrue := x)
        (by simpa [hyVal]) (by simpa [hxVal])

/--
Неудача проверки глубины `t` даёт pending-клаузу в исходном точном ограничении.
-/
lemma exists_pendingClause_of_badRestriction
    {F : Core.CNF n w} {ρ : ExactRestriction n ℓ} {t : Nat}
    (hbad : BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ) :
    ∃ C ∈ F.clauses,
      ∃ witness : Core.Restriction.ClausePendingWitness ρ.toRestriction C,
        ρ.toRestriction.clauseStatus C
          = Core.Restriction.ClauseStatus.pending witness := by
  classical
  have hconst : ρ.toRestriction.isConstantOn F.eval = false := by
    cases t with
    | zero =>
        simpa [BadRestriction,
          Core.Restriction.hasDecisionTreeOfDepth_zero] using hbad
    | succ t' =>
        have hval := hbad
        have hnotTrue : ρ.toRestriction.isConstantOn F.eval ≠ true := by
          intro htrue
          have :
              Core.Restriction.hasDecisionTreeOfDepth ρ.toRestriction F.eval
                (Nat.succ t') = true := by
            simp [Core.Restriction.hasDecisionTreeOfDepth, htrue]
          simpa [this] using hval
        cases hbool : ρ.toRestriction.isConstantOn F.eval with
        | false => exact hbool
        | true => exact (hnotTrue hbool).elim
  obtain ⟨C, hCmem, witness, hstatus⟩ :=
    exists_pendingClause_of_nonconstant
      (F := F) (ρ := ρ.toRestriction) hconst
  exact ⟨C, hCmem, witness, hstatus⟩

end Internal

/-- Для базового случая `t = 0` любая «плохая» рестрикция сразу попадает в
формульное «плохое» семейство: pending-свидетель предоставляет необходимое
неравенство на длину списка свободных литералов. -/
lemma badRestriction_mem_formulaBadFamily_zero
    {F : Core.CNF n w} {ρ : ExactRestriction n ℓ}
    (hbad : BadRestriction (n := n) (ℓ := ℓ) (w := w) F 0 ρ) :
    ρ ∈ formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F 0 := by
  classical
  obtain ⟨C, hC, witness, hstatus⟩ :=
    Internal.exists_pendingClause_of_badRestriction
      (n := n) (ℓ := ℓ) (w := w) (F := F) (t := 0)
      (ρ := ρ) hbad
  have hlen : 0 ≤ (ρ.toRestriction.freeLiterals C).length := Nat.zero_le _
  exact pendingWitness_mem_formulaBadFamily
    (n := n) (ℓ := ℓ) (w := w) (F := F) (ρ := ρ)
    (hC := hC) (witness := witness) hstatus hlen

/--
Неудача проверки глубины гарантирует наличие свободных переменных: список
`freeIndicesList` точного ограничения непуст, а значит, свободный счётчик
положителен.  Этот факт понадобится при извлечении конкретного литерала, по
которому будем продолжать каноническую ветку.
-/
lemma badRestriction_freeCount_pos
    {F : Core.CNF n w} {ρ : ExactRestriction n ℓ} {t : Nat}
    (hbad : BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ) :
    0 < ρ.toRestriction.freeCount := by
  classical
  obtain ⟨C, hC, witness, hstatus⟩ :=
    Internal.exists_pendingClause_of_badRestriction
      (n := n) (ℓ := ℓ) (w := w) (F := F) (t := t)
      (ρ := ρ) hbad
  obtain ⟨ℓlit, hℓmem, _⟩ :=
    Core.ClausePendingWitness.exists_unassigned (w := witness)
  have hfree : ℓlit.idx ∈ ρ.toRestriction.freeIndicesList := by
    exact Core.ClausePendingWitness.literal_idx_mem_freeIndicesList
      (ρ := ρ.toRestriction) (C := C) (w := witness)
      (ℓ := ℓlit) hℓmem
  exact Core.Restriction.freeCount_pos_of_mem_freeIndicesList
    (ρ := ρ.toRestriction) (i := ℓlit.idx) hfree

/--
Если ограничение `ρ` проваливает проверку глубины `t`, то число свободных
переменных в маске не меньше `t`.  Доказательство повторяет рекурсивное
определение `Restriction.hasDecisionTreeOfDepth`: из провала на уровне
`t + 1` мы выбираем свободный индекс, фиксируем его и переходим к одной из
ветвей, где всё ещё наблюдается провал на глубине `t`.  Операция `assign`
уменьшает число свободных координат ровно на единицу, что и даёт итоговую
оценку `t ≤ ρ.freeCount`.-/
lemma hasDecisionTree_false_freeCount_le
    {ρ : Core.Restriction n} {f : Core.BitVec n → Bool} {t : Nat}
    (hfail : Core.Restriction.hasDecisionTreeOfDepth ρ f t = false) :
    t ≤ ρ.freeCount := by
  classical
  revert ρ
  induction t with
  | zero =>
      intro ρ _
      exact Nat.zero_le _
  | succ t ih =>
      intro ρ hdepth
      -- Переписываем определение `hasDecisionTreeOfDepth` и разбираем случай
      -- константности отдельно: если функция стала константой, получаем
      -- противоречие с `hdepth`.
      have hdepth' := hdepth
      simp [Core.Restriction.hasDecisionTreeOfDepth] at hdepth'
      by_cases hconstTrue : ρ.isConstantOn f = true
      · have : False := by simpa [hconstTrue] using hdepth'
        cases this
      · have hconst : ρ.isConstantOn f = false :=
          Bool.eq_false_of_ne_true hconstTrue
        have hany :
            (ρ.freeIndicesList).any
                (fun i =>
                  match ρ.assign i false, ρ.assign i true with
                  | some ρ0, some ρ1 =>
                      Core.Restriction.hasDecisionTreeOfDepth ρ0 f t
                        && Core.Restriction.hasDecisionTreeOfDepth ρ1 f t
                  | _, _ => false)
              = false := by
          simpa [hconst] using hdepth'
        -- Из неконстантности следует, что свободных координат как минимум одна.
        have hfree_pos : 0 < ρ.freeCount := by
          have hconst_zero :=
            Core.Restriction.isConstantOn_of_freeCount_eq_zero
              (ρ := ρ) (f := f)
          have hnotZero : ρ.freeCount ≠ 0 := by
            intro hzero
            have := hconst_zero (ρ := ρ) (f := f) hzero
            exact (by simpa [hconst] using this)
          exact Nat.pos_of_ne_zero hnotZero
        -- Явно выделяем первый свободный индекс, чтобы проанализировать рекурсию.
        obtain ⟨i, rest, hlist⟩ :
          ∃ i rest, ρ.freeIndicesList = i :: rest := by
          have hnonempty : ρ.freeIndicesList ≠ [] := by
            intro hnil
            have hzero : ρ.freeCount = 0 := by
              simpa [Core.Restriction.freeCount, hnil]
              using congrArg List.length hnil
            have hconst_true :=
              Core.Restriction.isConstantOn_of_freeCount_eq_zero
              (ρ := ρ) (f := f) hzero
          exact (by simpa [hconst] using hconst_true)
          cases hfree : ρ.freeIndicesList with
          | nil => exact (hnonempty hfree).elim
          | cons j rest =>
            exact ⟨j, rest, hfree⟩
        -- Переписываем список свободных индексов и фиксируем полезные обозначения.
        have hi_mem : i ∈ ρ.freeIndicesList := by
          simpa [hlist] using List.mem_cons_self (a := i) (l := rest)
        obtain ⟨ρFalse, hassignFalse⟩ :=
          Core.Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := i) (b := false) hi_mem
        obtain ⟨ρTrue, hassignTrue⟩ :=
          Core.Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := i) (b := true) hi_mem
        -- Теперь анализируем условие `any = false` на первом элементе списка.
        have hpred :
            (Core.Restriction.hasDecisionTreeOfDepth ρFalse f t
                && Core.Restriction.hasDecisionTreeOfDepth ρTrue f t)
              = false := by
          simp [List.any_cons, hlist, hassignFalse, hassignTrue,
            Bool.and_eq_false] at hany
          obtain ⟨hhead, _⟩ := hany
          simpa [Bool.and_eq_false] using hhead
        -- По равенству `&& = false` одна из ветвей также проваливает проверку глубины.
        have hbranch :
            Core.Restriction.hasDecisionTreeOfDepth ρFalse f t = false ∨
              Core.Restriction.hasDecisionTreeOfDepth ρTrue f t = false := by
          simpa [Bool.and_eq_false] using hpred
        -- Разбираем случаи и применяем индуктивное предположение к нужной ветви.
        refine hbranch.elim ?_ ?_
        · intro hFalse
          have hrec := ih hFalse
          have hcount :=
            Core.Restriction.freeCount_assign_of_mem
              (ρ := ρ) (i := i) (b := false) (ρ' := ρFalse) hi_mem hassignFalse
          have hle : t ≤ ρ.freeCount - 1 := by
            simpa [hcount] using hrec
          have hsucc := Nat.succ_le_succ hle
          have hpred_eq := Nat.succ_pred_eq_of_pos hfree_pos
          exact (by simpa [hpred_eq] using hsucc)
        · intro hTrue
          have hrec := ih hTrue
          have hcount :=
            Core.Restriction.freeCount_assign_of_mem
              (ρ := ρ) (i := i) (b := true) (ρ' := ρTrue) hi_mem hassignTrue
          have hle : t ≤ ρ.freeCount - 1 := by
            simpa [hcount] using hrec
          have hsucc := Nat.succ_le_succ hle
          have hpred_eq := Nat.succ_pred_eq_of_pos hfree_pos
          exact (by simpa [hpred_eq] using hsucc)

/-- Универсальная оценка: провал проверки глубины `t` оставляет как минимум `t`
свободных переменных в исходном точном ограничении. -/
lemma badRestriction_freeCount_ge
    {F : Core.CNF n w} {ρ : ExactRestriction n ℓ} {t : Nat}
    (hbad : BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ) :
    t ≤ ρ.toRestriction.freeCount :=
  hasDecisionTree_false_freeCount_le
    (ρ := ρ.toRestriction) (f := F.eval) (t := t) hbad

/-- Суммарная масса «плохих» рестрикций в равномерном распределении. -/
@[simp] def badMass (F : Core.CNF n w) (ℓ t : Nat) : ℝ≥0∞ :=
  ∑ ρ : ExactRestriction n ℓ,
    if BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ then
      restrictionUniform n ℓ ρ
    else
      0

/-- На равномерном распределении каждый элемент имеет одинаковый вес. -/
lemma uniform_mass_const (n ℓ : Nat) :
    ∀ ρ : ExactRestriction n ℓ,
      restrictionUniform n ℓ ρ =
        (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) := by
  intro ρ
  simpa using restrictionUniform_apply (n := n) (ℓ := ℓ) ρ

/--
Масса любого конечного семейства точных рестрикций в равномерном распределении
равна произведению веса одной точки на мощность этого семейства.  Этот факт
используется при переходе от подсчёта «плохих» рестрикций к оценкам их
суммарной вероятности.-/
lemma uniform_mass_eq_card (n ℓ : Nat)
    (s : Finset (ExactRestriction n ℓ)) :
    ∑ ρ in s, restrictionUniform n ℓ ρ
      = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * (s.card : ℝ≥0∞) := by
  classical
  have hconst := uniform_mass_const (n := n) (ℓ := ℓ)
  have hmass :
      ∀ ρ : ExactRestriction n ℓ,
        restrictionUniform n ℓ ρ
          = (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) := by
    intro ρ
    simpa using hconst ρ
  calc
    ∑ ρ in s, restrictionUniform n ℓ ρ
        = ∑ _ρ in s,
            ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n)) := by
              refine Finset.sum_congr rfl ?_
              intro ρ _
              exact hmass ρ
    _ = (s.card : ℝ≥0∞)
          * ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n)) := by
            simpa [nsmul_eq_mul]
              using Finset.sum_const
                (s := s)
                (c := (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
    _ = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * (s.card : ℝ≥0∞) := by
            simp [mul_comm, mul_left_comm, mul_assoc]

/--
  Вспомогательное равенство для преобразования конечной суммы натуральных
  чисел в `ℝ≥0∞`.  Оно позволяет без труда переносить комбинаторные формулы,
  полученные на уровне мощностей, в вероятностные оценки.-/
lemma sum_natCast_ennreal {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) :
    ((∑ x in s, f x) : ℝ≥0∞) = ∑ x in s, (f x : ℝ≥0∞) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hrec
    simp [Finset.sum_insert, ha, hrec, Nat.cast_add, add_comm, add_left_comm,
      add_assoc]

/-- Масса «плохого» множества равна произведению веса одной точки на число
рестрикций, попадающих в это множество. -/
lemma badMass_eq_card (F : Core.CNF n w) (ℓ t : Nat) :
    badMass (n := n) (w := w) F ℓ t =
      ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
        * ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞) := by
  classical
  set mass : ℝ≥0∞ :=
      (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) with hmass_def
  have hmass_apply :
      ∀ ρ : ExactRestriction n ℓ, restrictionUniform n ℓ ρ = mass := by
    intro ρ
    simpa [mass, hmass_def] using restrictionUniform_apply (n := n) (ℓ := ℓ) ρ
  have hrewrite :
      badMass (n := n) (w := w) F ℓ t =
        ∑ ρ : ExactRestriction n ℓ,
          if BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ then mass else 0 := by
    unfold badMass
    refine Finset.sum_congr rfl ?_
    intro ρ _
    by_cases hρ : BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ
    · simp [BadRestriction, hρ, mass, hmass_apply ρ]
    · simp [BadRestriction, hρ, mass, hmass_apply ρ]
  have hfilter :
      (∑ ρ : ExactRestriction n ℓ,
          if BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ then mass else 0)
        = ∑ ρ in Finset.univ.filter
            (fun ρ : ExactRestriction n ℓ =>
              BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ), mass := by
    simpa [BadRestriction]
      using
        (Finset.sum_filter
          (s := Finset.univ)
          (p := fun ρ : ExactRestriction n ℓ =>
            BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ)
          (f := fun _ : ExactRestriction n ℓ => mass)).symm
  have hconst :
      ∑ ρ in Finset.univ.filter
          (fun ρ : ExactRestriction n ℓ =>
            BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ), mass
        = ((Finset.univ.filter
              (fun ρ : ExactRestriction n ℓ =>
                BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ)).card
            : ℝ≥0∞) * mass := by
    simpa [nsmul_eq_mul]
      using (Finset.sum_const
        (s := Finset.univ.filter
            (fun ρ : ExactRestriction n ℓ =>
              BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ))
        (a := mass))
  have hcard :
      ((Finset.univ.filter
          (fun ρ : ExactRestriction n ℓ =>
            BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ)).card
          : ℝ≥0∞)
        = ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞) := by
    rfl
  have hmul_comm := mul_comm mass
      ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞)
  calc
    badMass (n := n) (w := w) F ℓ t
        = ∑ ρ : ExactRestriction n ℓ,
            if BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ then mass else 0 :=
              hrewrite
    _ = ∑ ρ in Finset.univ.filter
          (fun ρ : ExactRestriction n ℓ =>
            BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ), mass := hfilter
    _ = ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞) * mass := by
          simpa [BadRestriction, mass, hmass_def, hcard]
            using hconst
    _ = mass * ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞) := by
          simpa [hmul_comm]
    _ = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞) := by
        simpa [mass, hmass_def]

/--
Если множество «плохих» рестрикций вложено в произвольное семейство `S`, то
их суммарная масса не превосходит массы `S`.  Это позволяет переходить от
комбинаторного включения `badSet ⊆ S` к вероятностным оценкам.-/
lemma badMass_le_familyMass (F : Core.CNF n w) (ℓ t : Nat)
    (S : Finset (ExactRestriction n ℓ))
    (hsubset : badSet (n := n) (w := w) F ℓ t ⊆ S) :
    badMass (n := n) (w := w) F ℓ t
      ≤ ∑ ρ in S, restrictionUniform n ℓ ρ := by
  classical
  have hmass_bad := badMass_eq_card (n := n) (w := w) (F := F) ℓ t
  have hmass_S := uniform_mass_eq_card (n := n) (ℓ := ℓ) (s := S)
  have hcard_le := Finset.card_le_of_subset hsubset
  have hcard_le' :
      ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞)
        ≤ (S.card : ℝ≥0∞) := by
    exact_mod_cast hcard_le
  have hconst_nonneg :
      0 ≤ (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) := by
    have : 0 ≤ (1 : ℝ≥0∞) := zero_le_one
    simpa using this
  have hineq :=
    mul_le_mul_of_nonneg_left hcard_le' hconst_nonneg
  refine hmass_bad.trans_le ?_
  have hS_mass :
      ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * (S.card : ℝ≥0∞)
        = ∑ ρ in S, restrictionUniform n ℓ ρ := by
    simpa using hmass_S.symm
  have htarget :
      ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((badSet (n := n) (w := w) F ℓ t).card : ℝ≥0∞)
        ≤ ∑ ρ in S, restrictionUniform n ℓ ρ := by
    simpa [hS_mass] using hineq
  exact htarget

/-- Простая оценка: мощность «плохого» множества не превосходит полного пространства
рестрикций.  Этот грубый барьер пригодится при последующей привязке к размеру формулы. -/
lemma badSet_card_le_total (F : Core.CNF n w) (ℓ t : Nat) :
    (badSet (n := n) (w := w) F ℓ t).card ≤ Fintype.card (ExactRestriction n ℓ) := by
  classical
  exact Finset.card_le_univ _

/-!
### Объединение клаузовых семейств и оценка его массы

Следующий блок связывает семейства `clauseBadFamily` с конкретной формулой.
Мы рассматриваем объединение всех клаузовых вкладов и оцениваем его как по
мощности, так и по массе в равномерном распределении.  Эти оценки понадобятся,
когда мы установим, что каждое «плохое» ограничение обязательно даёт
pending-свидетель.
-/

/-- Объединение «плохих» семейств для списка клауз. -/
@[simp] def clauseBadFamilyList
    (clauses : List (Core.CnfClause n)) (ℓ t : Nat) :
    Finset (ExactRestriction n ℓ) :=
  match clauses with
  | [] => ∅
  | C :: rest =>
      clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C ∪
        clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) rest

/-- Полное «плохое» семейство для формулы как объединение всех клаузовых вкладов. -/
@[simp] def formulaBadFamily (F : Core.CNF n w) (ℓ t : Nat) :
    Finset (ExactRestriction n ℓ) :=
  clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) F.clauses

lemma clauseBadFamilyList_cons {C : Core.CnfClause n}
    (rest : List (Core.CnfClause n)) {ℓ t : Nat} :
    clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) (C :: rest)
      = clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C
          ∪ clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) rest := by
  classical
  simp [clauseBadFamilyList]

lemma mem_formulaBadFamily {F : Core.CNF n w} {ℓ t : Nat}
    {ρ : ExactRestriction n ℓ} :
    ρ ∈ formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t
      ↔ ∃ C ∈ F.clauses,
          ρ ∈ clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C := by
  classical
  induction F.clauses with
  | nil =>
      simp [formulaBadFamily]
  | cons C rest ih =>
      have := ih
      simp [formulaBadFamily, clauseBadFamilyList_cons, this]

/-!
### Общие неравенства для сумм по объединению

Для дальнейших оценок нам понадобится неравенство на сумму по объединению
двух конечных множеств с неотрицательными весами.
-/

lemma sum_union_le {α : Type _} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ≥0∞) :
    ∑ x in s ∪ t, f x ≤ ∑ x in s, f x + ∑ x in t, f x := by
  classical
  have hdisj : Disjoint s (t \ s) := Finset.disjoint_sdiff
  have hrewrite :=
    Finset.sum_union (s := s) (t := t \ s) (f := f) hdisj
  have hsubset : t \ s ⊆ t := Finset.sdiff_subset _ _
  have hnonneg : ∀ x ∈ t, 0 ≤ f x := by
    intro x _
    exact zero_le _
  have hdiff_le :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := f)
      (hs₁ := hsubset) (hs₂ := hnonneg)
  have hgoal :
      ∑ x in s ∪ t, f x
        = ∑ x in s, f x + ∑ x in t \ s, f x := by
    simpa [Finset.union_sdiff_self_eq_union] using hrewrite
  calc
    ∑ x in s ∪ t, f x = ∑ x in s, f x + ∑ x in t \ s, f x := hgoal
    _ ≤ ∑ x in s, f x + ∑ x in t, f x := by
      have := add_le_add_left hdiff_le (a := ∑ x in s, f x)
      simpa using this

/-- Мощность объединения оценивается суммой мощностей составляющих множеств. -/
lemma clauseBadFamilyList_card_le
    (clauses : List (Core.CnfClause n)) (ℓ t : Nat) :
    (clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) clauses).card
      ≤ (clauses.map fun C =>
            (clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card).sum := by
  classical
  induction clauses with
  | nil =>
      simp
  | cons C rest ih =>
      have hcard :=
        Finset.card_union_le (s := clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C)
          (t := clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) rest)
      have :=
        add_le_add_left ih
          (a := (clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card)
      simpa [clauseBadFamilyList_cons] using
        le_trans hcard this

/-- Масса объединения ограничена суммой масс составляющих множеств. -/
lemma clauseBadFamilyList_mass_le
    (clauses : List (Core.CnfClause n)) (ℓ t : Nat) :
    ∑ ρ in clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) clauses,
        restrictionUniform n ℓ ρ
      ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((clauses.map fun C :
                  ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞))).sum := by
  classical
  induction clauses with
  | nil =>
      simp [clauseBadFamilyList]
  | cons C rest ih =>
      have hsplit :
          ∑ ρ in clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) (C :: rest),
              restrictionUniform n ℓ ρ
            ≤ ∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C,
                restrictionUniform n ℓ ρ
              + ∑ ρ in clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) rest,
                  restrictionUniform n ℓ ρ := by
        simpa [clauseBadFamilyList_cons]
          using sum_union_le
            (s := clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C)
            (t := clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) rest)
            (f := fun ρ => restrictionUniform n ℓ ρ)
      have hconst :
          ∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C,
              restrictionUniform n ℓ ρ
            = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
                * ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞) :=
        clauseBadFamily_uniformMass (n := n) (ℓ := ℓ) (t := t) (C := C)
      have hrest := ih
      have hcombined :=
        calc
          ∑ ρ in clauseBadFamilyList (n := n) (ℓ := ℓ) (t := t) (C :: rest),
              restrictionUniform n ℓ ρ
              ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
                    * ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞)
                  + ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
                      * ((rest.map fun C :
                          ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞))).sum := by
                have hC_le :
                    ∑ ρ in clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C,
                        restrictionUniform n ℓ ρ
                      ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
                          * ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞) :=
                  le_of_eq hconst
                have hrest_le := hrest
                exact le_trans hsplit (add_le_add hC_le hrest_le)
          _ = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
                * (((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞)
                    + ((rest.map fun C :
                        ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞))).sum) := by
                simp [mul_add, add_comm, add_left_comm, add_assoc]
          _ = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
                * (((C :: rest).map fun C :
                    ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞))).sum := by
                simp [List.map_cons, add_comm, add_left_comm, add_assoc]
      simpa using hcombined

/-- Масса формульного объединения выражается через вклад каждой клаузы. -/
lemma formulaBadFamily_mass_le_clauseSum (F : Core.CNF n w) (ℓ t : Nat) :
    ∑ ρ in formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t,
        restrictionUniform n ℓ ρ
      ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((F.clauses.map fun C :
                  ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞))).sum := by
  classical
  simpa [formulaBadFamily]
    using clauseBadFamilyList_mass_le
      (n := n) (clauses := F.clauses) (ℓ := ℓ) (t := t)

/-- Мощность объединения оценивается суммой мощностей по клауза́м. -/
lemma formulaBadFamily_card_le_clauseSum (F : Core.CNF n w) (ℓ t : Nat) :
    (formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t).card
      ≤ (F.clauses.map fun C =>
            (clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card).sum := by
  classical
  simpa [formulaBadFamily]
    using clauseBadFamilyList_card_le
      (n := n) (clauses := F.clauses) (ℓ := ℓ) (t := t)

/-- Pending-свидетель помещает рестрикцию в формульное «плохое» семейство. -/
lemma pendingWitness_mem_formulaBadFamily
    {F : Core.CNF n w} {ℓ t : Nat} {ρ : ExactRestriction n ℓ}
    {C : Core.CnfClause n}
    (hC : C ∈ F.clauses)
    {witness : Core.Restriction.ClausePendingWitness ρ.toRestriction C}
    (hstatus : ρ.toRestriction.clauseStatus C
        = Core.Restriction.ClauseStatus.pending witness)
    (ht : t ≤ (ρ.toRestriction.freeLiterals C).length) :
    ρ ∈ formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t := by
  classical
  refine (mem_formulaBadFamily (n := n) (ℓ := ℓ) (w := w) (F := F) (ρ := ρ)).2 ?_
  refine ⟨C, hC, ?_⟩
  exact pendingWitness_mem_clauseBadFamily
    (n := n) (ℓ := ℓ) (ρ := ρ) (C := C) (w := witness)
    (t := t) hstatus ht

/-- Вытаскиваем явную комбинаторную формулу из оценки массы. -/
lemma formulaBadFamily_mass_le_explicit (F : Core.CNF n w) (ℓ t : Nat) :
    ∑ ρ in formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t,
        restrictionUniform n ℓ ρ
      ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((F.clauses.map fun C =>
                (∑ k in Finset.Icc t
                        (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
                    (Nat.choose (clauseIndexFinset (n := n) C).card k
                        * Nat.choose
                            (n - (clauseIndexFinset (n := n) C).card)
                            (ℓ - k)
                        * Nat.pow 2
                            (n - (clauseIndexFinset (n := n) C).card + k)
                      : ℝ≥0∞))).sum := by
  classical
  have hmass := formulaBadFamily_mass_le_clauseSum
    (n := n) (ℓ := ℓ) (w := w) (F := F) (t := t)
  have hmap :
      F.clauses.map (fun C =>
          ((clauseBadFamily (n := n) (ℓ := ℓ) (t := t) C).card : ℝ≥0∞))
        = F.clauses.map (fun C =>
            (∑ k in Finset.Icc t
                    (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
                (Nat.choose (clauseIndexFinset (n := n) C).card k
                    * Nat.choose
                        (n - (clauseIndexFinset (n := n) C).card)
                        (ℓ - k)
                    * Nat.pow 2
                        (n - (clauseIndexFinset (n := n) C).card + k)
                  : ℝ≥0∞)) := by
    refine List.map_congr ?_ ?_
    · rfl
    · intro C hC
      have hcard := clauseBadFamily_card_eq_cardDecomposed
        (n := n) (ℓ := ℓ) (C := C) (t := t)
      have hcoe := congrArg (fun k : ℕ => (k : ℝ≥0∞)) hcard
      have hsum := sum_natCast_ennreal
        (s := Finset.Icc t (Nat.min ℓ (clauseIndexFinset (n := n) C).card))
        (f := fun k =>
          Nat.choose (clauseIndexFinset (n := n) C).card k
            * Nat.choose (n - (clauseIndexFinset (n := n) C).card) (ℓ - k)
            * Nat.pow 2 (n - (clauseIndexFinset (n := n) C).card + k))
      have hrewrite := hcoe.trans hsum
      simpa [clauseIndexFinset_card (n := n) (C := C)] using hrewrite
  simpa [hmap] using hmass

/--
  Комбинируем включение `badSet ⊆ formulaBadFamily` с явной формулой для
  массы последнего.  Результирующее неравенство — промежуточная цель на пути к
  оценке `(#clauses) · (p · t)^t` для «плохих» рестрикций.-/
lemma badMass_le_formulaExplicit (F : Core.CNF n w) (ℓ t : Nat)
    (hsubset :
      badSet (n := n) (w := w) F ℓ t
        ⊆ formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t) :
    badMass (n := n) (w := w) F ℓ t
      ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * ((F.clauses.map fun C =>
                (∑ k in Finset.Icc t
                        (Nat.min ℓ (clauseIndexFinset (n := n) C).card),
                    (Nat.choose (clauseIndexFinset (n := n) C).card k
                        * Nat.choose
                            (n - (clauseIndexFinset (n := n) C).card)
                            (ℓ - k)
                        * Nat.pow 2
                            (n - (clauseIndexFinset (n := n) C).card + k)
                      : ℝ≥0∞))).sum := by
  classical
  have hmass := badMass_le_familyMass
    (n := n) (ℓ := ℓ) (w := w) (F := F) (t := t)
    (S := formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t) hsubset
  have hexplicit := formulaBadFamily_mass_le_explicit
    (n := n) (ℓ := ℓ) (w := w) (F := F) (t := t)
  exact hmass.trans hexplicit

end Depth1Switching
end ThirdPartyFacts
end Pnp3
