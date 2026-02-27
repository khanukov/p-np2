import AC0.MultiSwitching.CanonicalDT
import AC0.MultiSwitching.Decides
import AC0.MultiSwitching.Definitions

/-!
  pnp3/AC0/MultiSwitching/CommonCCDT.lean

  Общий CCDT: дерево, которое продолжает ветвиться, пока существует
  формула из семейства с pending‑клаузаой. Это "true common tree",
  пригодный для Stage‑4 (leaf‑decisions).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n w t : Nat}

/-!
  Вспомогательная лемма для `find?`: найденный элемент удовлетворяет предикату
  и принадлежит списку.
-/
lemma find?_some_mem {α : Type _} (p : α → Bool) (xs : List α) (a : α) :
    xs.find? p = some a → p a = true ∧ a ∈ xs := by
  induction xs with
  | nil =>
      intro h
      simp [List.find?] at h
  | cons x xs ih =>
      intro h
      simp [List.find?] at h
      by_cases hpx : p x = true
      · simp [hpx] at h
        rcases h with rfl
        exact ⟨hpx, by simp⟩
      · simp [hpx] at h
        rcases ih h with ⟨hp, hmem⟩
        exact ⟨hp, by simp [hmem]⟩

lemma find?_none_forall {α : Type _} (p : α → Bool) (xs : List α) :
    xs.find? p = none → ∀ a ∈ xs, p a = false := by
  induction xs with
  | nil =>
      intro _ a hmem
      cases hmem
  | cons x xs ih =>
      intro hnone a hmem
      by_cases hpx : p x = true
      · -- `find?` не мог быть `none`.
        have : False := by
          simp [List.find?, hpx] at hnone
        exact this.elim
      · -- `find?` продолжает поиск в хвосте.
        have hrest : xs.find? p = none := by
          simpa [List.find?, hpx] using hnone
        have hmem' : a = x ∨ a ∈ xs := by
          exact List.mem_cons.mp hmem
        cases hmem' with
        | inl hax =>
            subst hax
            exact by
              -- `p x` не истинно, значит `p x = false`.
              simpa using hpx
        | inr hmemxs =>
            exact ih hrest a hmemxs

/-- Первый индекс формулы, для которой существует pending‑клауза. -/
noncomputable def firstPendingIndex?
    (F : FormulaFamily n w) (ρ : Restriction n) : Option (Fin F.length) := by
  classical
  -- Ищем первый индекс с `firstPendingClause? = some _`.
  let idxs := List.finRange F.length
  let pred : Fin F.length → Bool :=
    fun i => (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses).isSome
  exact idxs.find? pred

/-- Первая pending‑клауза вместе с индексом формулы (если существует). -/
noncomputable def firstPendingFormula?
    (F : FormulaFamily n w) (ρ : Restriction n) :
    Option (Sigma fun i : Fin F.length =>
      Restriction.PendingClauseSelection (ρ := ρ) (F.get i).clauses) :=
  match firstPendingIndex? (F := F) (ρ := ρ) with
  | none => none
  | some i =>
      -- Берём selection из соответствующей формулы (если он есть).
      Option.map (fun sel => Sigma.mk i sel)
        (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses)

lemma firstPendingFormula?_none_iff_index_none
    {F : FormulaFamily n w} {ρ : Restriction n} :
    firstPendingFormula? (F := F) (ρ := ρ) = none ↔
      firstPendingIndex? (F := F) (ρ := ρ) = none := by
  classical
  constructor
  · intro h
    cases hidx : firstPendingIndex? (F := F) (ρ := ρ) with
    | none => rfl
    | some i =>
        -- В этом случае `firstPendingFormula?` не может быть `none`.
        have hfind :=
          find?_some_mem
            (p := fun j : Fin F.length =>
              (Restriction.firstPendingClause? (ρ := ρ) (F.get j).clauses).isSome)
            (xs := List.finRange F.length) (a := i)
            (by simpa [firstPendingIndex?] using hidx)
        have hpred :
            (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses).isSome = true :=
          hfind.1
        obtain ⟨sel, hsel⟩ := (Option.isSome_iff_exists).1 (by simpa using hpred)
        have hne :
            Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses ≠ none := by
          intro hnone
          simp [hsel] at hnone
        let f :
            Restriction.PendingClauseSelection (ρ := ρ) (F.get i).clauses →
              Sigma fun j : Fin F.length =>
                Restriction.PendingClauseSelection (ρ := ρ) (F.get j).clauses :=
          fun sel => ⟨i, sel⟩
        have hmap :
            Option.map f
                (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses) = none := by
          unfold firstPendingFormula? at h
          simpa [hidx, f] using h
        have hnone' :
            Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses = none :=
          (Option.map_eq_none_iff (f := f)).1 hmap
        exact (hne hnone').elim
  · intro h
    cases hidx : firstPendingIndex? (F := F) (ρ := ρ) with
    | none =>
        simp [firstPendingFormula?, hidx]
    | some i =>
        -- противоречие с `h`
        have : False := by
          simp [hidx] at h
        exact this.elim

/-- Общий CCDT: ветвимся, пока есть pending‑формула. -/
noncomputable def commonCCDT_CNF_aux
    (F : FormulaFamily n w) :
    Nat → Restriction n → PDT n
  | 0, ρ => PDT.leaf ρ.mask
  | Nat.succ fuel, ρ =>
      match firstPendingFormula? (F := F) (ρ := ρ) with
      | none => PDT.leaf ρ.mask
      | some ⟨_, selection⟩ =>
          let ℓ := chooseFreeLiteral (w := selection.witness)
          have hmem : ℓ ∈ selection.witness.free :=
            chooseFreeLiteral_mem (w := selection.witness)
          have hfree :
              ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          PDT.node ℓ.idx
            (commonCCDT_CNF_aux F fuel ρ0)
            (commonCCDT_CNF_aux F fuel ρ1)

/-- CCDT‑алгоритм: общий tree для семейства. -/
noncomputable def commonCCDTAlgorithmCNF
    (F : FormulaFamily n w) (t : Nat) :
    CCDTAlgorithm n w 0 t F := by
  classical
  exact
    { ccdt := fun ρ => commonCCDT_CNF_aux (F := F) t ρ }

/-!
  Если pending‑формула не найдена, то каждая формула решена (константа)
  под ограничением `ρ`.
-/

lemma decidesCNFOn_of_firstPendingIndex?_none
    {ρ : Restriction n} {F : FormulaFamily n w}
    (hnone : firstPendingIndex? (F := F) (ρ := ρ) = none) :
    ∀ i : Fin F.length, DecidesCNFOn (ρ := ρ) (F := F.get i) := by
  classical
  -- Для всех индексов предикат pending ложен.
  have hall :
      ∀ i ∈ List.finRange F.length,
        (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses).isSome = false := by
    intro i hi
    have hnone' := find?_none_forall
      (p := fun j : Fin F.length =>
        (Restriction.firstPendingClause? (ρ := ρ) (F.get j).clauses).isSome)
      (xs := List.finRange F.length) (by simpa [firstPendingIndex?] using hnone)
    exact hnone' i hi
  intro i
  -- Перевод `isSome = false` в `= none`.
  have his : (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses).isSome = false := by
    exact hall i (List.mem_finRange _)
  have hnone' :
      Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses = none := by
    by_contra hne
    obtain ⟨sel, hsel⟩ := (Option.ne_none_iff_exists).1 hne
    have hsel' :
        Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses = some sel := by
      simpa using hsel.symm
    have hsome :
        (Restriction.firstPendingClause? (ρ := ρ) (F.get i).clauses).isSome = true := by
      rw [hsel']
      rfl
    have hfalse : False := by
      have his' := his
      rw [hsome] at his'
      cases his'
    exact hfalse.elim
  exact decidesCNFOn_of_firstPendingClause?_none (ρ := ρ) (F := F.get i) hnone'

lemma decidesFamilyOn_of_firstPendingFormula?_none
    {ρ : Restriction n} {F : FormulaFamily n w}
    (hnone : firstPendingFormula? (F := F) (ρ := ρ) = none) :
    DecidesFamilyOn (ρ := ρ) (F := F) := by
  have hidx : firstPendingIndex? (F := F) (ρ := ρ) = none := by
    exact (firstPendingFormula?_none_iff_index_none (F := F) (ρ := ρ)).1 hnone
  exact decidesCNFOn_of_firstPendingIndex?_none (ρ := ρ) (F := F) hidx

/-!
  Leaf‑decisions: если глубина дерева строго меньше `t`, то любой лист
  соответствует ограничению, при котором все формулы решены.
-/

theorem leaf_decidesFamily_of_depth_lt
    {F : FormulaFamily n w} :
    ∀ (t : Nat) (ρ : Restriction n) (β : Subcube n),
      β ∈ PDT.leaves (commonCCDT_CNF_aux (F := F) t ρ) →
      PDT.depth (commonCCDT_CNF_aux (F := F) t ρ) < t →
      DecidesFamilyOn (ρ := ⟨β⟩) (F := F)
  | 0, ρ, β, hβ, hdepth => by
      -- Невозможный случай: depth < 0.
      exact (Nat.not_lt_zero _ hdepth).elim
  | Nat.succ fuel, ρ, β, hβ, hdepth => by
      classical
      -- Разбираем по наличию pending‑формулы.
      cases hsel : firstPendingFormula? (F := F) (ρ := ρ) with
      | none =>
          -- Лист сразу: β = ρ.mask, и все формулы решены.
          have hβ' : β = ρ.mask := by
            -- leaves (leaf ρ.mask) = [ρ.mask]
            simpa [commonCCDT_CNF_aux, hsel, PDT.leaves] using hβ
          subst hβ'
          have hdec := decidesFamilyOn_of_firstPendingFormula?_none
            (F := F) (ρ := ρ) hsel
          simpa using hdec
      | some sel =>
          -- Узел: переходим в соответствующую ветвь.
          -- Обозначаем подограничения так же, как в определении.
          cases sel with
          | mk i selection =>
              let ℓ := chooseFreeLiteral (w := selection.witness)
              have hmem : ℓ ∈ selection.witness.free :=
                chooseFreeLiteral_mem (w := selection.witness)
              have hfree :
                  ℓ.idx ∈ ρ.freeIndicesList :=
                Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
              let ρ0 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
              let ρ1 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
              have hdepth' :
                  Nat.max
                      (PDT.depth (commonCCDT_CNF_aux (F := F) fuel ρ0))
                      (PDT.depth (commonCCDT_CNF_aux (F := F) fuel ρ1))
                    < fuel := by
                have hdepth_node :
                    Nat.succ
                        (Nat.max
                          (PDT.depth (commonCCDT_CNF_aux (F := F) fuel ρ0))
                          (PDT.depth (commonCCDT_CNF_aux (F := F) fuel ρ1)))
                      < Nat.succ fuel := by
                  simpa [commonCCDT_CNF_aux, hsel, PDT.depth, ℓ, ρ0, ρ1] using hdepth
                exact (Nat.succ_lt_succ_iff).1 hdepth_node
              have hdepth_left :
                  PDT.depth (commonCCDT_CNF_aux (F := F) fuel ρ0) < fuel := by
                exact lt_of_le_of_lt (Nat.le_max_left _ _) hdepth'
              have hdepth_right :
                  PDT.depth (commonCCDT_CNF_aux (F := F) fuel ρ1) < fuel := by
                exact lt_of_le_of_lt (Nat.le_max_right _ _) hdepth'
              -- Разбираем, в какой ветви лежит β.
              have hβ' :
                  β ∈ PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ0) ∨
                  β ∈ PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ1) := by
                have : β ∈
                    PDT.leaves
                      (PDT.node ℓ.idx
                        (commonCCDT_CNF_aux (F := F) fuel ρ0)
                        (commonCCDT_CNF_aux (F := F) fuel ρ1)) := by
                  simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1] using hβ
                -- leaves(node) = leaves left ++ leaves right
                have hmem :
                    β ∈
                      (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ0)) ++
                        (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ1)) := by
                  simpa [PDT.leaves] using this
                exact List.mem_append.mp hmem
              cases hβ' with
              | inl hβ0 =>
                  exact leaf_decidesFamily_of_depth_lt
                    (F := F) fuel ρ0 β hβ0 hdepth_left
              | inr hβ1 =>
                  exact leaf_decidesFamily_of_depth_lt
                    (F := F) fuel ρ1 β hβ1 hdepth_right

/-!
  Листья common‑CCDT уточняют исходную рестрикцию.
-/

lemma subcubeRefines_of_assign_some
    {ρ ρ' : Restriction n} {i : Fin n} {b : Bool}
    (hassign : ρ.assign i b = some ρ')
    (hfree : ρ.mask i = none) :
    subcubeRefines ρ'.mask ρ.mask := by
  intro j
  cases hmask : ρ.mask j with
  | none =>
      simp
  | some b0 =>
      have hne : j ≠ i := by
        intro hji
        subst hji
        -- Противоречие с `hfree`.
        simp [hfree] at hmask
      have hmask' :=
        Restriction.assign_mask_eq (ρ := ρ) (ρ' := ρ') (i := i) (b := b) hassign j
      -- На координатах ≠ i маска сохраняется.
      simp [hmask, hne] at hmask'
      simpa [hmask] using hmask'

lemma commonCCDT_leaves_refine_root
    {F : FormulaFamily n w} :
    ∀ t (ρ : Restriction n) (β : Subcube n),
      β ∈ PDT.leaves (commonCCDT_CNF_aux (F := F) t ρ) →
      subcubeRefines β ρ.mask
  | 0, ρ, β, hβ => by
      rcases List.mem_singleton.mp (by
        simpa [commonCCDT_CNF_aux, PDT.leaves] using hβ) with rfl
      exact subcubeRefines_refl (β := ρ.mask)
  | Nat.succ fuel, ρ, β, hβ => by
      classical
      cases hsel : firstPendingFormula? (F := F) (ρ := ρ) with
      | none =>
          -- Лист равен `ρ.mask`.
          rcases List.mem_singleton.mp (by
            simpa [commonCCDT_CNF_aux, hsel, PDT.leaves] using hβ) with rfl
          exact subcubeRefines_refl (β := ρ.mask)
      | some sel =>
          cases sel with
          | mk i selection =>
              let ℓ := chooseFreeLiteral (w := selection.witness)
              have hmem : ℓ ∈ selection.witness.free :=
                chooseFreeLiteral_mem (w := selection.witness)
              have hfree :
                  ℓ.idx ∈ ρ.freeIndicesList :=
                Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
              let ρ0 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
              let ρ1 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
              have hassign0 : ρ.assign ℓ.idx false = some ρ0 := by
                simpa [ρ0] using
                  (Classical.choose_spec
                    (Restriction.assign_some_of_mem_freeIndicesList
                      (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
              have hassign1 : ρ.assign ℓ.idx true = some ρ1 := by
                simpa [ρ1] using
                  (Classical.choose_spec
                    (Restriction.assign_some_of_mem_freeIndicesList
                      (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
              have hfree_mask : ρ.mask ℓ.idx = none := by
                exact (Restriction.mem_freeIndicesList (ρ := ρ) (i := ℓ.idx)).1 hfree
              have href0 :
                  subcubeRefines ρ0.mask ρ.mask :=
                subcubeRefines_of_assign_some (hassign := hassign0) (hfree := hfree_mask)
              have href1 :
                  subcubeRefines ρ1.mask ρ.mask :=
                subcubeRefines_of_assign_some (hassign := hassign1) (hfree := hfree_mask)
              -- β принадлежит одной из ветвей.
              have hmem :
                  β ∈
                    (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ0)) ++
                      (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ1)) := by
                have : β ∈
                    PDT.leaves
                      (PDT.node ℓ.idx
                        (commonCCDT_CNF_aux (F := F) fuel ρ0)
                        (commonCCDT_CNF_aux (F := F) fuel ρ1)) := by
                  simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1] using hβ
                simpa [PDT.leaves] using this
              cases (List.mem_append.mp hmem) with
              | inl hβ0 =>
                  have hβ0' :=
                    commonCCDT_leaves_refine_root (t := fuel) (ρ := ρ0) (β := β) hβ0
                  exact subcubeRefines_trans hβ0' href0
              | inr hβ1 =>
                  have hβ1' :=
                    commonCCDT_leaves_refine_root (t := fuel) (ρ := ρ1) (β := β) hβ1
                  exact subcubeRefines_trans hβ1' href1

/-!
  Совместимость: если точка совместима с корневой рестрикцией, то она
  лежит в некотором листе common‑CCDT.
-/

lemma mem_of_assign_some_of_mem
    {ρ ρ' : Restriction n} {i : Fin n} {b : Bool} {x : Core.BitVec n}
    (hassign : ρ.assign i b = some ρ')
    (hmem : mem ρ.mask x)
    (hxi : x i = b) :
    mem ρ'.mask x := by
  -- Показываем мембершип через определение `mem`.
  apply (mem_iff (β := ρ'.mask) (x := x)).2
  intro j b' hmask'
  have hmask := Restriction.assign_mask_eq
    (ρ := ρ) (ρ' := ρ') (i := i) (b := b) hassign j
  by_cases hji : j = i
  · cases hji
    -- На присвоенной координате значение фиксировано как `b`.
    have hmask_eq : ρ'.mask i = some b := by
      simpa using hmask
    -- Тогда `b' = b`, и используем `hxi`.
    have hb' : b' = b := by
      have hmask_eq' : ρ'.mask i = some b' := by
        simpa using hmask'
      have : some b' = some b := by
        simpa [hmask_eq'] using hmask_eq
      exact Option.some.inj this
    simp [hb', hxi]
  · -- На остальных координатах маска совпадает с исходной.
    have hmask'': ρ.mask j = some b' := by
      -- из `hmask` и `hji` следует `ρ'.mask j = ρ.mask j`
      have : ρ'.mask j = ρ.mask j := by
        simpa [hji] using hmask
      simpa [this] using hmask'
    have hmem' := (mem_iff (β := ρ.mask) (x := x)).1 hmem j b' hmask''
    exact hmem'

lemma commonCCDT_leaf_of_compatible
    {F : FormulaFamily n w} :
    ∀ t (ρ : Restriction n) (x : Core.BitVec n),
      ρ.compatible x = true →
      ∃ β ∈ PDT.leaves (commonCCDT_CNF_aux (F := F) t ρ), mem β x
  | 0, ρ, x, hcomp => by
      have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
      refine ⟨ρ.mask, ?_, hmem⟩
      simp [commonCCDT_CNF_aux, PDT.leaves]
  | Nat.succ fuel, ρ, x, hcomp => by
      classical
      cases hsel : firstPendingFormula? (F := F) (ρ := ρ) with
      | none =>
          have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
          refine ⟨ρ.mask, ?_, hmem⟩
          simp [commonCCDT_CNF_aux, hsel, PDT.leaves]
      | some sel =>
          cases sel with
          | mk i selection =>
              let ℓ := chooseFreeLiteral (w := selection.witness)
              have hmem : ℓ ∈ selection.witness.free :=
                chooseFreeLiteral_mem (w := selection.witness)
              have hfree :
                  ℓ.idx ∈ ρ.freeIndicesList :=
                Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
              let ρ0 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
              let ρ1 := Classical.choose
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
              have hassign0 : ρ.assign ℓ.idx false = some ρ0 := by
                simpa [ρ0] using
                  (Classical.choose_spec
                    (Restriction.assign_some_of_mem_freeIndicesList
                      (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
              have hassign1 : ρ.assign ℓ.idx true = some ρ1 := by
                simpa [ρ1] using
                  (Classical.choose_spec
                    (Restriction.assign_some_of_mem_freeIndicesList
                      (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
              -- Используем значение бита `x` на индексе ℓ.idx.
              by_cases hbit : x ℓ.idx = false
              · have hmem0 : mem ρ0.mask x := by
                  exact mem_of_assign_some_of_mem
                    (hassign := hassign0)
                    (hmem := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp)
                    (hxi := hbit)
                have hcomp0 : ρ0.compatible x = true :=
                  (Restriction.compatible_iff (ρ := ρ0) (x := x)).2 hmem0
                obtain ⟨β, hβ, hmemβ⟩ :=
                  commonCCDT_leaf_of_compatible (F := F) fuel ρ0 x hcomp0
                refine ⟨β, ?_, hmemβ⟩
                -- переносим membership через leaves node
                have hmem' :
                    β ∈
                      (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ0)) ++
                        (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ1)) := by
                  exact List.mem_append.mpr (Or.inl hβ)
                simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1, PDT.leaves] using hmem'
              · have hbit' : x ℓ.idx = true := by
                  cases hx : x ℓ.idx with
                  | false =>
                      exfalso
                      exact hbit (by simp [hx])
                  | true =>
                      simp
                have hmem1 : mem ρ1.mask x := by
                  exact mem_of_assign_some_of_mem
                    (hassign := hassign1)
                    (hmem := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp)
                    (hxi := hbit')
                have hcomp1 : ρ1.compatible x = true :=
                  (Restriction.compatible_iff (ρ := ρ1) (x := x)).2 hmem1
                obtain ⟨β, hβ, hmemβ⟩ :=
                  commonCCDT_leaf_of_compatible (F := F) fuel ρ1 x hcomp1
                refine ⟨β, ?_, hmemβ⟩
                have hmem' :
                    β ∈
                      (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ0)) ++
                        (PDT.leaves (commonCCDT_CNF_aux (F := F) fuel ρ1)) := by
                  exact List.mem_append.mpr (Or.inr hβ)
                simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1, PDT.leaves] using hmem'

/-!
## Good/Bad for common CCDT

Минимальная фиксация: "bad" означает `depth ≥ t` для common‑дерева.
Это не вмешивается в существующий trace‑based `GoodFamilyCNF`,
но даёт рабочий вход для Stage‑4.
-/

def BadEvent_common (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  t ≤ PDT.depth (commonCCDT_CNF_aux (F := F) t ρ)

def GoodFamilyCNF_common (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ¬ BadEvent_common (F := F) t ρ

theorem depth_lt_of_good_commonCCDT
    {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (_ht : 0 < t)
    (hgood : GoodFamilyCNF_common (F := F) t ρ) :
    PDT.depth (commonCCDT_CNF_aux (F := F) t ρ) < t := by
  -- По определению good — это ¬(t ≤ depth).
  have hnot_ge : ¬ t ≤ PDT.depth (commonCCDT_CNF_aux (F := F) t ρ) := by
    exact hgood
  exact lt_of_not_ge hnot_ge

end MultiSwitching
end AC0
end Pnp3
