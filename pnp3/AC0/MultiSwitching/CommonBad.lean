import Core.BooleanBasics
import AC0.MultiSwitching.CommonCCDT
import AC0.MultiSwitching.TraceBridge

/-!
  pnp3/AC0/MultiSwitching/CommonBad.lean

  Common‑CCDT "bad" predicate and deterministic traces.

  В отличие от canonical‑трассы, common‑trace разрешает менять индекс
  формулы на каждом шаге. Это отражает реальное поведение `commonCCDT_CNF_aux`.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core
open Restriction

variable {n w : Nat}

/--
`CommonTrace F ρ t` — детерминированная трасса длины `t` для common‑CCDT.
Каждый шаг хранит:
* индекс формулы `i`,
* pending‑клаузу этой формулы,
* выбор литерала (ветвление),
и продолжение трассы для обновлённой рестрикции.
-/
inductive CommonTrace (F : FormulaFamily n w) : Restriction n → Nat → Type
  | nil {ρ : Restriction n} : CommonTrace F ρ 0
  | cons {ρ : Restriction n}
      (i : Fin F.length)
      (selection : PendingClauseSelection (ρ := ρ) (F.get i).clauses)
      (choice : ClausePendingWitness.Selection selection.witness)
      {t : Nat}
      (rest : CommonTrace F
        (ClausePendingWitness.Selection.nextRestriction
          (ρ := ρ)
          (C := selection.clause)
          (w := selection.witness)
          (choice := choice)) t) :
      CommonTrace F ρ (Nat.succ t)

namespace CommonTrace

/-- Итоговая рестрикция после применения common‑трассы. -/
@[simp] noncomputable def finalRestriction
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) : Restriction n :=
  match trace with
  | CommonTrace.nil => ρ
  | CommonTrace.cons _ _ _ rest => finalRestriction rest

/-- Список фиксированных пар `(индекс, значение)` вдоль трассы. -/
@[simp] noncomputable def assignedBitFixes
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) : List (BitFix n) :=
  match trace with
  | CommonTrace.nil => []
  | CommonTrace.cons _ _ choice rest =>
      (choice.literal.idx, choice.value) :: assignedBitFixes rest

@[simp] noncomputable def literalPositions
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) : List Nat :=
  match trace with
  | CommonTrace.nil => []
  | CommonTrace.cons _ _ choice rest =>
      choice.index.1 :: literalPositions rest

@[simp] noncomputable def formulaIndices
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) : List Nat :=
  match trace with
  | CommonTrace.nil => []
  | CommonTrace.cons i _ _ rest =>
      i.1 :: formulaIndices rest

lemma assignedBitFixes_length
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    (assignedBitFixes trace).length = t := by
  induction trace with
  | nil =>
      simp [assignedBitFixes]
  | @cons ρ i selection choice t rest ih =>
      simp [assignedBitFixes, ih]

lemma literalPositions_length
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    (literalPositions trace).length = t := by
  induction trace with
  | nil =>
      simp [literalPositions]
  | @cons ρ i selection choice t rest ih =>
      simp [literalPositions, ih]

lemma formulaIndices_length
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    (formulaIndices trace).length = t := by
  induction trace with
  | nil =>
      simp [formulaIndices]
  | @cons ρ i selection choice t rest ih =>
      simp [formulaIndices, ih]

lemma reconstruct_eq_original
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    Core.SelectionTrace.reconstructRestriction
        (ρ := finalRestriction trace) (assignedBitFixes trace) = ρ := by
  induction trace with
  | nil =>
      simp [assignedBitFixes, finalRestriction, Core.SelectionTrace.reconstructRestriction]
  | @cons ρ i selection choice t rest ih =>
      have hstep :
          Core.SelectionTrace.reconstructRestriction
              (ρ := finalRestriction (CommonTrace.cons i selection choice rest))
              (assignedBitFixes (CommonTrace.cons i selection choice rest))
            =
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ)
                (C := selection.clause)
                (w := selection.witness)
                (choice := choice)).unassign choice.literal.idx := by
        simp [assignedBitFixes, finalRestriction,
          Core.SelectionTrace.reconstructRestriction, ih]
      have hundo :=
        ClausePendingWitness.Selection.unassign_nextRestriction
          (ρ := ρ)
          (C := selection.clause)
          (w := selection.witness)
          (choice := choice)
      exact Eq.trans hstep hundo

lemma finalRestriction_mem_R_s
    {F : FormulaFamily n w} {ρ : Restriction n} {t s : Nat}
    (trace : CommonTrace F ρ t)
    (hρ : ρ ∈ R_s (n := n) s) :
    finalRestriction trace ∈ R_s (n := n) (s - t) := by
  induction trace generalizing s with
  | nil =>
      simpa [R_s, finalRestriction] using hρ
  | @cons ρ i selection choice t rest ih =>
      have hcount : (ClausePendingWitness.Selection.nextRestriction
          (ρ := ρ) (C := selection.clause) (w := selection.witness)
          (choice := choice)).freeCount = ρ.freeCount - 1 := by
        simpa using
          (ClausePendingWitness.Selection.freeCount_nextRestriction
            (ρ := ρ) (C := selection.clause) (w := selection.witness) (choice := choice))
      have hρcount : ρ.freeCount = s := (mem_R_s (n := n) (s := s)).1 hρ
      have hρcount' : ρ.freeIndicesList.length = s := by
        simpa [Restriction.freeCount] using hρcount
      have hnext :
          ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := selection.witness)
              (choice := choice)
            ∈ R_s (n := n) (s - 1) := by
        apply (mem_R_s (n := n) (s := s - 1)).2
        simpa [Restriction.freeCount, hρcount'] using hcount
      have hfinal := ih (s := s - 1) hnext
      -- `(s - 1) - t = s - (t + 1)`
      simpa [finalRestriction, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfinal

end CommonTrace

/-!
Deterministic predicate for common‑trace.

Мы требуем, чтобы шаг точно совпадал с выбором `firstPendingFormula?`
и `chooseFreeLiteral` для текущей рестрикции.
-/
def commonTraceDeterministic
    {F : FormulaFamily n w} :
    {ρ : Restriction n} → {t : Nat} →
      CommonTrace F ρ t → Prop
  | _, _, CommonTrace.nil => True
  | ρ, _, CommonTrace.cons i selection choice rest =>
      firstPendingFormula? (F := F) (ρ := ρ) = some ⟨i, selection⟩
        ∧ choice.literal = chooseFreeLiteral (w := selection.witness)
        ∧ commonTraceDeterministic (F := F) rest

lemma commonTraceDeterministic_cast
    {F : FormulaFamily n w} {ρ ρ' : Restriction n} {t : Nat}
    (h : ρ = ρ') (trace : CommonTrace F ρ t) :
    commonTraceDeterministic (F := F) (ρ := ρ') (t := t)
        (cast (by cases h; rfl) trace) ↔
      commonTraceDeterministic (F := F) (ρ := ρ) (t := t) trace := by
  cases h
  rfl

/-- Детеминированное `Bad` для common‑CCDT. -/
def BadFamily_deterministic_common
    (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ trace : CommonTrace F ρ t,
    commonTraceDeterministic (F := F) trace

noncomputable instance instDecidableBadEventCommon (F : FormulaFamily n w) (t : Nat) :
    DecidablePred (BadEvent_common (F := F) t) := by
  intro ρ
  dsimp [BadEvent_common]
  infer_instance

/-!
## Common trace ↔ depth
-/

theorem commonTrace_of_depth_ge
    (F : FormulaFamily n w) :
    ∀ {t : Nat} {ρ : Restriction n},
      t ≤ PDT.depth (commonCCDT_CNF_aux (F := F) t ρ) →
      BadFamily_deterministic_common (F := F) t ρ
  | 0, ρ, _ => by
      exact ⟨CommonTrace.nil, by simp [commonTraceDeterministic]⟩
  | Nat.succ t, ρ, hdepth => by
      classical
      cases hsel : firstPendingFormula? (F := F) (ρ := ρ) with
      | none =>
          -- common tree is a leaf; depth = 0, contradiction with succ.
          have : PDT.depth (commonCCDT_CNF_aux (F := F) (Nat.succ t) ρ) = 0 := by
            simp [commonCCDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have h' : Nat.succ t ≤ 0 := by
              simp [this] at hdepth
            exact (Nat.not_succ_le_zero _ h').elim
          exact hcontr.elim
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
              have hdepth' :
                  PDT.depth
                      (PDT.node ℓ.idx
                        (commonCCDT_CNF_aux (F := F) t ρ0)
                        (commonCCDT_CNF_aux (F := F) t ρ1))
                    ≥ Nat.succ t := by
                -- unfold common tree at this step
                simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1, PDT.depth] using hdepth
              have hbranch :=
                (depth_ge_succ_iff (i := ℓ.idx)
                  (L := commonCCDT_CNF_aux (F := F) t ρ0)
                  (R := commonCCDT_CNF_aux (F := F) t ρ1)
                  (t := t)).1 hdepth'
              cases hbranch with
              | inl hdepth_left =>
                  -- left branch (value = false)
                  let choice := chooseFreeLiteralChoice (w := selection.witness) false
                  have hchoice_lit : choice.literal = ℓ := by
                    simpa [ℓ] using
                      (chooseFreeLiteralChoice_literal (w := selection.witness) (b := false))
                  have hnext :
                      ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice) = ρ0 := by
                    have hidx : choice.literal.idx = ℓ.idx := by
                      simpa using congrArg Literal.idx hchoice_lit
                    have hval : choice.value = false := by rfl
                    have hassign_choice :
                        ρ.assign ℓ.idx false =
                          some (ClausePendingWitness.Selection.nextRestriction
                            (ρ := ρ) (C := selection.clause) (w := selection.witness)
                            (choice := choice)) := by
                      have hassign :=
                        ClausePendingWitness.Selection.assign_eq
                          (ρ := ρ) (C := selection.clause)
                          (w := selection.witness) (choice := choice)
                      rw [hidx, hval] at hassign
                      exact hassign
                    have : some (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := selection.witness)
                        (choice := choice)) = some ρ0 := by
                      have h1 :
                          ρ.assign ℓ.idx false =
                            some (ClausePendingWitness.Selection.nextRestriction
                              (ρ := ρ) (C := selection.clause) (w := selection.witness)
                              (choice := choice)) := by
                        simpa [hval] using hassign_choice
                      calc
                        some (ClausePendingWitness.Selection.nextRestriction
                            (ρ := ρ) (C := selection.clause) (w := selection.witness)
                            (choice := choice))
                            = ρ.assign ℓ.idx false := by
                                simpa using h1.symm
                        _ = some ρ0 := hassign0
                    exact Option.some.inj this
                  have hbad :=
                    commonTrace_of_depth_ge (F := F)
                      (t := t) (ρ := ρ0) hdepth_left
                  rcases hbad with ⟨trace, hdet⟩
                  have hcast_eq :
                      CommonTrace F ρ0 t =
                        CommonTrace F
                          (ClausePendingWitness.Selection.nextRestriction
                            (ρ := ρ) (C := selection.clause) (w := selection.witness)
                            (choice := choice)) t := by
                    simpa using
                      congrArg (fun r => CommonTrace F r t) hnext.symm
                  let trace_cast :
                      CommonTrace F
                        (ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice)) t :=
                    cast hcast_eq trace
                  have hdet_cast :
                      commonTraceDeterministic (F := F) trace_cast := by
                    have hcast :=
                      (commonTraceDeterministic_cast (F := F)
                        (ρ := ρ0)
                        (ρ' := ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice))
                        (t := t) (h := hnext.symm) (trace := trace)).2 hdet
                    simpa [trace_cast] using hcast
                  refine ⟨CommonTrace.cons i selection choice trace_cast, ?_⟩
                  refine ⟨hsel, ?_, hdet_cast⟩
                  simpa [ℓ] using hchoice_lit
              | inr hdepth_right =>
                  -- right branch (value = true)
                  let choice := chooseFreeLiteralChoice (w := selection.witness) true
                  have hchoice_lit : choice.literal = ℓ := by
                    simpa [ℓ] using
                      (chooseFreeLiteralChoice_literal (w := selection.witness) (b := true))
                  have hnext :
                      ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice) = ρ1 := by
                    have hidx : choice.literal.idx = ℓ.idx := by
                      simpa using congrArg Literal.idx hchoice_lit
                    have hval : choice.value = true := by rfl
                    have hassign_choice :
                        ρ.assign ℓ.idx true =
                          some (ClausePendingWitness.Selection.nextRestriction
                            (ρ := ρ) (C := selection.clause) (w := selection.witness)
                            (choice := choice)) := by
                      have hassign :=
                        ClausePendingWitness.Selection.assign_eq
                          (ρ := ρ) (C := selection.clause)
                          (w := selection.witness) (choice := choice)
                      rw [hidx, hval] at hassign
                      exact hassign
                    have : some (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := selection.witness)
                        (choice := choice)) = some ρ1 := by
                      have h1 :
                          ρ.assign ℓ.idx true =
                            some (ClausePendingWitness.Selection.nextRestriction
                              (ρ := ρ) (C := selection.clause) (w := selection.witness)
                              (choice := choice)) := by
                        simpa [hval] using hassign_choice
                      calc
                        some (ClausePendingWitness.Selection.nextRestriction
                            (ρ := ρ) (C := selection.clause) (w := selection.witness)
                            (choice := choice))
                            = ρ.assign ℓ.idx true := by
                                simpa using h1.symm
                        _ = some ρ1 := hassign1
                    exact Option.some.inj this
                  have hbad :=
                    commonTrace_of_depth_ge (F := F)
                      (t := t) (ρ := ρ1) hdepth_right
                  rcases hbad with ⟨trace, hdet⟩
                  have hcast_eq :
                      CommonTrace F ρ1 t =
                        CommonTrace F
                          (ClausePendingWitness.Selection.nextRestriction
                            (ρ := ρ) (C := selection.clause) (w := selection.witness)
                            (choice := choice)) t := by
                    simpa using
                      congrArg (fun r => CommonTrace F r t) hnext.symm
                  let trace_cast :
                      CommonTrace F
                        (ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice)) t :=
                    cast hcast_eq trace
                  have hdet_cast :
                      commonTraceDeterministic (F := F) trace_cast := by
                    have hcast :=
                      (commonTraceDeterministic_cast (F := F)
                        (ρ := ρ1)
                        (ρ' := ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice))
                        (t := t) (h := hnext.symm) (trace := trace)).2 hdet
                    simpa [trace_cast] using hcast
                  refine ⟨CommonTrace.cons i selection choice trace_cast, ?_⟩
                  refine ⟨hsel, ?_, hdet_cast⟩
                  simpa [ℓ] using hchoice_lit

theorem depth_ge_of_commonTrace
    (F : FormulaFamily n w) :
    ∀ {t : Nat} {ρ : Restriction n},
      BadFamily_deterministic_common (F := F) t ρ →
      t ≤ PDT.depth (commonCCDT_CNF_aux (F := F) t ρ)
  | 0, ρ, _ => by
      simp [commonCCDT_CNF_aux, PDT.depth]
  | Nat.succ t, ρ, hbad => by
      classical
      rcases hbad with ⟨trace, hdet⟩
      cases trace with
      | cons i selection choice rest =>
          -- unfold deterministic conditions
          rcases hdet with ⟨hsel, hchoice, hdet_tail⟩
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
          have hchoice_lit : choice.literal = ℓ := by
            simpa [ℓ] using hchoice
          -- determine next restriction
          have hassign_choice :
              ρ.assign ℓ.idx choice.value =
                some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := selection.witness)
                  (choice := choice)) := by
            have hidx : choice.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoice_lit
            have hassign :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause)
                (w := selection.witness) (choice := choice)
            rw [hidx] at hassign
            exact hassign
          -- split on value
          cases hval : choice.value with
          | false =>
              have hnext :
                  ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := selection.witness)
                      (choice := choice) = ρ0 := by
                have : some (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := selection.witness)
                      (choice := choice)) = some ρ0 := by
                  have h1 :
                      ρ.assign ℓ.idx false =
                        some (ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice)) := by
                    simpa [hval] using hassign_choice
                  calc
                    some (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := selection.witness)
                        (choice := choice))
                        = ρ.assign ℓ.idx false := by
                            simpa using h1.symm
                    _ = some ρ0 := hassign0
                exact Option.some.inj this
              have hdepth_tail :=
                depth_ge_of_commonTrace (F := F)
                  (t := t)
                  (ρ := ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := selection.witness)
                    (choice := choice)) ⟨rest, hdet_tail⟩
              have hdepth_tail' :
                  PDT.depth (commonCCDT_CNF_aux (F := F) t ρ0) ≥ t := by
                simpa [hnext] using hdepth_tail
              have hnode :
                  PDT.depth
                      (PDT.node ℓ.idx
                        (commonCCDT_CNF_aux (F := F) t ρ0)
                        (commonCCDT_CNF_aux (F := F) t ρ1))
                    ≥ Nat.succ t := by
                exact (depth_ge_succ_iff (i := ℓ.idx)
                  (L := commonCCDT_CNF_aux (F := F) t ρ0)
                  (R := commonCCDT_CNF_aux (F := F) t ρ1)
                  (t := t)).2 (Or.inl hdepth_tail')
              simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1, PDT.depth] using hnode
          | true =>
              have hnext :
                  ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := selection.witness)
                      (choice := choice) = ρ1 := by
                have : some (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := selection.witness)
                      (choice := choice)) = some ρ1 := by
                  have h1 :
                      ρ.assign ℓ.idx true =
                        some (ClausePendingWitness.Selection.nextRestriction
                          (ρ := ρ) (C := selection.clause) (w := selection.witness)
                          (choice := choice)) := by
                    simpa [hval] using hassign_choice
                  calc
                    some (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := selection.witness)
                        (choice := choice))
                        = ρ.assign ℓ.idx true := by
                            simpa using h1.symm
                    _ = some ρ1 := hassign1
                exact Option.some.inj this
              have hdepth_tail :=
                depth_ge_of_commonTrace (F := F)
                  (t := t)
                  (ρ := ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := selection.witness)
                    (choice := choice)) ⟨rest, hdet_tail⟩
              have hdepth_tail' :
                  PDT.depth (commonCCDT_CNF_aux (F := F) t ρ1) ≥ t := by
                simpa [hnext] using hdepth_tail
              have hnode :
                  PDT.depth
                      (PDT.node ℓ.idx
                        (commonCCDT_CNF_aux (F := F) t ρ0)
                        (commonCCDT_CNF_aux (F := F) t ρ1))
                    ≥ Nat.succ t := by
                exact (depth_ge_succ_iff (i := ℓ.idx)
                  (L := commonCCDT_CNF_aux (F := F) t ρ0)
                  (R := commonCCDT_CNF_aux (F := F) t ρ1)
                  (t := t)).2 (Or.inr hdepth_tail')
              simpa [commonCCDT_CNF_aux, hsel, ℓ, ρ0, ρ1, PDT.depth] using hnode

theorem badEvent_common_iff_badFamilyDet_common
    (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) :
    BadEvent_common (F := F) t ρ ↔
      BadFamily_deterministic_common (F := F) t ρ := by
  constructor
  · intro h
    exact commonTrace_of_depth_ge (F := F) (t := t) (ρ := ρ) h
  · intro h
    exact depth_ge_of_commonTrace (F := F) (t := t) (ρ := ρ) h


end MultiSwitching
end AC0
end Pnp3
