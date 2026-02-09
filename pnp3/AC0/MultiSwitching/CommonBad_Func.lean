import Core.BooleanBasics
import AC0.MultiSwitching.CommonCCDT_Func
import AC0.MultiSwitching.TraceBridge

/-!
  pnp3/AC0/MultiSwitching/CommonBad_Func.lean

  Common‑CCDT "bad" predicate and deterministic traces for FuncCNF (atoms).

  Здесь детерминированность требует, чтобы на каждом шаге выбирались
  `firstPendingFormula_atom?`, `firstPendingClause?`, `firstPendingLit?`
  и `Atom.nextVar`. Ветвление по значению бита остаётся свободным.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core
open Restriction

variable {n : Nat}

/-!
### Common trace for atom‑CNF family
-/

inductive CommonTraceAtom (Fs : List (FuncCNF n)) : Restriction n → Nat → Type
  | nil {ρ : Restriction n} : CommonTraceAtom Fs ρ 0
  | cons {ρ : Restriction n}
      (F : FuncCNF n)
      (C : FuncClause n)
      (ℓ : AtomLit n)
      (i : Fin n)
      (b : Bool)
      {t : Nat}
      (rest : CommonTraceAtom Fs ((ρ.assign i b).getD ρ) t) :
      CommonTraceAtom Fs ρ (Nat.succ t)

namespace CommonTraceAtom

@[simp] noncomputable def finalRestriction
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t) : Restriction n :=
  match trace with
  | CommonTraceAtom.nil => ρ
  | CommonTraceAtom.cons _ _ _ _ _ rest => finalRestriction rest

@[simp] noncomputable def assignedBitFixes
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t) : List (BitFix n) :=
  match trace with
  | CommonTraceAtom.nil => []
  | CommonTraceAtom.cons _ _ _ i b rest =>
      (i, b) :: assignedBitFixes rest

lemma assignedBitFixes_length
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t) :
    (assignedBitFixes trace).length = t := by
  induction trace with
  | nil =>
      simp [assignedBitFixes]
  | @cons ρ F C ℓ i b t rest ih =>
      simp [assignedBitFixes, ih]

end CommonTraceAtom

/-!
### Deterministic predicate
-/

def commonTraceDeterministic_atom
    {Fs : List (FuncCNF n)} :
    {ρ : Restriction n} → {t : Nat} →
      CommonTraceAtom (n := n) Fs ρ t → Prop
  | _, _, CommonTraceAtom.nil => True
  | ρ, _, CommonTraceAtom.cons F C ℓ i _ rest =>
      firstPendingFormula_atom? (ρ := ρ) Fs = some F
        ∧ firstPendingClause? (ρ := ρ) F = some C
        ∧ firstPendingLit? (ρ := ρ) C = some ℓ
        ∧ ℓ.atom.nextVar ρ = some i
        ∧ commonTraceDeterministic_atom (Fs := Fs) rest

/-!
### Reconstructing restriction from deterministic trace
-/

lemma reconstruct_eq_original_atom
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t)
    (hdet : commonTraceDeterministic_atom (Fs := Fs) trace) :
    Core.SelectionTrace.reconstructRestriction
        (ρ := CommonTraceAtom.finalRestriction trace)
        (CommonTraceAtom.assignedBitFixes trace) = ρ := by
  induction trace with
  | nil =>
      simp [CommonTraceAtom.assignedBitFixes, CommonTraceAtom.finalRestriction,
        Core.SelectionTrace.reconstructRestriction]
  | @cons ρ F C ℓ i b t rest ih =>
      rcases hdet with ⟨hselF, hselC, hselL, hvar, hdetRest⟩
      have hfree : ρ.mask i = none := ℓ.atom.nextVar_free (ρ := ρ) (i := i) hvar
      have hmem : i ∈ ρ.freeIndicesList := by
        exact (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hfree
      have hassign :
          ∃ ρ', ρ.assign i b = some ρ' ∧ (ρ.assign i b).getD ρ = ρ' := by
        exact assign_getD_eq_of_mem_freeIndicesList (ρ := ρ) (i := i) (b := b) hmem
      rcases hassign with ⟨ρ', hassign, hgetD⟩
      have hrest : ((ρ.assign i b).getD ρ) = ρ' := hgetD
      have hih := ih hdetRest
      -- unfold reconstruction for the cons step
      have hstep :
          Core.SelectionTrace.reconstructRestriction
              (ρ := CommonTraceAtom.finalRestriction (CommonTraceAtom.cons F C ℓ i b rest))
              (CommonTraceAtom.assignedBitFixes (CommonTraceAtom.cons F C ℓ i b rest))
            =
              (Core.SelectionTrace.reconstructRestriction
                (ρ := CommonTraceAtom.finalRestriction rest)
                (CommonTraceAtom.assignedBitFixes rest)).unassign i := by
        simp [CommonTraceAtom.assignedBitFixes, CommonTraceAtom.finalRestriction,
          Core.SelectionTrace.reconstructRestriction]
      -- use IH and undo the assignment
      have hunassign' : ((ρ.assign i b).getD ρ).unassign i = ρ := by
        have hunassign'' : ρ'.unassign i = ρ := by
          exact Restriction.unassign_assign_of_free (ρ := ρ) (i := i) (b := b)
            (ρ' := ρ') hassign hfree
        have hrest' : ρ' = (ρ.assign i b).getD ρ := by
          exact hrest.symm
        simpa [hrest'] using hunassign''
      have hunassign :
          (Core.SelectionTrace.reconstructRestriction
              (ρ := CommonTraceAtom.finalRestriction rest)
              (CommonTraceAtom.assignedBitFixes rest)).unassign i = ρ := by
        calc
          (Core.SelectionTrace.reconstructRestriction
              (ρ := CommonTraceAtom.finalRestriction rest)
              (CommonTraceAtom.assignedBitFixes rest)).unassign i
              = ((ρ.assign i b).getD ρ).unassign i := by
                  simpa [hih]
          _ = ρ := hunassign'
      exact Eq.trans hstep hunassign

lemma finalRestriction_mem_R_s_atom
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t s : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t)
    (hdet : commonTraceDeterministic_atom (Fs := Fs) trace)
    (hρ : ρ ∈ R_s (n := n) s) :
    CommonTraceAtom.finalRestriction trace ∈ R_s (n := n) (s - t) := by
  induction trace generalizing s with
  | nil =>
      simpa [R_s, CommonTraceAtom.finalRestriction] using hρ
  | @cons ρ F C ℓ i b t rest ih =>
      rcases hdet with ⟨hselF, hselC, hselL, hvar, hdetRest⟩
      have hfree : ρ.mask i = none := ℓ.atom.nextVar_free (ρ := ρ) (i := i) hvar
      have hmem : i ∈ ρ.freeIndicesList := by
        exact (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hfree
      have hassign :
          ∃ ρ', ρ.assign i b = some ρ' ∧ (ρ.assign i b).getD ρ = ρ' := by
        exact assign_getD_eq_of_mem_freeIndicesList (ρ := ρ) (i := i) (b := b) hmem
      rcases hassign with ⟨ρ', hassign, hgetD⟩
      have hcount :
          ρ'.freeCount = ρ.freeCount - 1 := by
        exact Restriction.freeCount_assign_of_mem (ρ := ρ) (i := i) (b := b) hmem hassign
      have hρcount : ρ.freeCount = s := (mem_R_s (n := n) (s := s)).1 hρ
      have hρcount' : ρ.freeIndicesList.length = s := by
        simpa [Restriction.freeCount] using hρcount
      have hnext' : ρ' ∈ R_s (n := n) (s - 1) := by
        apply (mem_R_s (n := n) (s := s - 1)).2
        simpa [Restriction.freeCount, hρcount'] using hcount
      have hnext : (ρ.assign i b).getD ρ ∈ R_s (n := n) (s - 1) := by
        have hnextfc : ρ'.freeCount = s - 1 := by
          exact (mem_R_s (n := n) (s := s - 1)).1 hnext'
        have hnextfc' : ((ρ.assign i b).getD ρ).freeCount = s - 1 := by
          have hgetD' : ρ' = (ρ.assign i b).getD ρ := by
            exact hgetD.symm
          simpa [hgetD'] using hnextfc
        exact (mem_R_s (n := n) (s := s - 1)).2 hnextfc'
      have hfinal := ih (s := s - 1) hdetRest hnext
      -- `(s - 1) - t = s - (t + 1)`
      simpa [CommonTraceAtom.finalRestriction, hgetD,
        Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfinal

/-!
### Deterministic bad predicate
-/

def BadFamily_deterministic_common_atom
    (Fs : List (FuncCNF n)) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ trace : CommonTraceAtom (n := n) Fs ρ t,
    commonTraceDeterministic_atom (Fs := Fs) trace

noncomputable instance instDecidableBadFamilyDetCommonAtom
    (Fs : List (FuncCNF n)) (t : Nat) :
    DecidablePred (BadFamily_deterministic_common_atom (Fs := Fs) t) := by
  classical
  intro ρ
  infer_instance

noncomputable instance instDecidableBadEventCommonAtom
    (Fs : List (FuncCNF n)) (t : Nat) :
    DecidablePred (BadEvent_common_atom (Fs := Fs) t) := by
  intro ρ
  dsimp [BadEvent_common_atom]
  infer_instance

/-!
### Depth ≥ t → deterministic common trace (atoms)
-/

theorem commonTrace_of_depth_ge_atom
    (Fs : List (FuncCNF n)) :
    ∀ {t : Nat} {ρ : Restriction n},
      t ≤ PDT.depth (commonCCDT_Family_atom (Fs := Fs) t ρ) →
      BadFamily_deterministic_common_atom (Fs := Fs) t ρ
  | 0, ρ, _ => by
      exact ⟨CommonTraceAtom.nil, by simp [commonTraceDeterministic_atom]⟩
  | Nat.succ t, ρ, hdepth => by
      classical
      cases hsel : firstPendingFormula_atom? (ρ := ρ) Fs with
      | none =>
          have : PDT.depth (commonCCDT_Family_atom (Fs := Fs) (Nat.succ t) ρ) = 0 := by
            simp [commonCCDT_Family_atom, hsel, PDT.depth]
          have hcontr : False := by
            have h' : Nat.succ t ≤ 0 := by
              simpa [this] using hdepth
            exact (Nat.not_succ_le_zero _ h').elim
          exact hcontr.elim
      | some F =>
          cases hselC : firstPendingClause? (ρ := ρ) F with
          | none =>
              have : PDT.depth (commonCCDT_Family_atom (Fs := Fs) (Nat.succ t) ρ) = 0 := by
                simp [commonCCDT_Family_atom, hsel, hselC, PDT.depth]
              have hcontr : False := by
                have h' : Nat.succ t ≤ 0 := by
                  simpa [this] using hdepth
                exact (Nat.not_succ_le_zero _ h').elim
              exact hcontr.elim
          | some C =>
              cases hselL : firstPendingLit? (ρ := ρ) C with
              | none =>
                  have : PDT.depth (commonCCDT_Family_atom (Fs := Fs) (Nat.succ t) ρ) = 0 := by
                    simp [commonCCDT_Family_atom, hsel, hselC, hselL, PDT.depth]
                  have hcontr : False := by
                    have h' : Nat.succ t ≤ 0 := by
                      simpa [this] using hdepth
                    exact (Nat.not_succ_le_zero _ h').elim
                  exact hcontr.elim
              | some ℓ =>
                  cases hvar : ℓ.atom.nextVar ρ with
                  | none =>
                      have hpending :
                          atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending :=
                        pendingLit_of_firstPendingLit?_some (ρ := ρ) (C := C) (ℓ := ℓ) hselL
                      have hdec : AtomLit.decide ℓ ρ = none :=
                        decide_none_of_atomLitStatus_pending (ρ := ρ) (ℓ := ℓ) hpending
                      rcases AtomLit.nextVar_of_undecided (ℓ := ℓ) (ρ := ρ) hdec with ⟨i, hi⟩
                      have : (none : Option (Fin n)) = some i := by
                        exact hvar.symm.trans hi
                      exact (by cases this)
                  | some i =>
                      let ρ0 := (ρ.assign i false).getD ρ
                      let ρ1 := (ρ.assign i true).getD ρ
                      have hdepth' :
                          PDT.depth
                              (PDT.node i
                                (commonCCDT_Family_atom (Fs := Fs) t ρ0)
                                (commonCCDT_Family_atom (Fs := Fs) t ρ1))
                            ≥ Nat.succ t := by
                        simpa [commonCCDT_Family_atom, hsel, hselC, hselL, hvar, ρ0, ρ1, PDT.depth]
                          using hdepth
                      have hbranch :=
                        (depth_ge_succ_iff (i := i)
                          (L := commonCCDT_Family_atom (Fs := Fs) t ρ0)
                          (R := commonCCDT_Family_atom (Fs := Fs) t ρ1)
                          (t := t)).1 hdepth'
                      cases hbranch with
                      | inl hleft =>
                          rcases commonTrace_of_depth_ge_atom (Fs := Fs)
                            (t := t) (ρ := ρ0) hleft with ⟨trace, hdet⟩
                          refine ⟨CommonTraceAtom.cons F C ℓ i false trace, ?_⟩
                          exact ⟨hsel, hselC, hselL, hvar, hdet⟩
                      | inr hright =>
                          rcases commonTrace_of_depth_ge_atom (Fs := Fs)
                            (t := t) (ρ := ρ1) hright with ⟨trace, hdet⟩
                          refine ⟨CommonTraceAtom.cons F C ℓ i true trace, ?_⟩
                          exact ⟨hsel, hselC, hselL, hvar, hdet⟩

lemma badEvent_common_atom_implies_badFamilyDet
    {Fs : List (FuncCNF n)} {t : Nat} {ρ : Restriction n} :
    BadEvent_common_atom (Fs := Fs) t ρ →
      BadFamily_deterministic_common_atom (Fs := Fs) t ρ := by
  intro h
  exact commonTrace_of_depth_ge_atom (Fs := Fs) (t := t) (ρ := ρ) h

end MultiSwitching
end AC0
end Pnp3
