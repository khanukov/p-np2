import AC0.MultiSwitching.FuncCNF
import AC0.MultiSwitching.DecidesAtoms
import Core.PDT

/-!
  pnp3/AC0/MultiSwitching/CommonCCDT_Func.lean

  Common‑CCDT for CNF built from atoms (functions + branching strategy).
  This mirrors `CommonCCDT.lean` for literal CNF, but branches on
  `Atom.nextVar` instead of literal indices.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-!
  Status definitions for atoms and clauses.
-/

/-- Status of a literal under restriction (decided or pending). -/
inductive AtomLitStatus
  | decided : Bool → AtomLitStatus
  | pending : AtomLitStatus
  deriving DecidableEq

/-- Status of a literal under restriction. -/
@[simp] def atomLitStatus {n : Nat} (ρ : Restriction n) (ℓ : AtomLit n) : AtomLitStatus :=
  match AtomLit.decide ℓ ρ with
  | some b => AtomLitStatus.decided b
  | none => AtomLitStatus.pending

lemma atomLitStatus_pending_iff
    {n : Nat} {ρ : Restriction n} {ℓ : AtomLit n} :
    atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending ↔
      AtomLit.decide ℓ ρ = none := by
  cases hdec : ℓ.atom.decide ρ <;>
    simp [atomLitStatus, AtomLit.decide, hdec]

/-- Clause status: satisfied, falsified, or pending. -/
inductive AtomClauseStatus
  | satisfied
  | falsified
  | pending
  deriving DecidableEq

/-- Status of a clause under restriction. -/
@[simp] def atomClauseStatus {n : Nat} (ρ : Restriction n) (C : FuncClause n) : AtomClauseStatus :=
  if _hsat : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true then
    AtomClauseStatus.satisfied
  else if _hfalse : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false then
    AtomClauseStatus.falsified
  else
    AtomClauseStatus.pending

/-!
  Helper lemmas: `find?` and clause decisions.
-/

lemma find?_eq_none_forall {α : Type _} (p : α → Bool) :
    ∀ xs : List α, xs.find? p = none → ∀ x ∈ xs, p x = false
  | [], h, x, hx => by
      cases hx
  | x :: xs, h, y, hy => by
      by_cases hp : p x
      · -- impossible: find? would return `some x`
        simp [List.find?, hp] at h
      · have h' : xs.find? p = none := by
          simpa [List.find?, hp] using h
        have hy' : y = x ∨ y ∈ xs := by
          simpa using hy
        cases hy' with
        | inl hxy =>
            subst hxy
            simp [hp]
        | inr hyxs =>
            exact find?_eq_none_forall p xs h' y hyxs

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

lemma decidesClauseOn_of_status_not_pending
    {n : Nat} {ρ : Restriction n} {C : FuncClause n}
    (h : atomClauseStatus (ρ := ρ) C ≠ AtomClauseStatus.pending) :
    DecidesClauseOnAtom (ρ := ρ) C := by
  unfold DecidesClauseOnAtom
  by_cases hsat : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true
  · refine ⟨true, ?_⟩
    simp [FuncClause.decide, hsat, -AtomLit.decide]
  · by_cases hfalse : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false
    · refine ⟨false, ?_⟩
      unfold FuncClause.decide
      simp [hsat, -AtomLit.decide]
      exact hfalse
    · have hstatus : atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending := by
        by_cases hsat' : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true
        · exact (hsat hsat').elim
        · by_cases hfalse' : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false
          · exact (hfalse hfalse').elim
          · simp [atomClauseStatus, hsat', hfalse', -AtomLit.decide]
      exact (h hstatus).elim

/-!
  Pending selectors.
-/

/-- First pending literal in a clause (by list order). -/
def firstPendingLit? {n : Nat} (ρ : Restriction n) (C : FuncClause n) :
    Option (AtomLit n) :=
  C.lits.find? (fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending))

/-- First pending clause in a CNF. -/
def firstPendingClause? {n : Nat} (ρ : Restriction n) (F : FuncCNF n) :
    Option (FuncClause n) :=
  F.clauses.find? (fun C => decide (atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending))

/-- First pending formula in a family (by list order). -/
def firstPendingFormula_atom? {n : Nat} (ρ : Restriction n) (Fs : List (FuncCNF n)) :
    Option (FuncCNF n) :=
  Fs.find? (fun F => (firstPendingClause? (ρ := ρ) F).isSome)

lemma pendingClause_of_firstPendingClause?_some
    {n : Nat} {ρ : Restriction n} {F : FuncCNF n} {C : FuncClause n}
    (hsel : firstPendingClause? (ρ := ρ) F = some C) :
    atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending := by
  have hsel' :
      F.clauses.find?
        (fun C => decide (atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending)) = some C := by
    simpa [firstPendingClause?] using hsel
  have hpred := (find?_some_mem
    (p := fun C => decide (atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending))
    (xs := F.clauses) (a := C) hsel').1
  exact (decide_eq_true_iff (p := atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending)).1 hpred

lemma pendingLit_of_firstPendingLit?_some
    {n : Nat} {ρ : Restriction n} {C : FuncClause n} {ℓ : AtomLit n}
    (hsel : firstPendingLit? (ρ := ρ) C = some ℓ) :
    atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending := by
  have hsel' :
      C.lits.find? (fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending)) = some ℓ := by
    simpa [firstPendingLit?] using hsel
  have hpred := (find?_some_mem
    (p := fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending))
    (xs := C.lits) (a := ℓ) hsel').1
  exact (decide_eq_true_iff (p := atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending)).1 hpred

lemma decide_none_of_atomLitStatus_pending
    {n : Nat} {ρ : Restriction n} {ℓ : AtomLit n}
    (hp : atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending) :
    AtomLit.decide ℓ ρ = none := by
  exact (atomLitStatus_pending_iff (ρ := ρ) (ℓ := ℓ)).1 hp

lemma pending_clause_has_pending_lit
    {n : Nat} {ρ : Restriction n} {C : FuncClause n}
    (hpend : atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending) :
    ∃ ℓ ∈ C.lits, atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending := by
  classical
  have hnone : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = none := by
    by_cases hsat : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true
    · -- contradiction: satisfied but pending
      exfalso
      have hpend' := hpend
      simp [atomClauseStatus, hsat, -AtomLit.decide] at hpend'
    · by_cases hfalse : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false
      · exfalso
        have hpend' := hpend
        simp [atomClauseStatus, hsat, -AtomLit.decide] at hpend'
        rcases hpend' with ⟨ℓ, hℓ, hnot⟩
        exact hnot (hfalse ℓ hℓ)
      · -- if not all false, some literal is not decided false; since no true, it must be none
        by_contra hnone
        have hall : ∀ ℓ ∈ C.lits, ∃ b, AtomLit.decide ℓ ρ = some b := by
          intro ℓ hℓ
          cases hdec : AtomLit.decide ℓ ρ with
          | none =>
              exact (hnone ⟨ℓ, hℓ, hdec⟩).elim
          | some b =>
              exact ⟨b, rfl⟩
        have hfalse' : ∀ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some false := by
          intro ℓ hℓ
          rcases hall ℓ hℓ with ⟨b, hb⟩
          cases hb' : b with
          | true =>
              have htrue : AtomLit.decide ℓ ρ = some true := by
                simpa [AtomLit.decide, hb'] using hb
              have : ∃ ℓ ∈ C.lits, AtomLit.decide ℓ ρ = some true := by
                exact ⟨ℓ, hℓ, htrue⟩
              exact (hsat this).elim
          | false =>
              simpa [AtomLit.decide, hb'] using hb
        exact (hfalse hfalse').elim
  rcases hnone with ⟨ℓ, hℓ, hdec⟩
  refine ⟨ℓ, hℓ, ?_⟩
  exact (atomLitStatus_pending_iff (ρ := ρ) (ℓ := ℓ)).2 hdec

lemma assign_getD_eq_of_mem_freeIndicesList
    {n : Nat} {ρ : Restriction n} {i : Fin n} {b : Bool}
    (hmem : i ∈ ρ.freeIndicesList) :
    ∃ ρ', ρ.assign i b = some ρ' ∧ (ρ.assign i b).getD ρ = ρ' := by
  rcases Restriction.assign_some_of_mem_freeIndicesList
    (ρ := ρ) (i := i) (b := b) hmem with ⟨ρ', hassign⟩
  refine ⟨ρ', hassign, ?_⟩
  cases h : Subcube.assign ρ.mask i b with
  | none =>
      -- contradiction: assign is none
      simp [Restriction.assign, h] at hassign
  | some β =>
      have hρ' : ρ' = ⟨β⟩ := by
        simpa [Restriction.assign, h] using hassign.symm
      simp [Option.getD, Restriction.assign, h, hρ']
lemma pendingFormula_has_pendingClause
    {n : Nat} {ρ : Restriction n} {Fs : List (FuncCNF n)} {F : FuncCNF n}
    (hsel : firstPendingFormula_atom? (ρ := ρ) Fs = some F) :
    ∃ C, firstPendingClause? (ρ := ρ) F = some C := by
  have hsel' :
      Fs.find? (fun F => (firstPendingClause? (ρ := ρ) F).isSome) = some F := by
    simpa [firstPendingFormula_atom?] using hsel
  have hpred := (find?_some_mem
    (p := fun F => (firstPendingClause? (ρ := ρ) F).isSome)
    (xs := Fs) (a := F) hsel').1
  cases h : firstPendingClause? (ρ := ρ) F with
  | none =>
      simp [h] at hpred
  | some C =>
      exact ⟨C, by simp⟩

lemma decidesCNFOnAtom_of_firstPendingClause?_none
    {n : Nat} {ρ : Restriction n} {F : FuncCNF n}
    (hnone : firstPendingClause? (ρ := ρ) F = none) :
    DecidesCNFOnAtom (ρ := ρ) F := by
  intro C hC
  have hnone' :
      F.clauses.find?
        (fun C => decide (atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending)) = none := by
    simpa [firstPendingClause?] using hnone
  have hpred :=
    find?_eq_none_forall
      (p := fun C => decide (atomClauseStatus (ρ := ρ) C = AtomClauseStatus.pending))
      (xs := F.clauses) hnone' C hC
  have hnotpending : atomClauseStatus (ρ := ρ) C ≠ AtomClauseStatus.pending := by
    intro hpending
    have hpred' := hpred
    simp at hpred'
    exact hpred' hpending
  exact decidesClauseOn_of_status_not_pending (ρ := ρ) (C := C) hnotpending

/-- CCDT for a single CNF of atoms. -/
noncomputable def commonCCDT_CNF_atom
    {n : Nat} (F : FuncCNF n) (fuel : Nat) : Restriction n → PDT n := by
  classical
  intro ρ
  match fuel with
  | 0 => exact PDT.leaf (ρ.mask)
  | Nat.succ t =>
      match firstPendingClause? (ρ := ρ) F with
      | none => exact PDT.leaf (ρ.mask)
      | some C =>
          match firstPendingLit? (ρ := ρ) C with
          | none => exact PDT.leaf (ρ.mask)
          | some ℓ =>
              match ℓ.atom.nextVar ρ with
              | none => exact PDT.leaf (ρ.mask)
              | some i =>
                  let ρ0 := (ρ.assign i false).getD ρ
                  let ρ1 := (ρ.assign i true).getD ρ
                  exact PDT.node i
                    (commonCCDT_CNF_atom F t ρ0)
                    (commonCCDT_CNF_atom F t ρ1)

/-- Family CCDT: run CCDT for each formula and refine. -/
noncomputable def commonCCDT_Family_atom
    {n : Nat} (Fs : List (FuncCNF n)) (fuel : Nat) : Restriction n → PDT n := by
  classical
  intro ρ
  match fuel with
  | 0 => exact PDT.leaf (ρ.mask)
  | Nat.succ t =>
      match firstPendingFormula_atom? (ρ := ρ) Fs with
      | none => exact PDT.leaf (ρ.mask)
      | some F =>
          match firstPendingClause? (ρ := ρ) F with
          | none => exact PDT.leaf (ρ.mask)
          | some C =>
              match firstPendingLit? (ρ := ρ) C with
              | none => exact PDT.leaf (ρ.mask)
              | some ℓ =>
                  match ℓ.atom.nextVar ρ with
                  | none => exact PDT.leaf (ρ.mask)
                  | some i =>
                      let ρ0 := (ρ.assign i false).getD ρ
                      let ρ1 := (ρ.assign i true).getD ρ
                      exact PDT.node i
                        (commonCCDT_Family_atom (Fs := Fs) t ρ0)
                        (commonCCDT_Family_atom (Fs := Fs) t ρ1)

/-- Good family: depth < t for common‑CCDT. -/
@[simp] def BadEvent_common_atom
    {n : Nat} (Fs : List (FuncCNF n)) (t : Nat) (ρ : Restriction n) : Prop :=
  t ≤ PDT.depth (commonCCDT_Family_atom (Fs := Fs) t ρ)

@[simp] def GoodFamily_common_atom
    {n : Nat} (Fs : List (FuncCNF n)) (t : Nat) (ρ : Restriction n) : Prop :=
  ¬ BadEvent_common_atom (Fs := Fs) t ρ

/-- If good, then depth < t. -/
lemma depth_lt_of_good_common_atom
    {n : Nat} (Fs : List (FuncCNF n)) (t : Nat) (ρ : Restriction n)
    (hgood : GoodFamily_common_atom (Fs := Fs) t ρ) :
    PDT.depth (commonCCDT_Family_atom (Fs := Fs) t ρ) < t := by
  by_contra hge
  exact hgood (by exact Nat.le_of_not_gt hge)

/-!
  Leaf decisions for common‑CCDT on a single CNF.
-/

theorem leaf_decidesCNF_of_depth_lt
    {n : Nat} (F : FuncCNF n) :
    ∀ (t : Nat) (ρ : Restriction n) (β : Subcube n),
      β ∈ PDT.leaves (commonCCDT_CNF_atom (F := F) t ρ) →
      PDT.depth (commonCCDT_CNF_atom (F := F) t ρ) < t →
      DecidesCNFOnAtom (ρ := ⟨β⟩) (F := F)
  | 0, ρ, β, hβ, hdepth => by
      exact (Nat.not_lt_zero _ hdepth).elim
  | Nat.succ fuel, ρ, β, hβ, hdepth => by
      classical
      cases hsel : firstPendingClause? (ρ := ρ) F with
      | none =>
          have hβ' : β = ρ.mask := by
            simpa [commonCCDT_CNF_atom, hsel, PDT.leaves] using hβ
          subst hβ'
          have hdec := decidesCNFOnAtom_of_firstPendingClause?_none
            (ρ := ρ) (F := F) hsel
          simpa using hdec
      | some C =>
          cases hselLit : firstPendingLit? (ρ := ρ) C with
          | none =>
              -- Impossible: pending clause must have a pending literal.
              exfalso
              have hpendC := pendingClause_of_firstPendingClause?_some (ρ := ρ) (F := F) (C := C) hsel
              rcases pending_clause_has_pending_lit (ρ := ρ) (C := C) hpendC with ⟨ℓ, hℓ, hpendℓ⟩
              have hnone' :
                  C.lits.find?
                    (fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending)) = none := by
                simpa [firstPendingLit?] using hselLit
              have hpred :=
                find?_eq_none_forall
                  (p := fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending))
                  (xs := C.lits) hnone' ℓ hℓ
              have hnot : atomLitStatus (ρ := ρ) ℓ ≠ AtomLitStatus.pending := by
                have hpred' := hpred
                simp at hpred'
                exact hpred'
              exact (hnot hpendℓ).elim
          | some ℓ =>
              cases hvar : ℓ.atom.nextVar ρ with
              | none =>
                  -- Impossible: pending literal must have a nextVar.
                  exfalso
                  have hpendℓ := pendingLit_of_firstPendingLit?_some (ρ := ρ) (C := C) (ℓ := ℓ) hselLit
                  have hdec : AtomLit.decide ℓ ρ = none :=
                    decide_none_of_atomLitStatus_pending (ρ := ρ) (ℓ := ℓ) hpendℓ
                  rcases AtomLit.nextVar_of_undecided (ℓ := ℓ) (ρ := ρ) hdec with ⟨i, hi⟩
                  exact (Option.noConfusion (Eq.trans hvar.symm hi))
              | some i =>
                  have hfree : ρ.mask i = none := ℓ.atom.nextVar_free (ρ := ρ) (i := i) hvar
                  have hmem : i ∈ ρ.freeIndicesList :=
                    (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hfree
                  let ρ0 := (ρ.assign i false).getD ρ
                  let ρ1 := (ρ.assign i true).getD ρ
                  have hdepth' :
                      Nat.max
                        (PDT.depth (commonCCDT_CNF_atom (F := F) fuel ρ0))
                        (PDT.depth (commonCCDT_CNF_atom (F := F) fuel ρ1))
                      < fuel := by
                    have hdepth_node :
                        Nat.succ
                          (Nat.max
                            (PDT.depth (commonCCDT_CNF_atom (F := F) fuel ρ0))
                            (PDT.depth (commonCCDT_CNF_atom (F := F) fuel ρ1)))
                          < Nat.succ fuel := by
                      simpa [commonCCDT_CNF_atom, hsel, hselLit, hvar, ρ0, ρ1, PDT.depth] using hdepth
                    exact (Nat.succ_lt_succ_iff).1 hdepth_node
                  have hdepth_left :
                      PDT.depth (commonCCDT_CNF_atom (F := F) fuel ρ0) < fuel := by
                    exact lt_of_le_of_lt (Nat.le_max_left _ _) hdepth'
                  have hdepth_right :
                      PDT.depth (commonCCDT_CNF_atom (F := F) fuel ρ1) < fuel := by
                    exact lt_of_le_of_lt (Nat.le_max_right _ _) hdepth'
                  have hβ' :
                      β ∈ PDT.leaves (commonCCDT_CNF_atom (F := F) fuel ρ0) ∨
                      β ∈ PDT.leaves (commonCCDT_CNF_atom (F := F) fuel ρ1) := by
                    have : β ∈
                        PDT.leaves
                          (PDT.node i
                            (commonCCDT_CNF_atom (F := F) fuel ρ0)
                            (commonCCDT_CNF_atom (F := F) fuel ρ1)) := by
                      simpa [commonCCDT_CNF_atom, hsel, hselLit, hvar, ρ0, ρ1] using hβ
                    have hmem :
                        β ∈
                          (PDT.leaves (commonCCDT_CNF_atom (F := F) fuel ρ0)) ++
                            (PDT.leaves (commonCCDT_CNF_atom (F := F) fuel ρ1)) := by
                      simpa [PDT.leaves] using this
                    exact List.mem_append.mp hmem
                  cases hβ' with
                  | inl hβ0 =>
                      exact leaf_decidesCNF_of_depth_lt
                        (F := F) fuel ρ0 β hβ0 hdepth_left
                  | inr hβ1 =>
                      exact leaf_decidesCNF_of_depth_lt
                        (F := F) fuel ρ1 β hβ1 hdepth_right

/-!
  Leaf decisions for common‑CCDT on a family of CNFs.
-/

lemma decidesFamilyOnAtom_of_firstPendingFormula_atom?_none
    {n : Nat} {ρ : Restriction n} {Fs : List (FuncCNF n)}
    (hnone : firstPendingFormula_atom? (ρ := ρ) Fs = none) :
    DecidesFamilyOnAtom (ρ := ρ) Fs := by
  intro F hF
  have hnone' :
      Fs.find? (fun F => (firstPendingClause? (ρ := ρ) F).isSome) = none := by
    simpa [firstPendingFormula_atom?] using hnone
  have hpred :=
    find?_eq_none_forall
      (p := fun F => (firstPendingClause? (ρ := ρ) F).isSome)
      (xs := Fs) hnone' F hF
  have hnoneClause : firstPendingClause? (ρ := ρ) F = none := by
    cases h : firstPendingClause? (ρ := ρ) F with
    | none =>
        rfl
    | some C =>
        have : (firstPendingClause? (ρ := ρ) F).isSome = true := by
          simp [h]
        simpa [this] using hpred
  exact decidesCNFOnAtom_of_firstPendingClause?_none (ρ := ρ) (F := F) hnoneClause

theorem leaf_decidesFamily_of_depth_lt_atom
    {n : Nat} (Fs : List (FuncCNF n)) :
    ∀ (t : Nat) (ρ : Restriction n) (β : Subcube n),
      β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) t ρ) →
      PDT.depth (commonCCDT_Family_atom (Fs := Fs) t ρ) < t →
      DecidesFamilyOnAtom (ρ := ⟨β⟩) Fs
  | 0, ρ, β, hβ, hdepth => by
      exact (Nat.not_lt_zero _ hdepth).elim
  | Nat.succ fuel, ρ, β, hβ, hdepth => by
      classical
      cases hsel : firstPendingFormula_atom? (ρ := ρ) Fs with
      | none =>
          have hβ' : β = ρ.mask := by
            simpa [commonCCDT_Family_atom, hsel, PDT.leaves] using hβ
          subst hβ'
          have hdec := decidesFamilyOnAtom_of_firstPendingFormula_atom?_none
            (ρ := ρ) (Fs := Fs) hsel
          simpa using hdec
      | some F =>
          cases hselC : firstPendingClause? (ρ := ρ) F with
          | none =>
              exfalso
              rcases pendingFormula_has_pendingClause (ρ := ρ) (Fs := Fs) (F := F) hsel with ⟨C, hC⟩
              simp [hselC] at hC
          | some C =>
              cases hselLit : firstPendingLit? (ρ := ρ) C with
              | none =>
                  exfalso
                  have hpendC := pendingClause_of_firstPendingClause?_some (ρ := ρ) (F := F) (C := C) hselC
                  rcases pending_clause_has_pending_lit (ρ := ρ) (C := C) hpendC with ⟨ℓ, hℓ, hpendℓ⟩
                  have hnone' :
                      C.lits.find?
                        (fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending)) = none := by
                    simpa [firstPendingLit?] using hselLit
                  have hpred :=
                    find?_eq_none_forall
                      (p := fun ℓ => decide (atomLitStatus (ρ := ρ) ℓ = AtomLitStatus.pending))
                      (xs := C.lits) hnone' ℓ hℓ
                  have hnot : atomLitStatus (ρ := ρ) ℓ ≠ AtomLitStatus.pending := by
                    have hpred' := hpred
                    simp at hpred'
                    exact hpred'
                  exact (hnot hpendℓ).elim
              | some ℓ =>
                  cases hvar : ℓ.atom.nextVar ρ with
                  | none =>
                      exfalso
                      have hpendℓ := pendingLit_of_firstPendingLit?_some (ρ := ρ) (C := C) (ℓ := ℓ) hselLit
                      have hdec : AtomLit.decide ℓ ρ = none :=
                        decide_none_of_atomLitStatus_pending (ρ := ρ) (ℓ := ℓ) hpendℓ
                      rcases AtomLit.nextVar_of_undecided (ℓ := ℓ) (ρ := ρ) hdec with ⟨i, hi⟩
                      exact (Option.noConfusion (Eq.trans hvar.symm hi))
                  | some i =>
                      have hfree : ρ.mask i = none := ℓ.atom.nextVar_free (ρ := ρ) (i := i) hvar
                      have hmem : i ∈ ρ.freeIndicesList :=
                        (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hfree
                      let ρ0 := (ρ.assign i false).getD ρ
                      let ρ1 := (ρ.assign i true).getD ρ
                      have hdepth' :
                          Nat.max
                            (PDT.depth (commonCCDT_Family_atom (Fs := Fs) fuel ρ0))
                            (PDT.depth (commonCCDT_Family_atom (Fs := Fs) fuel ρ1))
                          < fuel := by
                        have hdepth_node :
                            Nat.succ
                              (Nat.max
                                (PDT.depth (commonCCDT_Family_atom (Fs := Fs) fuel ρ0))
                                (PDT.depth (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)))
                              < Nat.succ fuel := by
                          simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar,
                            ρ0, ρ1, PDT.depth] using hdepth
                        exact (Nat.succ_lt_succ_iff).1 hdepth_node
                      have hdepth_left :
                          PDT.depth (commonCCDT_Family_atom (Fs := Fs) fuel ρ0) < fuel := by
                        exact lt_of_le_of_lt (Nat.le_max_left _ _) hdepth'
                      have hdepth_right :
                          PDT.depth (commonCCDT_Family_atom (Fs := Fs) fuel ρ1) < fuel := by
                        exact lt_of_le_of_lt (Nat.le_max_right _ _) hdepth'
                      have hβ' :
                          β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0) ∨
                          β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1) := by
                        have : β ∈
                            PDT.leaves
                              (PDT.node i
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                          simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar,
                            ρ0, ρ1] using hβ
                        have hmem :
                            β ∈
                              (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)) ++
                                (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                          simpa [PDT.leaves] using this
                        exact List.mem_append.mp hmem
                      cases hβ' with
                      | inl hβ0 =>
                          exact leaf_decidesFamily_of_depth_lt_atom
                            (Fs := Fs) fuel ρ0 β hβ0 hdepth_left
                      | inr hβ1 =>
                          exact leaf_decidesFamily_of_depth_lt_atom
                            (Fs := Fs) fuel ρ1 β hβ1 hdepth_right

/-!
  Leaf refinement and compatibility for common‑CCDT on atom families.
-/

lemma subcubeRefines_of_assign_some
    {n : Nat} {ρ ρ' : Restriction n} {i : Fin n} {b : Bool}
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
        simp [hfree] at hmask
      have hmask' :=
        Restriction.assign_mask_eq (ρ := ρ) (ρ' := ρ') (i := i) (b := b) hassign j
      simp [hmask, hne] at hmask'
      simpa [hmask] using hmask'

lemma commonCCDT_leaves_refine_root_atom
    {n : Nat} (Fs : List (FuncCNF n)) :
    ∀ t (ρ : Restriction n) (β : Subcube n),
      β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) t ρ) →
      subcubeRefines β ρ.mask
  | 0, ρ, β, hβ => by
      rcases List.mem_singleton.mp (by
        simpa [commonCCDT_Family_atom, PDT.leaves] using hβ) with rfl
      exact subcubeRefines_refl (β := ρ.mask)
  | Nat.succ fuel, ρ, β, hβ => by
      classical
      cases hsel : firstPendingFormula_atom? (ρ := ρ) Fs with
      | none =>
          rcases List.mem_singleton.mp (by
            simpa [commonCCDT_Family_atom, hsel, PDT.leaves] using hβ) with rfl
          exact subcubeRefines_refl (β := ρ.mask)
      | some F =>
          cases hselC : firstPendingClause? (ρ := ρ) F with
          | none =>
              rcases List.mem_singleton.mp (by
                simpa [commonCCDT_Family_atom, hsel, hselC, PDT.leaves] using hβ) with rfl
              exact subcubeRefines_refl (β := ρ.mask)
          | some C =>
              cases hselLit : firstPendingLit? (ρ := ρ) C with
              | none =>
                  rcases List.mem_singleton.mp (by
                    simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, PDT.leaves] using hβ) with rfl
                  exact subcubeRefines_refl (β := ρ.mask)
              | some ℓ =>
                  cases hvar : ℓ.atom.nextVar ρ with
                  | none =>
                      have hβ' : β = ρ.mask := by
                        have hβ'' : β ∈ PDT.leaves (PDT.leaf ρ.mask) := by
                          simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar] using hβ
                        simpa [PDT.leaves] using hβ''
                      subst hβ'
                      exact subcubeRefines_refl (β := ρ.mask)
                  | some i =>
                      have hfree : ρ.mask i = none := ℓ.atom.nextVar_free (ρ := ρ) (i := i) hvar
                      have hmem : i ∈ ρ.freeIndicesList :=
                        (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hfree
                      let ρ0 := (ρ.assign i false).getD ρ
                      let ρ1 := (ρ.assign i true).getD ρ
                      have hassign0 : ρ.assign i false = some ρ0 := by
                        rcases assign_getD_eq_of_mem_freeIndicesList
                          (ρ := ρ) (i := i) (b := false) hmem with ⟨ρ0', hassign0', hget0⟩
                        have hρ0 : ρ0 = ρ0' := by
                          simpa [ρ0] using hget0
                        simpa [hρ0] using hassign0'
                      have hassign1 : ρ.assign i true = some ρ1 := by
                        rcases assign_getD_eq_of_mem_freeIndicesList
                          (ρ := ρ) (i := i) (b := true) hmem with ⟨ρ1', hassign1', hget1⟩
                        have hρ1 : ρ1 = ρ1' := by
                          simpa [ρ1] using hget1
                        simpa [hρ1] using hassign1'
                      have hβ' :
                          β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0) ∨
                          β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1) := by
                        have : β ∈
                            PDT.leaves
                              (PDT.node i
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                          have hβ' := hβ
                          simp [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar] at hβ'
                          exact hβ'
                        have hmem' :
                            β ∈
                              (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)) ++
                                (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                          simpa [PDT.leaves] using this
                        exact List.mem_append.mp hmem'
                      have href0 : subcubeRefines ρ0.mask ρ.mask :=
                        subcubeRefines_of_assign_some (hassign := hassign0) (hfree := hfree)
                      have href1 : subcubeRefines ρ1.mask ρ.mask :=
                        subcubeRefines_of_assign_some (hassign := hassign1) (hfree := hfree)
                      cases hβ' with
                      | inl hβ0 =>
                          exact subcubeRefines_trans
                            (commonCCDT_leaves_refine_root_atom (Fs := Fs) fuel ρ0 β hβ0) href0
                      | inr hβ1 =>
                          exact subcubeRefines_trans
                            (commonCCDT_leaves_refine_root_atom (Fs := Fs) fuel ρ1 β hβ1) href1

lemma mem_of_assign_some_of_mem
    {n : Nat} {ρ ρ' : Restriction n} {i : Fin n} {b : Bool} {x : Core.BitVec n}
    (hassign : ρ.assign i b = some ρ')
    (hmem : mem ρ.mask x)
    (hxi : x i = b) :
    mem ρ'.mask x := by
  apply (mem_iff (β := ρ'.mask) (x := x)).2
  intro j b' hmask'
  have hmask := Restriction.assign_mask_eq
    (ρ := ρ) (ρ' := ρ') (i := i) (b := b) hassign j
  by_cases hji : j = i
  · cases hji
    have hmask_eq : ρ'.mask i = some b := by
      simpa using hmask
    have hb' : b' = b := by
      have hmask_eq' : ρ'.mask i = some b' := by
        simpa using hmask'
      have : some b' = some b := by
        simpa [hmask_eq'] using hmask_eq
      exact Option.some.inj this
    simp [hb', hxi]
  · have hmask'' : ρ.mask j = some b' := by
      have : ρ'.mask j = ρ.mask j := by
        simpa [hji] using hmask
      simpa [this] using hmask'
    have hmem' := (mem_iff (β := ρ.mask) (x := x)).1 hmem j b' hmask''
    exact hmem'

lemma commonCCDT_leaf_of_compatible_atom
    {n : Nat} (Fs : List (FuncCNF n)) :
    ∀ t (ρ : Restriction n) (x : Core.BitVec n),
      ρ.compatible x = true →
      ∃ β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) t ρ), mem β x
  | 0, ρ, x, hcomp => by
      have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
      refine ⟨ρ.mask, ?_, hmem⟩
      simp [commonCCDT_Family_atom, PDT.leaves]
  | Nat.succ fuel, ρ, x, hcomp => by
      classical
      cases hsel : firstPendingFormula_atom? (ρ := ρ) Fs with
      | none =>
          have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
          refine ⟨ρ.mask, ?_, hmem⟩
          simp [commonCCDT_Family_atom, hsel, PDT.leaves]
      | some F =>
          cases hselC : firstPendingClause? (ρ := ρ) F with
          | none =>
              have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
              refine ⟨ρ.mask, ?_, hmem⟩
              simp [commonCCDT_Family_atom, hsel, hselC, PDT.leaves]
          | some C =>
              cases hselLit : firstPendingLit? (ρ := ρ) C with
              | none =>
                  have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
                  refine ⟨ρ.mask, ?_, hmem⟩
                  simp [commonCCDT_Family_atom, hsel, hselC, hselLit, PDT.leaves]
              | some ℓ =>
                  cases hvar : ℓ.atom.nextVar ρ with
                  | none =>
                      have hmem : mem ρ.mask x := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp
                      refine ⟨ρ.mask, ?_, hmem⟩
                      have hmem' : ρ.mask ∈ PDT.leaves (PDT.leaf ρ.mask) := by
                        simp [PDT.leaves]
                      simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar] using hmem'
                  | some i =>
                      have hfree : ρ.mask i = none := ℓ.atom.nextVar_free (ρ := ρ) (i := i) hvar
                      have hmemi : i ∈ ρ.freeIndicesList :=
                        (Restriction.mem_freeIndicesList (ρ := ρ) (i := i)).2 hfree
                      let ρ0 := (ρ.assign i false).getD ρ
                      let ρ1 := (ρ.assign i true).getD ρ
                      have hassign0 : ρ.assign i false = some ρ0 := by
                        rcases assign_getD_eq_of_mem_freeIndicesList
                          (ρ := ρ) (i := i) (b := false) hmemi with ⟨ρ0', hassign0', hget0⟩
                        have hρ0 : ρ0 = ρ0' := by
                          simpa [ρ0] using hget0
                        simpa [hρ0] using hassign0'
                      have hassign1 : ρ.assign i true = some ρ1 := by
                        rcases assign_getD_eq_of_mem_freeIndicesList
                          (ρ := ρ) (i := i) (b := true) hmemi with ⟨ρ1', hassign1', hget1⟩
                        have hρ1 : ρ1 = ρ1' := by
                          simpa [ρ1] using hget1
                        simpa [hρ1] using hassign1'
                      by_cases hx : x i = true
                      · have hmem1 : mem ρ1.mask x := by
                          exact mem_of_assign_some_of_mem
                            (hassign := hassign1)
                            (hmem := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp)
                            (hxi := hx)
                        have hcomp1 : ρ1.compatible x = true :=
                          (Restriction.compatible_iff (ρ := ρ1) (x := x)).2 hmem1
                        rcases commonCCDT_leaf_of_compatible_atom (Fs := Fs) fuel ρ1 x hcomp1 with
                          ⟨β, hβ, hmemβ⟩
                        refine ⟨β, ?_, hmemβ⟩
                        have : β ∈
                            PDT.leaves
                              (PDT.node i
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                          have hmem' : β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1) := hβ
                          have : β ∈
                              (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)) ++
                                (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                            exact List.mem_append.mpr (Or.inr hmem')
                          simpa [PDT.leaves] using this
                        simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar,
                          ρ0, ρ1] using this
                      · have hxi : x i = false := by
                          cases h' : x i with
                          | true =>
                              have : False := hx h'
                              exact (False.elim this)
                          | false =>
                              simp
                        have hmem0 : mem ρ0.mask x := by
                          exact mem_of_assign_some_of_mem
                            (hassign := hassign0)
                            (hmem := (Restriction.compatible_iff (ρ := ρ) (x := x)).1 hcomp)
                            (hxi := hxi)
                        have hcomp0 : ρ0.compatible x = true :=
                          (Restriction.compatible_iff (ρ := ρ0) (x := x)).2 hmem0
                        rcases commonCCDT_leaf_of_compatible_atom (Fs := Fs) fuel ρ0 x hcomp0 with
                          ⟨β, hβ, hmemβ⟩
                        refine ⟨β, ?_, hmemβ⟩
                        have : β ∈
                            PDT.leaves
                              (PDT.node i
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)
                                (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                          have hmem' : β ∈ PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0) := hβ
                          have : β ∈
                              (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ0)) ++
                                (PDT.leaves (commonCCDT_Family_atom (Fs := Fs) fuel ρ1)) := by
                            exact List.mem_append.mpr (Or.inl hmem')
                          simpa [PDT.leaves] using this
                        simpa [commonCCDT_Family_atom, hsel, hselC, hselLit, hvar,
                          ρ0, ρ1] using this

end MultiSwitching
end AC0
end Pnp3
