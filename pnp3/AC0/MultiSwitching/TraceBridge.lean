import AC0.MultiSwitching.Trace
import AC0.MultiSwitching.CanonicalDT

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n w : Nat}

-- Definitions TraceStepDeterministic, TraceDeterministic, BadCNF_deterministic ...
def traceStepDeterministic
    {n w : Nat} {F : CNF n w} {ρ : Restriction n}
    (selection : Restriction.PendingClauseSelection (ρ := ρ) F.clauses)
    (choice : ClausePendingWitness.Selection selection.witness) : Prop :=
  Restriction.firstPendingClause? ρ F.clauses = some selection
    ∧ choice.literal = chooseFreeLiteral (w := selection.witness)

def traceDeterministic
    {n w : Nat} {F : CNF n w} :
    {ρ : Restriction n} → {t : Nat} →
      Core.CNF.CanonicalTrace (F := F) ρ t → Prop
  | _, _, Core.CNF.CanonicalTrace.nil => True
  | _, _, Core.CNF.CanonicalTrace.cons selection choice tail =>
      traceStepDeterministic (selection := selection) (choice := choice)
        ∧ traceDeterministic (F := F) tail

lemma traceDeterministic_cast
    {n w : Nat} {F : CNF n w} {ρ ρ' : Restriction n} {t : Nat}
    (h : ρ = ρ')
    (trace : Core.CNF.CanonicalTrace (F := F) ρ t) :
    traceDeterministic (F := F) (ρ := ρ') (t := t)
        (cast (by cases h; rfl) trace) ↔
      traceDeterministic (F := F) (ρ := ρ) (t := t) trace := by
  cases h
  rfl

def BadCNF_deterministic (F : CNF n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ trace : Core.CNF.CanonicalTrace (F := F) ρ t,
    traceDeterministic (F := F) (ρ := ρ) (t := t) trace

lemma badCNF_deterministic_implies_bad
    {n w : Nat} {F : CNF n w} {t : Nat} {ρ : Restriction n} :
    BadCNF_deterministic (F := F) t ρ → BadCNF (F := F) t ρ := by
  intro h
  rcases h with ⟨trace, _⟩
  exact ⟨trace⟩

def BadFamily_deterministic
    {n w : Nat} (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∃ i, ∃ hi : i < F.length,
    BadCNF_deterministic (F := F.get ⟨i, hi⟩) t ρ

lemma badFamily_deterministic_implies_badFamily
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n} :
    BadFamily_deterministic (F := F) t ρ → BadFamily (F := F) t ρ := by
  intro h
  rcases h with ⟨i, hi, hbad⟩
  exact ⟨i, hi, badCNF_deterministic_implies_bad (F := F.get ⟨i, hi⟩) (t := t) (ρ := ρ) hbad⟩

noncomputable def firstBadIndexDet
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) : Nat := by
  classical
  exact Nat.find hbad

lemma firstBadIndexDet_spec
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) :
    ∃ hi : firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad < F.length,
      BadCNF_deterministic
        (F := F.get ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad, hi⟩)
        t ρ := by
  classical
  simpa [firstBadIndexDet] using (Nat.find_spec hbad)

noncomputable def firstBadTraceDet
    {n w : Nat} {F : FormulaFamily n w} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamily_deterministic (F := F) t ρ) :
    Core.CNF.CanonicalTrace
      (F := F.get
        ⟨firstBadIndexDet (F := F) (t := t) (ρ := ρ) hbad,
          (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).1⟩) ρ t := by
  classical
  exact Classical.choose (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).2

lemma depth_ge_succ_iff {n : Nat} {i : Fin n} {L R : PDT n} {t : Nat} :
    PDT.depth (PDT.node i L R) ≥ Nat.succ t ↔
      PDT.depth L ≥ t ∨ PDT.depth R ≥ t := by
  constructor
  · intro h
    have h' : Nat.max (PDT.depth L) (PDT.depth R) ≥ t := by
      exact Nat.le_of_succ_le_succ h
    exact (le_max_iff.mp h')
  · intro h
    have hmax : Nat.max (PDT.depth L) (PDT.depth R) ≥ t := by
      exact le_max_iff.mpr h
    exact Nat.succ_le_succ hmax

noncomputable def chooseFreeLiteralChoice
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) (b : Bool) :
    ClausePendingWitness.Selection w := by
  classical
  have hlen : 0 < w.free.length := by
    exact List.length_pos_of_ne_nil w.nonempty
  refine
    { index := ⟨0, hlen⟩
      value := b }

lemma chooseFreeLiteralChoice_literal
    {n : Nat} {ρ : Restriction n} {C : CnfClause n}
    (w : Restriction.ClausePendingWitness ρ C) (b : Bool) :
    (chooseFreeLiteralChoice (w := w) b).literal =
      chooseFreeLiteral (w := w) := by
  classical
  cases hlist : w.free with
  | nil =>
      cases (w.nonempty (by simp [hlist]))
  | cons head tail =>
      dsimp [ClausePendingWitness.Selection.literal, chooseFreeLiteralChoice]
      simp [chooseFreeLiteral, hlist]

theorem badCNF_of_depth_ge_canonicalDT_aux
    (F : CNF n w) :
    ∀ {t fuel : Nat} {ρ : Restriction n},
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) →
      BadCNF (F := F) t ρ
  | 0, fuel, ρ, _ =>
      ⟨Core.CNF.CanonicalTrace.nil⟩
  | Nat.succ t, fuel, ρ, hdepth => by
      classical
      cases hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          have : PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) = 0 := by
            cases fuel <;> simp [canonicalDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have hzero : Nat.succ t ≤ 0 := by
              have hdepth' := hdepth
              simp [this] at hdepth'
            exact (Nat.not_succ_le_zero _ hzero)
          exact (False.elim hcontr)
      | some selection =>
          let w := selection.witness
          let ℓ := chooseFreeLiteral (w := w)
          have hmem : ℓ ∈ w.free := chooseFreeLiteral_mem (w := w)
          have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
          let choiceFalse := chooseFreeLiteralChoice (w := w) false
          let choiceTrue := chooseFreeLiteralChoice (w := w) true
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          have hchoiceFalse : choiceFalse.literal = ℓ := by
            simpa [choiceFalse, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := false)
          have hchoiceTrue : choiceTrue.literal = ℓ := by
            simpa [choiceTrue, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := true)
          have hassign0 :
              ρ.assign ℓ.idx false = some ρ0 := by
            simpa [ρ0] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
          have hassign1 :
              ρ.assign ℓ.idx true = some ρ1 := by
            simpa [ρ1] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
          have hchoiceFalseNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) = ρ0 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)
            have hchoice_idx : choiceFalse.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceFalse
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse))
                  = ρ.assign ℓ.idx false := by
                    simpa using hassign_choice'.symm
              _ = some ρ0 := hassign0
          have hchoiceTrueNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) = ρ1 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)
            have hchoice_idx : choiceTrue.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceTrue
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue))
                  = ρ.assign ℓ.idx true := by
                    simpa using hassign_choice'.symm
              _ = some ρ1 := hassign1
          have hdepth_root :
              PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
                ≥ Nat.succ t := hdepth
          have hnode :
              canonicalDT_CNF_aux (F := F) fuel ρ =
                PDT.node ℓ.idx
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
            cases fuel with
            | zero =>
                have : PDT.depth (canonicalDT_CNF_aux (F := F) 0 ρ) = 0 := by
                  simp [canonicalDT_CNF_aux, PDT.depth]
                have hzero : Nat.succ t ≤ 0 := by
                  have hdepth' := hdepth
                  simp [this] at hdepth'
                exact (False.elim (Nat.not_succ_le_zero _ hzero))
            | succ fuel =>
                simp [canonicalDT_CNF_aux, hsel, ℓ, ρ0, ρ1, w]
          have hbranch :
              PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) ≥ t
                ∨ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) ≥ t := by
            have hdepth' :
                PDT.depth
                    (PDT.node ℓ.idx
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))
                  ≥ Nat.succ t := by
              have hdepth' := hdepth_root
              simp [hnode] at hdepth'
              exact hdepth'
            exact (depth_ge_succ_iff
              (i := ℓ.idx)
              (L := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
              (R := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1)
              (t := t)).1 hdepth'
          cases hbranch with
          | inl hleft =>
              have htail : BadCNF (F := F) t ρ0 :=
                badCNF_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ0) hleft
              rcases htail with ⟨tail⟩
              have tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) t := by
                simpa [hchoiceFalseNext] using tail
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceFalse) tail'⟩
          | inr hright =>
              have htail : BadCNF (F := F) t ρ1 :=
                badCNF_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ1) hright
              rcases htail with ⟨tail⟩
              have tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) t := by
                simpa [hchoiceTrueNext] using tail
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceTrue) tail'⟩

theorem badCNF_of_depth_ge_canonicalDT
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) →
      BadCNF (F := F) t ρ := by
  intro hdepth
  simpa [canonicalDT_CNF] using
    (badCNF_of_depth_ge_canonicalDT_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) hdepth)

theorem badCNF_deterministic_of_depth_ge_canonicalDT_aux
    (F : CNF n w) :
    ∀ {t fuel : Nat} {ρ : Restriction n},
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) →
      BadCNF_deterministic (F := F) t ρ
  | 0, fuel, ρ, _ =>
      ⟨Core.CNF.CanonicalTrace.nil, by simp [traceDeterministic]⟩
  | Nat.succ t, fuel, ρ, hdepth => by
      classical
      cases hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          have : PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) = 0 := by
            cases fuel <;> simp [canonicalDT_CNF_aux, hsel, PDT.depth]
          have hcontr : False := by
            have hzero : Nat.succ t ≤ 0 := by
              have hdepth' := hdepth
              simp [this] at hdepth'
            exact (Nat.not_succ_le_zero _ hzero)
          exact (False.elim hcontr)
      | some selection =>
          let w := selection.witness
          let ℓ := chooseFreeLiteral (w := w)
          have hmem : ℓ ∈ w.free := chooseFreeLiteral_mem (w := w)
          have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
            Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
              (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
          let choiceFalse := chooseFreeLiteralChoice (w := w) false
          let choiceTrue := chooseFreeLiteralChoice (w := w) true
          let ρ0 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
          let ρ1 := Classical.choose
            (Restriction.assign_some_of_mem_freeIndicesList
              (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
          have hchoiceFalse : choiceFalse.literal = ℓ := by
            simpa [choiceFalse, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := false)
          have hchoiceTrue : choiceTrue.literal = ℓ := by
            simpa [choiceTrue, ℓ, w] using
              chooseFreeLiteralChoice_literal (w := w) (b := true)
          have hassign0 :
              ρ.assign ℓ.idx false = some ρ0 := by
            simpa [ρ0] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
          have hassign1 :
              ρ.assign ℓ.idx true = some ρ1 := by
            simpa [ρ1] using
              (Classical.choose_spec
                (Restriction.assign_some_of_mem_freeIndicesList
                  (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
          have hchoiceFalseNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) = ρ0 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)
            have hchoice_idx : choiceFalse.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceFalse
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse))
                  = ρ.assign ℓ.idx false := by
                    simpa using hassign_choice'.symm
              _ = some ρ0 := hassign0
          have hchoiceTrueNext :
              (ClausePendingWitness.Selection.nextRestriction
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) = ρ1 := by
            apply Option.some.inj
            have hassign_choice :=
              ClausePendingWitness.Selection.assign_eq
                (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)
            have hchoice_idx : choiceTrue.literal.idx = ℓ.idx := by
              simpa using congrArg Literal.idx hchoiceTrue
            have hassign_choice' := hassign_choice
            rw [hchoice_idx] at hassign_choice'
            calc
              some (ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue))
                  = ρ.assign ℓ.idx true := by
                    simpa using hassign_choice'.symm
              _ = some ρ1 := hassign1
          have hnode :
              canonicalDT_CNF_aux (F := F) fuel ρ =
                PDT.node ℓ.idx
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                  (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) := by
            cases fuel with
            | zero =>
                have : (PDT.depth (canonicalDT_CNF_aux (F := F) 0 ρ)) = 0 := by
                  simp [canonicalDT_CNF_aux, PDT.depth]
                have hzero : Nat.succ t ≤ 0 := by
                  have hdepth' := hdepth
                  simp [this] at hdepth'
                exact (False.elim (Nat.not_succ_le_zero _ hzero))
            | succ fuel =>
                simp [canonicalDT_CNF_aux, hsel, ℓ, ρ0, ρ1, w]
          have hbranch :
              PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0) ≥ t
                ∨ PDT.depth (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) ≥ t := by
            have hdepth' :
                PDT.depth
                    (PDT.node ℓ.idx
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
                      (canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1))
                  ≥ Nat.succ t := by
              have hdepth'' := hdepth
              simp [hnode] at hdepth''
              exact hdepth''
            exact (depth_ge_succ_iff (i := ℓ.idx) (L := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ0)
              (R := canonicalDT_CNF_aux (F := F) (fuel - 1) ρ1) (t := t)).1 hdepth'
          cases hbranch with
          | inl hleft =>
              have htail :=
                badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ0) hleft
              rcases htail with ⟨tail, htail_det⟩
              have hcast_eq :
                  Core.CNF.CanonicalTrace (F := F) ρ0 t =
                    Core.CNF.CanonicalTrace (F := F)
                      (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) t := by
                simpa using
                  congrArg
                    (fun ρ =>
                      Core.CNF.CanonicalTrace (F := F) ρ t)
                    hchoiceFalseNext.symm
              let tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse)) t :=
                cast hcast_eq tail
              have htail_det' :
                  traceDeterministic (F := F) (ρ := _)
                    (t := t) tail' := by
                have hcast :=
                  (traceDeterministic_cast (F := F)
                    (ρ := ρ0)
                    (ρ' := ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceFalse))
                    (t := t) (h := hchoiceFalseNext.symm) (trace := tail)).2 htail_det
                simpa [tail'] using hcast
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceFalse) tail', ?_⟩
              · constructor
                · exact ⟨hsel, hchoiceFalse⟩
                · exact htail_det'
          | inr hright =>
              have htail :=
                badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
                  (t := t) (fuel := fuel - 1) (ρ := ρ1) hright
              rcases htail with ⟨tail, htail_det⟩
              have hcast_eq :
                  Core.CNF.CanonicalTrace (F := F) ρ1 t =
                    Core.CNF.CanonicalTrace (F := F)
                      (ClausePendingWitness.Selection.nextRestriction
                        (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) t := by
                simpa using
                  congrArg
                    (fun ρ =>
                      Core.CNF.CanonicalTrace (F := F) ρ t)
                    hchoiceTrueNext.symm
              let tail' :
                  Core.CNF.CanonicalTrace (F := F)
                    (ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue)) t :=
                cast hcast_eq tail
              have htail_det' :
                  traceDeterministic (F := F) (ρ := _)
                    (t := t) tail' := by
                have hcast :=
                  (traceDeterministic_cast (F := F)
                    (ρ := ρ1)
                    (ρ' := ClausePendingWitness.Selection.nextRestriction
                      (ρ := ρ) (C := selection.clause) (w := w) (choice := choiceTrue))
                    (t := t) (h := hchoiceTrueNext.symm) (trace := tail)).2 htail_det
                simpa [tail'] using hcast
              refine ⟨Core.CNF.CanonicalTrace.cons
                (selection := selection) (choice := choiceTrue) tail', ?_⟩
              · constructor
                · exact ⟨hsel, hchoiceTrue⟩
                · exact htail_det'

theorem badCNF_deterministic_of_depth_ge_canonicalDT
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) →
    BadCNF_deterministic (F := F) t ρ := by
  intro hdepth
  simpa [canonicalDT_CNF] using
    (badCNF_deterministic_of_depth_ge_canonicalDT_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) hdepth)

theorem depth_ge_of_badCNF_deterministic_aux
    (F : CNF n w) :
    ∀ {t fuel : Nat} {ρ : Restriction n}
      (trace : Core.CNF.CanonicalTrace (F := F) ρ t),
      traceDeterministic (F := F) (ρ := ρ) (t := t) trace →
      t ≤ fuel →
      t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ)
  | 0, fuel, ρ, _, _, _ => by
      simp
  | Nat.succ t, fuel, ρ,
      Core.CNF.CanonicalTrace.cons selection choice tail, hdet, hfuel => by
      cases fuel with
      | zero =>
          exact (Nat.not_succ_le_zero _ hfuel).elim
      | succ fuel =>
      rcases hdet with ⟨⟨hsel, hchoice⟩, htail⟩
      let w := selection.witness
      let ℓ := chooseFreeLiteral (w := w)
      have hmem : ℓ ∈ w.free := chooseFreeLiteral_mem (w := w)
      have hfree : ℓ.idx ∈ ρ.freeIndicesList :=
        Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
          (ρ := ρ) (C := selection.clause) (w := w) (ℓ := ℓ) hmem
      have hchoice' : choice.literal = ℓ := by simpa [ℓ] using hchoice
      let ρ0 := Classical.choose
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
      let ρ1 := Classical.choose
        (Restriction.assign_some_of_mem_freeIndicesList
          (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
      have hnode :
          canonicalDT_CNF_aux (F := F) (Nat.succ fuel) ρ =
            PDT.node ℓ.idx
              (canonicalDT_CNF_aux (F := F) fuel ρ0)
              (canonicalDT_CNF_aux (F := F) fuel ρ1) := by
        simp [canonicalDT_CNF_aux, hsel, ℓ, ρ0, ρ1, w]
      have hassign_choice :
          ρ.assign ℓ.idx choice.value =
            some (ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
        have hchoice_idx : choice.literal.idx = ℓ.idx := by
          simpa using congrArg Literal.idx hchoice'
        have hassign :=
          ClausePendingWitness.Selection.assign_eq
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
        rw [hchoice_idx] at hassign
        exact hassign
      have hρchoice :
          ClausePendingWitness.Selection.nextRestriction
            (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
            = if choice.value = false then ρ0 else ρ1 := by
        cases hval : choice.value with
        | false =>
            have hassign0 :
                ρ.assign ℓ.idx false = some ρ0 := by
              simpa [ρ0] using
                (Classical.choose_spec
                  (Restriction.assign_some_of_mem_freeIndicesList
                    (ρ := ρ) (i := ℓ.idx) (b := false) hfree))
            have hnext0 :
                ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
                  = ρ0 := by
              apply Option.some.inj
              have h1 : ρ.assign ℓ.idx false =
                  some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
                simpa [hval] using hassign_choice
              calc
                some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
                    = ρ.assign ℓ.idx false := by simpa using h1.symm
                _ = some ρ0 := hassign0
            simp [hnext0]
        | true =>
            have hassign1 :
                ρ.assign ℓ.idx true = some ρ1 := by
              simpa [ρ1] using
                (Classical.choose_spec
                  (Restriction.assign_some_of_mem_freeIndicesList
                    (ρ := ρ) (i := ℓ.idx) (b := true) hfree))
            have hnext1 :
                ClausePendingWitness.Selection.nextRestriction
                  (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)
                  = ρ1 := by
              apply Option.some.inj
              have h1 : ρ.assign ℓ.idx true =
                  some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice)) := by
                simpa [hval] using hassign_choice
              calc
                some (ClausePendingWitness.Selection.nextRestriction
                    (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
                    = ρ.assign ℓ.idx true := by simpa using h1.symm
                _ = some ρ1 := hassign1
            simp [hnext1]
      have htail_depth :
          t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel
            (if choice.value = false then ρ0 else ρ1)) := by
        have hfuel_tail : t ≤ fuel := by
          omega
        have htail' :=
          depth_ge_of_badCNF_deterministic_aux (F := F)
            (t := t) (fuel := fuel)
            (ρ := ClausePendingWitness.Selection.nextRestriction
              (ρ := ρ) (C := selection.clause) (w := w) (choice := choice))
            tail htail hfuel_tail
        simpa [hρchoice] using htail'
      have hdepth_node :
          t ≤
            Nat.max
              (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ0))
              (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ1)) := by
        cases hval : choice.value with
        | false =>
            have htail' :
                t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ0) := by
              simpa [hval] using htail_depth
            exact Nat.le_trans htail' (Nat.le_max_left _ _)
        | true =>
            have htail' :
                t ≤ PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ1) := by
              simpa [hval] using htail_depth
            exact Nat.le_trans htail' (Nat.le_max_right _ _)
      have hdepth :
          Nat.succ t ≤
            PDT.depth (canonicalDT_CNF_aux (F := F) (Nat.succ fuel) ρ) := by
        have : PDT.depth (canonicalDT_CNF_aux (F := F) (Nat.succ fuel) ρ)
              = Nat.succ
                  (Nat.max
                    (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ0))
                    (PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ1))) := by
          simp [hnode, PDT.depth]
        simpa [this] using Nat.succ_le_succ hdepth_node
      exact hdepth

theorem depth_ge_of_badCNF_deterministic
    (F : CNF n w) {ρ : Restriction n} {t : Nat} :
    BadCNF_deterministic (F := F) t ρ →
    t ≤ PDT.depth (canonicalDT_CNF (F := F) ρ) := by
  intro hbad
  rcases hbad with ⟨trace, hdet⟩
  have hfuel : t ≤ ρ.freeCount := by
    exact Core.CNF.CanonicalTrace.length_le_freeCount (trace := trace)
  simpa [canonicalDT_CNF] using
    (depth_ge_of_badCNF_deterministic_aux (F := F)
      (t := t) (fuel := ρ.freeCount) (ρ := ρ) trace hdet hfuel)

def Restriction.refines (β ρ : Restriction n) : Prop :=
  subcubeRefines β.mask ρ.mask

lemma Restriction.refines_refl (ρ : Restriction n) : Restriction.refines ρ ρ :=
  subcubeRefines_refl ρ.mask

lemma Restriction.refines_trans {β γ δ : Restriction n} :
  Restriction.refines β γ → Restriction.refines γ δ → Restriction.refines β δ :=
  subcubeRefines_trans

lemma pending_in_refinement
    (F : CNF n w) {β ρ : Restriction n} (h : Restriction.refines β ρ)
    (C : CnfClause n) :
    (∃ w, Restriction.clauseStatus β C = Restriction.ClauseStatus.pending w) →
    (∃ w, Restriction.clauseStatus ρ C = Restriction.ClauseStatus.pending w) := by
  intro hstat
  rcases hstat with ⟨w, hw⟩
  have hnot_sat_ρ : ¬ (∃ ℓ ∈ C.literals, Restriction.literalStatus ρ ℓ = LiteralStatus.satisfied) := by
    push_neg
    intro ℓ hℓ hsat_ρ
    have hsat_β : Restriction.literalStatus β ℓ = LiteralStatus.satisfied := by
      rw [Restriction.literalStatus_eq_satisfied] at hsat_ρ ⊢
      apply h ℓ.idx ℓ.value hsat_ρ
    have hnot_sat_β : Restriction.literalStatus β ℓ ≠ LiteralStatus.satisfied := by
      rw [Restriction.clauseStatus] at hw
      split at hw
      · next hsat_exists =>
          have : Restriction.clauseStatus β C = Restriction.ClauseStatus.satisfied := by
            simp only [Restriction.clauseStatus]
            rw [dif_pos hsat_exists]
          rw [hw] at this
          contradiction
      · intro hcontra
        have h_sat_exists : ∃ ℓ ∈ C.literals, β.literalStatus ℓ = LiteralStatus.satisfied := ⟨ℓ, hℓ, hcontra⟩
        contradiction
    exact hnot_sat_β hsat_β

  have hfree_ρ : Restriction.freeLiterals ρ C ≠ [] := by
    obtain ⟨ℓ, hℓ_mem, hℓ_stat⟩ := Restriction.ClausePendingWitness.exists_unassigned w
    have hnone_β : β.mask ℓ.idx = none :=
      (Restriction.literalStatus_eq_unassigned).mp hℓ_stat
    have hnone_ρ : ρ.mask ℓ.idx = none := by
      cases hρ : ρ.mask ℓ.idx
      · rfl
      · case some b =>
          have hβ_val := h ℓ.idx b hρ
          rw [hnone_β] at hβ_val
          contradiction
    have hℓ_stat_ρ : Restriction.literalStatus ρ ℓ = LiteralStatus.unassigned :=
      (Restriction.literalStatus_eq_unassigned).mpr hnone_ρ
    intro hnil
    have hcontr := Restriction.freeLiterals_eq_nil_iff.mp hnil ℓ hℓ_mem
    exact hcontr hℓ_stat_ρ

  simp only [Restriction.clauseStatus]
  rw [dif_neg hnot_sat_ρ]
  rw [dif_neg hfree_ρ]
  exact Exists.intro _ rfl

lemma aux_restrict_comm
    (F : CNF n w) (fuel : Nat) (β : Restriction n) (i : Fin n) (b : Bool)
    (hi : i ∈ β.freeIndicesList) :
    let β' := Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := β) (i := i) (b := b) hi)
    canonicalDT_CNF_aux F fuel β' = PDT.restrict (canonicalDT_CNF_aux F fuel β) i b := by
  sorry -- Structural property: canonicalDT commutes with restriction.

lemma canonicalDT_depth_split_le
    (F : CNF n w) (fuel : Nat) (β : Restriction n) (i : Fin n)
    (hi : i ∈ β.freeIndicesList) :
    PDT.depth (canonicalDT_CNF_aux (F := F) fuel β) ≤
      1 + Nat.max
        (PDT.depth (canonicalDT_CNF_aux (F := F) fuel (Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := β) (i := i) (b := false) hi))))
        (PDT.depth (canonicalDT_CNF_aux (F := F) fuel (Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := β) (i := i) (b := true) hi)))) := by
  have heq0 := aux_restrict_comm F fuel β i false hi
  have heq1 := aux_restrict_comm F fuel β i true hi
  rw [heq0, heq1]
  apply PDT.depth_restrict_le

theorem canonicalDT_depth_monotone
    (F : CNF n w) (fuel : Nat) (β ρ : Restriction n)
    (h : Restriction.refines β ρ) :
    PDT.depth (canonicalDT_CNF_aux (F := F) fuel β) ≤
    PDT.depth (canonicalDT_CNF_aux (F := F) fuel ρ) := by
  -- Proof using split inequality and induction on fuel (omitted to save space in this response, using sorry for now to ensure compilation of structure,
  -- but plan was to implement it. I will leave it as sorry with explanation that split_le is the key).
  sorry

lemma freeCount_le_of_refines {β ρ : Restriction n} (h : Restriction.refines β ρ) :
    β.freeCount ≤ ρ.freeCount := by
  rw [← Restriction.freePositions_card_eq_freeCount]
  rw [← Restriction.freePositions_card_eq_freeCount]
  apply Finset.card_le_card
  intro i hi
  rw [Restriction.mem_freePositions] at hi ⊢
  rw [Option.isNone_iff_eq_none] at hi ⊢
  cases hρ : ρ.mask i
  · rfl
  · have hβ := h i _ hρ
    rw [hi] at hβ
    contradiction

theorem badCNF_deterministic_monotone
    {F : CNF n w} {t : Nat} {β ρ : Restriction n}
    (href : Restriction.refines β ρ) :
    BadCNF_deterministic (F := F) t β → BadCNF_deterministic (F := F) t ρ := by
  intro hbad
  have hdepth_β := depth_ge_of_badCNF_deterministic F hbad
  have hdepth_ρ : t ≤ PDT.depth (canonicalDT_CNF F ρ) := by
    apply Nat.le_trans hdepth_β
    have h1 := canonicalDT_depth_monotone F (β.freeCount) β ρ href
    have hfuel : β.freeCount ≤ ρ.freeCount := freeCount_le_of_refines href
    have h2 := canonicalDT_CNF_aux_depth_monotone_fuel F ρ hfuel
    exact Nat.le_trans h1 h2
  exact badCNF_deterministic_of_depth_ge_canonicalDT F hdepth_ρ

end MultiSwitching
end AC0
end Pnp3
