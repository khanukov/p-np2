/-
  mistral_test/SourceTheorems/IsoStrongMain.lean
  
  Main proof: IsoStrongFamilyEventually for concreteFamily.
-/
import MistralTestLib.SourceTheorems.ForcingProperty
import MistralTestLib.SourceTheorems.ConcreteFamily
import MistralTestLib.SourceTheorems.CircuitBound
import Pnp3.LowerBounds.AsymptoticDAGBarrierTheorems

namespace MistralTestLib

open Pnp3.Models Pnp3.ComplexityInterfaces Pnp3.LowerBounds Pnp3.Core

/-!
## Parameters for IsoStrongFamilyEventually
-/

def iso_beta0 : Rat := 1

def iso_kappa (n : Nat) (β : Rat) : Nat := 
  (Partial.tableLen n) / 2

def iso_nIso (β : Rat) : Nat := 
  concreteFamily.N0

/-!
## Key lemma: Agreement on D implies agreement on all of support C
-/

lemma agree_on_D_implies_agree_on_support_C
    (p : GapPartialMCSPParams)
    (C : DagCircuit (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (yYes : Core.BitVec (partialInputLen p))
    (z : Core.BitVec (partialInputLen p))
    (hD_subset : D ⊆ ForcingProperty.support_on_table p C)
    (hAgree : AgreeOnValues D yYes z)
    (hyYes_val_all_true : ∀ j, Partial.valPart yYes j = true) :
    ∀ i ∈ DagCircuit.support C, z i = yYes i := by
  intro i hi
  let j := ForcingProperty.tableIndexOfInput p.n i
  have hj_in_D : j ∈ D := by
    have h_in_support : i ∈ DagCircuit.support C := hi
    have : ForcingProperty.tableIndexOfInput p.n i ∈ ForcingProperty.support_on_table p C :=
      ForcingProperty.tableIndex_in_support_on_table p C i hi
    have : j ∈ ForcingProperty.support_on_table p C := by simpa [j] using this
    exact hD_subset this
  have hyYes_mask_idx : yYes (Partial.maskIndex j) = true := by
    simp [Partial.maskIndex]
    have : Partial.valPart yYes j = true := hyYes_val_all_true j
    simp [Partial.valPart, Models.encodeTotalAsPartial, Models.totalTableToPartial,
          Models.encodePartial, Partial.valIndex] at this ⊢
    omega
  have hyYes_val_idx : yYes (Partial.valIndex j) = true := by
    simp [Partial.valIndex]
    have : Partial.valPart yYes j = true := hyYes_val_all_true j
    simp [Partial.valPart, Models.encodeTotalAsPartial, Models.totalTableToPartial,
          Models.encodePartial, Partial.valIndex] at this ⊢
    omega
  have h_val_agree : Partial.valPart z j = true := by
    have := hAgree j hj_in_D
    have : Partial.valPart yYes j = true := hyYes_val_all_true j
    rw [this] at ⊢
    exact this.symm
  have hz_mask_idx : z (Partial.maskIndex j) = true := by
    have : Partial.valPart z j = true := h_val_agree
    simp [Partial.valPart, Models.encodePartial, Partial.maskIndex] at this ⊢
    have : (Partial.decodePartial z) j ≠ none := by
      by_contra h_none
      have : Partial.valPart z j = false := by
        simp [Partial.valPart, Partial.maskIndex, Partial.valIndex, h_none]
      contradiction
    have : (Partial.decodePartial z) j = some true := by
      have h_vals : (Partial.decodePartial z) j = some ((Partial.decodePartial z) j.getD false) := by
        cases h : (Partial.decodePartial z) j with
        | none => simp at h_vals; simp [h] at this
        | some b => simp; rw [← h]
      have : (Partial.decodePartial z) j.getD false = true := h_val_agree
      rw [← this] at h_vals
      simp at h_vals ⊢
      exact h_vals
    simp [this]
  have hz_val_idx : z (Partial.valIndex j) = true := by
    have : (Partial.decodePartial z) j = some true := by
      have h_vals : (Partial.decodePartial z) j = some ((Partial.decodePartial z) j.getD false) := by
        cases h : (Partial.decodePartial z) j with
        | none => simp at h_vals; simp [h] at this
        | some b => simp; rw [← h]
      have : (Partial.decodePartial z) j.getD false = true := h_val_agree
      rw [← this] at h_vals
      simp at h_vals ⊢
      exact h_vals
    simp [Partial.valIndex, this]
  cases ForcingProperty.inputCoord_eq_mask_or_val p.n i with
  | inl h_eq_mask => rw [h_eq_mask, hyYes_mask_idx, hz_mask_idx]
  | inr h_eq_val => rw [h_eq_val, hyYes_val_idx, hz_val_idx]

/-!
## Main theorem: IsoStrongFamilyEventually for concreteFamily
-/

theorem isoStrongFamilyEventually_theorem :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (concreteFamily.paramsOf n β)),
      IsoStrongFamilyEventually concreteFamily hInDag :=
  by
    intro hInDag
    refine ⟨iso_beta0, by norm_num, iso_kappa, iso_nIso, ?_, ?_⟩
    
    -- Part 1: Forcing property
    · intro n β hβPos hβLt hn C hSize hCorrect
      let p := concreteFamily.paramsOf n β
      let S_table := ForcingProperty.support_on_table p C
      
      have hSupport_gthalf : (DagCircuit.support C).card > Partial.tableLen p.n / 2 :=
        ForcingProperty.support_card_gt_half_tableLen p C hSize hCorrect
      
      -- Choose yYes = encodeTotalAsPartial (fun _ => true)
      let Ty : PartialTruthTable p.n := fun _ => some true
      have hTy_yes : PartialMCSP_YES p Ty := by
        apply PartialMCSP_yes_of_small
        refine ⟨Circuit.const true, ?_, ?_⟩
        · simp [Circuit.size]; exact (baseParams n (by omega)).sYES_pos
        · intro x; simp [Ty, Circuit.eval]
      
      let yYes := Models.encodeTotalAsPartial (fun _ => true)
      have hyYes_yes : yYes ∈ (gapSliceOfParams p).Yes := by
        show gapPartialMCSP_Language p (partialInputLen p) yYes = true
        rw [gapPartialMCSP_language_true_iff_yes]
        simp [yYes]
        exact hTy_yes
      have hyYes_valid : ValidEncoding p yYes := 
        validEncoding_encodeTotalAsPartial p (fun _ => true)
      
      -- From agree_on_D_implies_agree_on_support_C, ANY nonempty D ⊆ S_table works
      have h_S_nonempty : S_table.Nonempty := by
        have h_sc_gt : (DagCircuit.support C).card > Partial.tableLen p.n / 2 :=
          ForcingProperty.support_card_gt_half_tableLen p C hSize hCorrect
        have h_sc_pos : (DagCircuit.support C).card > 0 := by omega
        have : (DagCircuit.support C).Nonempty := Finset.card_pos.mp h_sc_pos
        obtain ⟨i, hi⟩ := this
        have : ForcingProperty.tableIndexOfInput p.n i ∈ S_table := 
          ForcingProperty.tableIndex_in_support_on_table p C i hi
        use ForcingProperty.tableIndexOfInput p.n i
        simp [S_table, ForcingProperty.support_on_table]
        exact this
      obtain ⟨j0, hj0⟩ := h_S_nonempty
      let D := {j0}
      have hD_subset : D ⊆ S_table := by simp [D, hj0]
      have hDCard : D.card ≤ iso_kappa n β := by
        simp [iso_kappa, D, Partial.tableLen]
        have hn_ge : p.n ≥ 8 := by
          have h_params : p = baseParams n (by omega) := by simp [concreteFamily]
          simp only [h_params]
          exact (baseParams n (by omega)).n_ge
        have h_tableLen_ge : Partial.tableLen p.n ≥ 256 := by
          simp [Partial.tableLen]
          calc 2 ^ p.n ≥ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num : 1 < 2) hn_ge
            _ = 256 := by norm_num
        have h_kappa_ge : iso_kappa n β ≥ 128 := by
          simp [iso_kappa, Partial.tableLen]
          calc 2 ^ p.n / 2 ≥ 256 / 2 := Nat.div_le_div (by omega) (by norm_num) h_tableLen_ge
            _ = 128 := by norm_num
        omega
      refine ⟨yYes, hyYes_yes, hyYes_valid, D, hDCard, ?_⟩
      intro z hzValid hzAgree
      have hAgreeOnSupportC : ∀ i ∈ DagCircuit.support C, z i = yYes i := by
        apply agree_on_D_implies_agree_on_support_C p C D yYes z
        · exact hD_subset
        · exact hzAgree
        · intro j; simp [yYes, Partial.valPart, Models.encodeTotalAsPartial,
                  Models.totalTableToPartial, Models.encodePartial, Partial.valIndex]
      have hCz_eq : DagCircuit.eval C z = DagCircuit.eval C yYes := by
        apply DagCircuit.eval_eq_of_eq_on_support
        exact hAgreeOnSupportC
      have hCy_yes : DagCircuit.eval C yYes = true := hCorrect.1 yYes hyYes_yes
      have hCz : DagCircuit.eval C z = true := by rw [hCz_eq, hCy_yes]
      have hz_promise : z ∈ (gapSliceOfParams p).Yes ∨ z ∈ (gapSliceOfParams p).No := 
        mem_yes_or_no_gapSliceOfParams p z
      cases hz_promise with
      | inl h => exact h
      | inr h_no =>
        have : DagCircuit.eval C z = false := hCorrect.2 z h_no
        contradiction
      
    -- Part 2: Slack condition
    · intro n β hβPos hβLt hn
      let p := concreteFamily.paramsOf n β
      have h_params : p = baseParams n (by omega) := by simp [concreteFamily]
      simp only [h_params]
      have hMof : concreteFamily.Mof n (concreteFamily.Tof n β) = 
          circuitCountBound n (n ^ 2 + n) := by
        simp [concreteFamily, h_params]
        omega
      have hTof : concreteFamily.Tof n β = n ^ 2 + n := by
        simp [concreteFamily, h_params]
        omega
      rw [hMof, hTof]
      have hTableLen : Partial.tableLen n = 2 ^ n := by simp [Partial.tableLen]
      rw [hTableLen]
      have hIsoKappa : iso_kappa n β = 2 ^ n / 2 := by simp [iso_kappa, Partial.tableLen]
      rw [hIsoKappa]
      have hBound : circuitCountBound n (n ^ 2 + n) < 2 ^ (2 ^ n / 2) :=
        CircuitBound.circuit_bound_ok_simplest n (by omega)
      calc
        circuitCountBound n (n ^ 2 + n)
          < 2 ^ (2 ^ n / 2) := hBound
        _ = 2 ^ (2 ^ n - 2 ^ n / 2) := by
            congr 1
            have hn_ge : n ≥ 8 := by
              have : concreteFamily.N0 = 8 := by simp [concreteFamily]
              omega
            have h_pow_even : (2 ^ n) % 2 = 0 := by
              have : ∀ k ≥ 1, (2 ^ k) % 2 = 0 := by
                intro k hk
                induction k with
                | zero => simp at hk
                | succ k ih =>
                  cases k with
                  | zero => simp
                  | succ k => simp [Nat.pow_succ, Nat.mul_mod, Nat.add_mod]
              apply this n (by omega)
            have h_div_exact : 2 ^ n = 2 * (2 ^ n / 2) := by omega
            have h_eq1 : 2 ^ n / 2 = 2 ^ (n - 1) := by
              calc 2 ^ n / 2
                _ = (2 * 2 ^ (n - 1)) / 2 := by rw [← Nat.pow_succ]; omega
                _ = 2 ^ (n - 1) := by simp [Nat.mul_div_cancel_left _ (by norm_num)]
            have h_eq2 : 2 ^ n - 2 ^ n / 2 = 2 ^ (n - 1) := by
              rw [h_div_exact]; omega
            rw [h_eq2, h_eq1]
        _ = 2 ^ (2 ^ n - iso_kappa n β) := by rw [hIsoKappa]

/-- ISO Strong Family Eventually instance -/
def isoStrongFamilyEventually_concreteFamily :
    ∀ hInDag :
      ∀ n : Nat, ∀ β : Rat,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (concreteFamily.paramsOf n β)),
      IsoStrongFamilyEventually concreteFamily hInDag :=
  isoStrongFamilyEventually_theorem

end MistralTestLib
