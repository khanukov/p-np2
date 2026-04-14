/-
  mistral_test/SourceTheorems/ForcingProperty.lean
-/
import MistralTestLib.SourceTheorems.ConcreteFamily
import Pnp3.LowerBounds.MCSPGapLocality

namespace MistralTestLib
open Pnp3.Models Pnp3.LowerBounds Pnp3.Core

def support_on_table (p : GapPartialMCSPParams) (C : DagCircuit (partialInputLen p)) :
    Finset (Fin (Partial.tableLen p.n)) :=
  Finset.univ.filter (fun j =>
    Partial.maskIndex j.1 ∈ DagCircuit.support C ∨ Partial.valIndex j.1 ∈ DagCircuit.support C)

def tableIndexOfInput (n : Nat) (i : Fin (Partial.inputLen n)) : Fin (Partial.tableLen n) := by
  by_cases h_lt : i.1 < Partial.tableLen n
  · exact ⟨i.1, h_lt⟩
  · exact ⟨i.1 - Partial.tableLen n, by
      have h_ge : Partial.tableLen n ≤ i.1 := Nat.le_of_not_lt h_lt
      have h_lt_upper : i.1 < 2 * Partial.tableLen n := by simp[Partial.inputLen]; exact i.2
      omega⟩

lemma inputCoord_eq_mask_or_val (n : Nat) (i : Fin (Partial.inputLen n)) :
    i = Partial.maskIndex (tableIndexOfInput n i) ∨ i = Partial.valIndex (tableIndexOfInput n i) := by
  by_cases h_lt : i.1 < Partial.tableLen n
  · left; apply Fin.ext; simp[tableIndexOfInput,Partial.maskIndex]; omega
  · right; apply Fin.ext; simp[tableIndexOfInput,Partial.valIndex]; have h_ge : Partial.tableLen n ≤ i.1 := Nat.le_of_not_lt h_lt; omega

lemma tableIndex_in_support_on_table (p : GapPartialMCSPParams) (C : DagCircuit (partialInputLen p))
    (i : Fin (Partial.inputLen p)) (hi : i ∈ DagCircuit.support C) :
    tableIndexOfInput p.n i ∈ support_on_table p C := by
  simp[support_on_table]; cases inputCoord_eq_mask_or_val p.n i with
  | inl h_eq => left; rw[h_eq]; exact hi
  | inr h_eq => right; rw[h_eq]; exact hi

theorem support_card_gt_half_tableLen
    (p : GapPartialMCSPParams) (C : DagCircuit (partialInputLen p))
    (hSize : DagCircuit.size C ≤ p.sNO - 1) (hCorrect : CorrectOnPromiseSlice C (gapSliceOfParams p))
    : (DagCircuit.support C).card > Partial.tableLen p.n / 2 := by
  by_contra h_contra; push_neg at h_contra
  let S := support_on_table p C
  have hSCard_bound : S.card ≤ (DagCircuit.support C).card := by
    let f : S → DagCircuit.support C := fun j =>
      if h : Partial.maskIndex j.1 ∈ DagCircuit.support C then ⟨Partial.maskIndex j.1, h⟩
      else ⟨Partial.valIndex j.1, by have hj : j.1 ∈ S := j.2; simp[S,support_on_table] at hj; exact hj.2.2⟩
    have hinj : Function.Injective f := by
      intro j1 j2 heq; simp[f] at heq; split at heq
      · have : Partial.maskIndex j1.1 = Partial.maskIndex j2.1 := Subtype.ext_iff.mp heq
        have : j1.1 = j2.1 := by simp[Partial.maskIndex,Fin.ext_iff] at this; omega; exact Subtype.ext this
      · exfalso; have h1 : (Partial.maskIndex j1.1).1 < Partial.tableLen p.n := Partial.maskIndex_lt_tableLen j1.1
        have h2 : Partial.tableLen p.n ≤ (Partial.valIndex j2.1).1 := Partial.valIndex_in_right_half j2.1
        have : (Partial.maskIndex j1.1).1 < (Partial.valIndex j2.1).1 := Nat.lt_of_lt_of_le h1 h2
        have := congr_arg Fin.val this; omega
      · exfalso; have h2 : (Partial.maskIndex j2.1).1 < Partial.tableLen p.n := Partial.maskIndex_lt_tableLen j2.1
        have h1 : Partial.tableLen p.n ≤ (Partial.valIndex j1.1).1 := Partial.valIndex_in_right_half j1.1
        have : (Partial.maskIndex j2.1).1 < (Partial.valIndex j1.1).1 := Nat.lt_of_lt_of_le h2 h1
        have := congr_arg Fin.val this; omega
      · have : Partial.valIndex j1.1 = Partial.valIndex j2.1 := Subtype.ext_iff.mp heq
        have : j1.1 = j2.1 := by simp[Partial.valIndex,Fin.ext_iff] at this; omega; exact Subtype.ext this
    exact Finset.card_le_card (Finset.image_subset_iff.mpr (fun j => (f j).2))
  have hSCard : S.card ≤ Partial.tableLen p.n / 2 := by calc S.card ≤ (DagCircuit.support C).card := hSCard_bound; _ ≤ Partial.tableLen p.n / 2 := h_contra
  have hSlack : circuitCountBound p.n (p.sNO - 1) < 2^(Partial.tableLen p.n - S.card) := by
    have hCard : Partial.tableLen p.n - S.card ≥ Partial.tableLen p.n / 2 := by omega
    calc circuitCountBound p.n (p.sNO - 1) < 2^(Partial.tableLen p.n / 2) := p.circuit_bound_ok
      _ ≤ 2^(Partial.tableLen p.n - S.card) := by apply Nat.pow_le_pow_right (by norm_num:1<2) hCard
  obtain ⟨g, hg_false, hg_no⟩ := Pnp3.LowerBounds.Counting.exists_hard_function_with_constraints_of_countingSlack p S hSlack
  let T_yes : PartialTruthTable p.n := fun i => if i ∈ S then some false else none
  let x_yes : Core.BitVec (partialInputLen p) := Models.encodePartial T_yes
  let x_no : Core.BitVec (partialInputLen p) := Pnp3.Models.encodeTotalAsPartial g
  have hValidYes := Pnp3.LowerBounds.validEncoding_encodePartial p T_yes
  have hValidNo := Pnp3.LowerBounds.validEncoding_encodeTotalAsPartial p g
  have hInYes : x_yes ∈ (gapSliceOfParams p).Yes := by
    show Models.gapPartialMCSP_Language p (partialInputLen p) x_yes = true
    rw[Models.gapPartialMCSP_language_true_iff_yes]; simp[x_yes,Models.decodePartial_encodePartial,T_yes]
    refine ⟨Pnp3.Models.Circuit.const false, ?_, ?_⟩
    · simp[Pnp3.Models.Circuit.size]; exact p.sYES_pos
    · intro x; simp[x_yes,Models.Circuit.eval]
  have hInNo : x_no ∈ (gapSliceOfParams p).No := by
    show Models.gapPartialMCSP_Language p (partialInputLen p) x_no = false
    apply Models.gapPartialMCSP_language_false_of_no
    rw[show Models.decodePartial x_no = Models.totalTableToPartial g from by simp[x_no,Models.decodePartial_encodeTotal]]
    exact hg_no
  have hAgree_values : MCSPGapLocality.AgreeOnValues S x_yes x_no := by
    intro i hi
    have h_yes_val : Partial.valPart x_yes i = false := by simp[x_yes,T_yes,Partial.valPart,Models.encodePartial,Partial.valIndex,hi]
    have h_no_val : Partial.valPart x_no i = g i := by simp[x_no,Pnp3.Models.encodeTotalAsPartial,Models.totalTableToPartial,Partial.valPart,Models.encodePartial,Partial.valIndex]
    rw[h_yes_val,h_no_val,hg_false i hi]
  have hAgreeOnSupport : ∀ i ∈ DagCircuit.support C, x_yes i = x_no i := by
    intro i hi
    let j := tableIndexOfInput p.n i
    have hj_in_S : j ∈ S := tableIndex_in_support_on_table p C i hi
    cases inputCoord_eq_mask_or_val p.n i with
    | inl h_eq_mask =>
      rw[h_eq_mask]
      have h_yes_mask : x_yes (Partial.maskIndex j) = true := by simp[x_yes,T_yes,Models.encodePartial,Partial.maskIndex]; simp[hj_in_S]
      have h_no_mask : x_no (Partial.maskIndex j) = true := by simp[x_no,Pnp3.Models.encodeTotalAsPartial,Models.totalTableToPartial,Models.encodePartial,Partial.maskIndex]
      rw[h_yes_mask,h_no_mask]
    | inr h_eq_val =>
      rw[h_eq_val]
      have h_yes_val : x_yes (Partial.valIndex j) = false := by simp[x_yes,T_yes,Models.encodePartial,Partial.valIndex,hj_in_S]
      have h_no_val : x_no (Partial.valIndex j) = g j := by simp[x_no,Pnp3.Models.encodeTotalAsPartial,Models.totalTableToPartial,Models.encodePartial,Partial.valIndex]
      rw[h_yes_val,h_no_val,hg_false j hj_in_S]
  have hEq : DagCircuit.eval C x_yes = DagCircuit.eval C x_no := DagCircuit.eval_eq_of_eq_on_support hAgreeOnSupport
  have hTrue : DagCircuit.eval C x_yes = true := hCorrect.1 x_yes hInYes
  have hFalse : DagCircuit.eval C x_no = false := hCorrect.2 x_no hInNo
  rw[hTrue] at hEq; exact Bool.false_ne_true (hFalse.symm.trans hEq)

lemma support_card_le_twice_table_card (p : GapPartialMCSPParams) (C : DagCircuit (partialInputLen p)) :
    (DagCircuit.support C).card ≤ 2 * (support_on_table p C).card := by
  classical
  let proj : Fin (partialInputLen p) → Fin (Partial.tableLen p.n) := tableIndexOfInput p.n
  have h_proj_in : ∀ i ∈ DagCircuit.support C, proj i ∈ support_on_table p C := tableIndex_in_support_on_table p C
  have h_fiber : ∀ j ∈ support_on_table p C, (Finset.univ.filter (fun i => proj i = j ∧ i ∈ DagCircuit.support C)).card ≤ 2 := by
    intro j hj
    have h_only_two : ∀ i, proj i = j ∧ i ∈ DagCircuit.support C → i = Partial.maskIndex j ∨ i = Partial.valIndex j := by
      intro i ⟨h_proj,hi⟩
      simp[proj,tableIndexOfInput] at h_proj
      split at h_proj
      · left; exact Fin.ext h_proj.1
      · right; apply Fin.ext; simp[Partial.valIndex]; have h_ge : Partial.tableLen p.n ≤ i.1 := by omega; omega
    have h_sub : Finset.univ.filter (fun i => proj i = j ∧ i ∈ DagCircuit.support C) ⊆ {Partial.maskIndex j, Partial.valIndex j} := by
      intro i hi; simp only[Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton] at hi
      exact h_only_two i hi
    calc (Finset.univ.filter (fun i => proj i = j ∧ i ∈ DagCircuit.support C)).card
      ≤ ({Partial.maskIndex j, Partial.valIndex j} : Finset (Fin (partialInputLen p))).card := Finset.card_le_card h_sub
      _ = 2 := by simp
  have h_union : DagCircuit.support C ⊆ Finset.biUnion (support_on_table p C) (fun j => Finset.univ.filter (fun i => proj i = j ∧ i ∈ DagCircuit.support C)) := by
    intro i hi; have hj := h_proj_in i hi; use proj i, hj; simp only[Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion]; exact ⟨rfl,hi⟩
  calc (DagCircuit.support C).card ≤ (Finset.biUnion (support_on_table p C) (fun j => Finset.univ.filter (fun i => proj i = j ∧ i ∈ DagCircuit.support C))).card := Finset.card_le_card h_union
    _ ≤ Σ j : support_on_table p C, (Finset.univ.filter (fun i => proj i = j ∧ i ∈ DagCircuit.support C)).card := Finset.card_biUnion_le _ _
    _ ≤ Σ j : support_on_table p C, 2 := by apply Finset.sum_le_sum; intro j hj; exact h_fiber j hj
    _ = 2 * (support_on_table p C).card := by simp[Finset.sum_const,Finset.card_univ]

end MistralTestLib
