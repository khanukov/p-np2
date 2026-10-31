import PhysicalCallerClosure.SourceInitialize
import PhysicalCallerClosure.RoundImage
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
private theorem mode_virtual {S} (source : Fin S → Bool) (p : Nat) :
    (SerializedBody.sourceMode source p).val=2 ↔ S ≤ p := by
  unfold SerializedBody.sourceMode
  by_cases hp:p < S
  · rw [dif_pos hp]
    cases source ⟨p,hp⟩ <;> simp only [ite_true,ite_false,Bool.false_eq_true,Fin.val_mk]
    all_goals omega
  · rw [dif_neg hp]
    change 2=2 ↔ S ≤ p
    omega
private theorem mode_value {S} (source : Fin S → Bool) (p : Nat) :
    decide ((SerializedBody.sourceMode source p).val=1)=padRead source p := by
  unfold SerializedBody.sourceMode padRead
  by_cases hp:p < S
  · rw [dif_pos hp,dif_pos hp]
    cases source ⟨p,hp⟩ <;> rfl
  · rw [dif_neg hp,dif_neg hp];rfl
private theorem anchor_virtual {S} (source : Fin S → Bool) (M : Nat) :
    (if M < S then (SerializedBody.sourceMode source (M-1)).val else 2)=2 ↔ S ≤ M := by
  by_cases hm:M < S
  · rw [if_pos hm]
    have h:=mode_virtual source (M-1)
    omega
  · rw [if_neg hm];omega
private theorem anchor_value {S} (source : Fin S → Bool) (M : Nat) :
    decide ((if M < S then (SerializedBody.sourceMode source (M-1)).val else 2)=1)=
      if M < S then padRead source (M-1) else false := by
  by_cases hm:M < S
  · rw [if_pos hm,if_pos hm,mode_value]
  · rw [if_neg hm,if_neg hm];rfl
private theorem source_cell {S} (source : Fin S → Bool) (T : Nat → Option Bool) (A p : Nat)
    (src:∀ i,A ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)) (lower:A ≤ p) :
    p < S → T p=some (decide ((SerializedBody.sourceMode source p).val=1)) := by
  intro hp
  rw [mode_value]
  unfold padRead
  rw [dif_pos hp]
  exact src p lower hp
private theorem zero_beta (n : Nat) : Pnp3.Core.vecOfNat n 0=(fun _=>false) := by
  funext j
  simp [Pnp3.Core.vecOfNat]
end PhysicalCallerClosure
