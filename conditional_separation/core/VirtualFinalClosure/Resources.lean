import VirtualFinalClosure.Target
namespace VirtualFinalClosure.Resources
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  let found:=env.constants.toList.filter fun (n,_)=>
    n.toString.startsWith "_private.IngressAllocation.Extension." &&
    n.toString.endsWith ".IngressAllocation.extend_unique"
  match found with
  | [(n,.thmInfo ci)]=>
    logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `uniqueExtension n::st.openDecls}
  | _=>throwError "Nonunique whole-Config extension theorem"
private def extension_type : ∀ {states N C B : Nat} (h : C ≤ B)
    {small : Config states N C} {large : Config states N B},
    FixedPairParser.ConfigExtension h small large → large=IngressAllocation.extendConfig h small := uniqueExtension
private theorem old_le_new (k N : Nat) : CertificateGuardClosure.allocation k N ≤ allocation k N := by
  change 1099511627776*(k+1)*(N+1)^8 ≤ 281474976710656*(k+1)^4*(N+1)^(k+12)
  have hk : k+1 ≤ (k+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 1≤4 by decide)
  have hn : (N+1)^8 ≤ (N+1)^(k+12) := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul (by decide) hk) hn
private theorem old_room (k N : Nat) :
    12*(N+1)^2+1 < tapeLength N (CertificateGuardClosure.allocation k N) := by
  have hn : (N+1)^2 ≤ (N+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hk : (1:Nat) ≤ k+1 := by omega
  have lower : 1099511627776*(N+1)^2 ≤ CertificateGuardClosure.allocation k N := by
    change _ ≤ 1099511627776*(k+1)*(N+1)^8
    simpa only [Nat.mul_one] using Nat.mul_le_mul (Nat.mul_le_mul_left 1099511627776 hk) hn
  have positive : 1 ≤ (N+1)^2 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<N+1) (show 0≤2 by decide)
  dsimp only [tapeLength]
  omega
private theorem prefix_price (k N : Nat) : CertificateGuardClosure.deadline k N ≤ deadline k N := by
  change 137438953472*(k+1)*(N+1)^6 ≤ 18446744073709551616*(k+1)^8*(N+1)^(4*k+24)
  have hk : k+1 ≤ (k+1)^8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 1≤8 by decide)
  have hn : (N+1)^6 ≤ (N+1)^(4*k+24) := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul (by decide) hk) hn
private theorem prefix_space (k N : Nat) : 12*(N+1)^2 ≤ spaceBound k N := by
  have hn : (N+1)^2 ≤ (N+1)^(k+3) := Nat.pow_le_pow_right (by omega) (by omega)
  have pk : 1 ≤ (k+1)^2 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 0≤2 by decide)
  have hk : 12 ≤ 1048576*(k+1)^2 := by omega
  exact Nat.mul_le_mul hk hn
private theorem one_le_power (N t : Nat) : 1 ≤ (N+1)^t := by
  simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<N+1) (Nat.zero_le t)
private theorem power_two (j : Nat) : j+1 ≤ 2^j := by
  induction j with
  | zero => decide
  | succ j ih => rw [pow_succ];have pos:=Nat.two_pow_pos j;nlinarith
private theorem bitLength_le (n : Nat) : bitLength n ≤ n := by
  by_cases empty : n=0
  · subst n;simp [bitLength]
  · have pos : 0<n := by omega
    have bits:=bitLength_pos_of_pos pos
    have lower:=two_pow_bitLength_pred_le pos
    have linear:=power_two (bitLength n-1)
    omega
private theorem weight_bound (k N n : Nat) (hn : n ≤ N) :
    Cursor.Target.W k n ≤ 4*(k+1)*(N+1)^(k+1) := by
  have width : bitLength n+4 ≤ 4*(N+1) := by have bits:=bitLength_le n;omega
  have pow : n^k ≤ (N+1)^k := Nat.pow_le_pow_left (by omega) k
  have base:=one_le_power N k
  have g : n^k+k ≤ (k+1)*(N+1)^k := by nlinarith
  have mult:=Nat.mul_le_mul width g
  change (bitLength n+4)*(n^k+k) ≤ _
  calc
    _ ≤ (4*(N+1))*((k+1)*(N+1)^k) := mult
    _ = 4*(k+1)*(N+1)^(k+1) := by rw [pow_succ];ring
private theorem scratch_bound (k N n r C : Nat) (hn : n ≤ N) (hr : r ≤ N)
    (hc : C ≤ 2*(Cursor.Target.W k n+r+1)) :
    3*N+2+5*C+n+7 ≤ spaceBound k N := by
  have w:=weight_bound k N n hn
  have pw : N+1 ≤ (N+1)^(k+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<N+1) (show 1≤k+1 by omega)
  have kp : (N+1)^(k+1) ≤ (k+1)*(N+1)^(k+1) := by nlinarith
  have small : 3*N+2+5*C+n+7 ≤ 64*(k+1)*(N+1)^(k+1) := by nlinarith
  have hn' : (N+1)^(k+1) ≤ (N+1)^(k+3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hk : 64*(k+1) ≤ 1048576*(k+1)^2 := by nlinarith
  exact small.trans (Nat.mul_le_mul hk hn')
/-- The concrete parent prefix is extended by actual move room, not elapsed≤C0.
This is a component of the full new Raw proof; it does not execute the new guard. -/
private theorem old_prefix_extension (k N t : Nat) (y : Bitstring N)
    (heads : ∀ u,u ≤ t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).head.val ≤ 12*(N+1)^2) :
    ∀ u,u ≤ t →
      (CertificateGuardClosure.machine k).run u (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)=
      IngressAllocation.extendConfig (old_le_new k N)
        ((CertificateGuardClosure.machine k).run u
          (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)) := by
  intro u hu
  apply uniqueExtension (old_le_new k N)
  apply FixedPairParser.run_extension
  · exact FixedPairParser.initialConfig_extension _ (old_le_new k N) y
  · intro v hv
    have bound:=heads v (by omega)
    have fit:=old_room k N
    omega
#print axioms extension_type
#print axioms old_le_new
#print axioms old_room
#print axioms prefix_price
#print axioms prefix_space
#print axioms weight_bound
#print axioms scratch_bound
#print axioms old_prefix_extension
end VirtualFinalClosure.Resources
