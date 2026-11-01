import VirtualFinalClosure.Resources
namespace VirtualFinalClosure.CapMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
set_option autoImplicit false
private theorem value_positive (k n : Nat) : 0 < n^k+k := by
  cases k
  · simp
  · omega
private theorem weight_lower (k n : Nat) :
    bitLength n+4  ≤  Cursor.Target.W k n ∧ n^k+k  ≤  Cursor.Target.W k n := by
  have positive:=value_positive k n
  change bitLength n+4  ≤  (bitLength n+4)*(n^k+k) ∧ n^k+k  ≤  (bitLength n+4)*(n^k+k)
  constructor <;> nlinarith
/-- Every one of the FOUR exact physical residual alternatives implies lack of
capacity. This says virtual continuation, and does NOT say semantic rejection. -/
private theorem cap_shortage (k n r v2 v3 v4 v5 d : Nat)
    (cap : CappedWeight.Target.Cap k n r v2 v3 v4 v5 d) : r < Cursor.Target.W k n := by
  obtain ⟨width,value⟩:=weight_lower k n
  rcases cap with power|add|widthAdd|product
  · obtain ⟨j,a,e,jk,ac,en,eq,_rest⟩:=power
    have positive : 0 < n := by omega
    have next : (a+1)*n  ≤  n^j*n := Nat.mul_le_mul_right n (by omega)
    have partialProduct : a*n+e  <  n^j*n := by nlinarith
    have bounded : n^(j+1)  ≤  n^k := Nat.pow_le_pow_right positive (by omega)
    rw [←pow_succ] at partialProduct
    omega
  · obtain ⟨j,jk,eq,_rest⟩:=add
    omega
  · obtain ⟨j,j4,eq,_rest⟩:=widthAdd
    omega
  · obtain ⟨a,e,ac,en,eq,_rest⟩:=product
    have next : (a+1)*(n^k+k)  ≤  (bitLength n+4)*(n^k+k) :=
      Nat.mul_le_mul_right (n^k+k) (by omega)
    change r < (bitLength n+4)*(n^k+k)
    nlinarith
private theorem capacity_success_only (k n C v2 v3 v4 v5 d : Nat)
    (fits : Cursor.Target.W k n ≤ C) : ¬CappedWeight.Target.Cap k n C v2 v3 v4 v5 d := by
  intro cap
  have shortage:=cap_shortage k n C v2 v3 v4 v5 d cap
  omega
private theorem length_shortage (k n r : Nat) (shortage : r < bitLength n) :
    r < Cursor.Target.W k n := by
  have width:=(weight_lower k n).1
  omega
private theorem virtual_address (k n z S : Nat)
    (physical : 9+2*z+2^n < S)
    (shortage : S-(9+2*z+2^n) < Cursor.Target.W k n) : S < Cursor.Target.M k n z := by
  change S < 9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
  omega
private theorem doubled_capacity (W r C : Nat) (positive : 0 < C) (shortage : C < W)
    (old : r ≤ C) : r ≤ 2*C ∧ C < 2*C ∧ 2*C ≤ 2*(W+r+1) := by omega
#print axioms value_positive
#print axioms weight_lower
#print axioms cap_shortage
#print axioms capacity_success_only
#print axioms length_shortage
#print axioms virtual_address
#print axioms doubled_capacity
end VirtualFinalClosure.CapMeaning
