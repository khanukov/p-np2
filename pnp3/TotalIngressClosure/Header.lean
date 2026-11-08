import TotalIngressClosure.Gate
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open FixedGammaTargetRegisterDecrement (borrow decBit)
/-- General source-header identification, including physically missing later payload bits.
No semantic acceptance, complete payload or successful parser premise. -/
private theorem header_data {a m z : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    ∃ n,contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
      2^z ≤ n+1 ∧ n+1 < 2^(z+1) ∧ borrow x w z ≤ z ∧
      (∀ j,j ≤ z → n.testBit (z-j)=decBit x w z (borrow x w z) j) ∧
      (∀ b,z < b → n.testBit b=false) := by
  have present: (contentHeader? (Fin.append x w)).isSome=true:=
    (fixedGamma_header_contract (Fin.append x w)).1 (by rw [gamma];rfl)
  cases header:contentHeader? (Fin.append x w) with
  | none => simp only [header,Option.isSome_none,Bool.false_eq_true] at present
  | some pair =>
    rcases pair with ⟨n,consumed⟩
    obtain ⟨z',width,length,lower,upper,borrowBound,digits,high⟩:=decremented_register_digits x w header
    have equal:z'=z:=Option.some.inj (width.symm.trans gamma)
    subst z'
    subst consumed
    refine ⟨n,rfl,lower,upper,borrowBound,?_,high⟩
    intro j hj
    exact (digits j hj).symm
private theorem zero_width {n : Nat} (high:n+1 < 2^(0+1)) : n=0:=by
  norm_num at high
  omega
private theorem one_width {n : Nat} (low:2^1 ≤ n+1) (high:n+1 < 2^(1+1)) : n=1 ∨ n=2:=by
  norm_num at low high
  omega
private theorem wide_width {n z : Nat} (wide:2 ≤ z) (low:2^z ≤ n+1) : 3 ≤ n:=by
  have four:4 ≤ 2^z:=Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) wide
  omega
/-- This bound uses the ACTUAL paid-row capacity, never accepted-only table support. -/
private theorem triple_lt_power (R : Nat) (positive:1 ≤ R) : 3*R < 2^(R+1) := by
  induction R with
  | zero => omega
  | succ R ih =>
    by_cases empty:R=0
    · subst R;decide
    · have prev:=ih (by omega)
      have growth:4 ≤ 2^(R+1):=Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega : 2 ≤ R+1)
      rw [show R+1+1=(R+1)+1 by omega,pow_succ]
      nlinarith only [prev,growth]
private theorem table_budget_width (R S z n : Nat) (positive:1 ≤ R)
    (paid:S+z+n+3+2^n < FixedRawLengthFence.fencePos R) : n ≤ R := by
  have cap:2^n < 3*R:=by change S+z+n+3+2^n < 3*R+2 at paid;omega
  by_contra no
  have lower:2^(R+1) ≤ 2^n:=Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
  have upper:=triple_lt_power R positive
  omega
private theorem physical_full_gamma (S z n : Nat)
    (physical:min (9+2*z+2^n) S < S) : 9+2*z < S := by
  have pw:0 < 2^n:=Nat.two_pow_pos n
  have left:9+2*z+2^n < S:=by
    by_contra no
    rw [Nat.min_eq_right (by omega)] at physical
    omega
  omega
end TotalIngressClosure
