import RawCallerClosure.Target
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
private theorem gates_positive (k n : Nat) : 0<n^k+k := by
  cases k with
  | zero => simp
  | succ k => omega
private theorem window_positive (k n : Nat) : 0<Cursor.Target.W k n := by
  exact Nat.mul_pos (by omega) (gates_positive k n)
private theorem large_budget (k R : Nat) :
    FixedRawLengthFence.allocation R ≤ allocation k R := by
  change 16*(R+1)^2 ≤ 1099511627776*(k+1)*(R+1)^8
  have pow:(R+1)^2 ≤ (R+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have coeff:16 ≤ 1099511627776*(k+1):=by omega
  exact Nat.mul_le_mul coeff pow
private theorem metadata_room (R r n : Nat) (rp:1≤R) (rr:r≤R) (nr:n≤R) :
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 <
      tapeLength R (FixedRawLengthFence.allocation R) := by
  change 3*R+2+13*r+2*n+16+6 < R+16*(R+1)^2+1
  nlinarith only [rr,nr,rp,Nat.zero_le (R^2)]
private theorem raw_rows_price (k R pre t : Nat)
    (hp:pre≤137438953472*(k+1)*(R+1)^6) (tp:t≤1099511627776*(R+1)^8) :
    pre+t ≤ deadline k R := by
  have powers:(R+1)^6 ≤ (R+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have mult:137438953472*(k+1)*(R+1)^6 ≤ 137438953472*(k+1)*(R+1)^8:=Nat.mul_le_mul_left _ powers
  have one:(R+1)^8 ≤ (k+1)*(R+1)^8:=Nat.le_mul_of_pos_left _ (by omega)
  change pre+t ≤ 4398046511104*(k+1)*(R+1)^8
  nlinarith only [hp,tp,mult,one]
end RawCallerClosure
