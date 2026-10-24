import IngressAllocation.Target
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1
private theorem old_le_new (k R : Nat) : FixedRawLengthFence.allocation R ≤ allocation k R := by
  have power : (R+1)^2 ≤ (R+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have coefficient : 16 ≤ 1099511627776*(k+1) := by omega
  calc
    FixedRawLengthFence.allocation R=16*(R+1)^2 := rfl
    _ ≤ (1099511627776*(k+1))*(R+1)^8 := Nat.mul_le_mul coefficient power
    _ = allocation k R := rfl
private theorem envelope_room (R : Nat) : 12*(R+1)^2+1 < tapeLength R (FixedRawLengthFence.allocation R) := by
  change 12*(R+1)^2+1 < R+16*(R+1)^2+1
  have positivePower : 0 < (R+1)^2 := Nat.pow_pos (by omega)
  nlinarith only [Nat.zero_le R,positivePower]
private theorem twelve_fields_bound (R r n : Nat) (hr : r ≤ R) (hn : n ≤ R) (positive : 1 ≤ R) :
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12 ≤ 12*(R+1)^2 := by
  change 3*R+2+13*r+2*n+16 ≤ 12*(R+1)^2
  nlinarith only [hr,hn,positive,Nat.zero_le (R^2)]
private theorem current_clock_fits (k R : Nat) :
    17179869184*(k+1)*(R+1)^6 ≤ allocation k R := by
  have power : (R+1)^6 ≤ (R+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have coefficient : 17179869184*(k+1) ≤ 1099511627776*(k+1) := by omega
  exact Nat.mul_le_mul coefficient power
end IngressAllocation
