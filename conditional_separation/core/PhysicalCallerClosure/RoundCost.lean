import PhysicalCallerClosure.RowAfter
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
private theorem extent_price (R S z n r q : Nat) (rr:r ≤ R)
    (arena:S+z+n+3+q < FixedRawLengthFence.fencePos R) :
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+7 ≤ 32*(R+1) := by
  change 3*R+2+13*r+2*n+16+7 ≤ 32*(R+1)
  change S+z+n+3+q < 3*R+2 at arena
  omega
private theorem round_price (R r d h b v : Nat) (rr:r ≤ R) (extent:d+7 ≤ 32*(R+1))
    (reset:h ≤ 1024*(r+1)*(d+7)) (body:b ≤ 1073741824*(R+1)^6) (native:v ≤ 256*(d+7)) :
    h+b+v ≤ 2147483648*(R+1)^6 := by
  have x1:1 ≤ R+1:=by omega
  have p1:(R+1) ≤ (R+1)^6:=by simpa using Nat.pow_le_pow_right x1 (show 1 ≤ 6 by decide)
  have p2:(R+1)^2 ≤ (R+1)^6:=Nat.pow_le_pow_right x1 (by decide)
  have hm:h ≤ 32768*(R+1)^2:=by nlinarith [Nat.mul_le_mul (show r+1 ≤ R+1 by omega) extent]
  have vm:v ≤ 8192*(R+1):=by omega
  nlinarith
private theorem all_price (R Q row t initial : Nat) (_rpos:1 ≤ R) (paid:Q ≤ 3*R+2)
    (count:row ≤ Q) (loops:t ≤ row*(2147483648*(R+1)^6))
    (start:initial ≤ 4096*(R+1)^2) : initial+t ≤ 1099511627776*(R+1)^8 := by
  have x1:1 ≤ R+1:=by omega
  have p2:(R+1)^2 ≤ (R+1)^8:=Nat.pow_le_pow_right x1 (by decide)
  have p7:(R+1)^7 ≤ (R+1)^8:=Nat.pow_le_pow_right x1 (by decide)
  have rows:row ≤ 3*(R+1):=by omega
  have loops':t ≤ 6442450944*(R+1)^7:=by
    have mult:=Nat.mul_le_mul_right (2147483648*(R+1)^6) rows
    rw [pow_succ] at ⊢
    nlinarith
  nlinarith
end PhysicalCallerClosure
