import NormalFinalClosure.Frame2
namespace NormalFinalClosure
private theorem guard_price (k N r P t d : Nat)
    (rN:r ≤ N) (PN:P+1 ≤ 64*(N+1))
    (prePrice:d ≤ 4398046511104*(k+1)*(N+1)^8)
    (tail:t ≤ 1048576*(r+1)^4*(P+1)^2) :
    d+t ≤ 17592186044416*(k+1)*(N+1)^8 := by
  have rpow:(r+1)^4 ≤ (N+1)^4:=Nat.pow_le_pow_left (by omega) 4
  have ppow:(P+1)^2 ≤ (64*(N+1))^2:=Nat.pow_le_pow_left PN 2
  have tailCoarse:t ≤ 4294967296*(N+1)^6 := by
    calc t ≤ 1048576*(r+1)^4*(P+1)^2:=tail
         _ ≤ 1048576*(N+1)^4*(64*(N+1))^2 :=
           Nat.mul_le_mul (Nat.mul_le_mul_left _ rpow) ppow
         _ = 4294967296*(N+1)^6:=by ring
  have upow:(N+1)^6 ≤ (N+1)^8:=Nat.pow_le_pow_right (by omega) (by omega)
  have factor:4294967296*(N+1)^6 ≤ 4294967296*(k+1)*(N+1)^8 := by
    exact Nat.mul_le_mul (by omega) upow
  have b:t ≤ 4294967296*(k+1)*(N+1)^8:=tailCoarse.trans factor
  have sum:4398046511104*(k+1)*(N+1)^8+4294967296*(k+1)*(N+1)^8 ≤
      17592186044416*(k+1)*(N+1)^8 := by
    rw [←Nat.add_mul,←Nat.add_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  exact (Nat.add_le_add prePrice b).trans sum
private theorem delimiter_bound (N S z n r : Nat) (_SN:S ≤ N) (_zN:z ≤ N) (rN:r ≤ N)
    (room:S+z+n+3+2^n < 3*N+2) :
    SerializedBody.delimiter (3*N+2) r n 12+6+1 ≤ 64*(N+1) := by
  change (3*N+2)+13*r+2*n+16+6+1 ≤ 64*(N+1)
  have nTotal:n ≤ S+z+n+3+2^n := calc
    n ≤ S+z+n:=Nat.le_add_left _ _
    _ ≤ S+z+n+3:=Nat.le_add_right _ _
    _ ≤ S+z+n+3+2^n:=Nat.le_add_right _ _
  have bound:n ≤ 3*N+2:=nTotal.trans room.le
  clear room nTotal _SN _zN
  omega
end NormalFinalClosure
