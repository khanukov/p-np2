import FullIngressClosure.Target
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1
private theorem workspace_span (R r n : Nat) (hr : r ≤ R) (hn : n ≤ R) :
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16 ≤ 34*(R+1) := by
  change 3*R+2+13*r+2*n+16+16 ≤ 34*(R+1)
  omega
private theorem preparation_price (R r n g ell W a b : Nat)
    (hr : r ≤ R) (hn : n ≤ R) (hg : g ≤ r) (he : ell ≤ r) (hw : W ≤ r)
    (ha : a ≤ 256*(n+r+1)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16))
    (hb : b ≤ 1024*(g+ell+W+1)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16)) :
    a+b+1 ≤ 262144*(R+1)^2 := by
  have span:=workspace_span R r n hr hn
  have widths : n+r+1 ≤ 2*(R+1) := by omega
  have values : g+ell+W+1 ≤ 3*(R+1) := by omega
  have left:=Nat.mul_le_mul (Nat.mul_le_mul_left 256 widths) span
  have right:=Nat.mul_le_mul (Nat.mul_le_mul_left 1024 values) span
  have square : 1 ≤ (R+1)^2:=by nlinarith
  nlinarith only [ha,hb,left,right,square]
end FullIngressClosure
