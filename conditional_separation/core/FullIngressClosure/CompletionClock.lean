import FullIngressClosure.PreparationClock
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let e ← getEnv
  let found:=e.constants.toList.filter fun (n,_) =>
    n.toString.startsWith "_private.FullIngressClosure.PreparationClock." &&
    n.toString.endsWith ".FullIngressClosure.workspace_span"
  match found with
  | [(n,.thmInfo ci)] =>
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit `workspaceSpan n :: st.openDecls}
  | _ => throwError "Nonunique workspace span theorem: {found.map Prod.fst}"
private theorem installer_price (R r n ell W a b c d e : Nat)
    (hr : r ≤ R) (hn : n ≤ R) (he : ell ≤ r) (hw : W ≤ r)
    (ha : a ≤ 524288*(R+1)^2)
    (hb : b ≤ (32*r+4)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16))
    (hc : c ≤ (64*ell+4)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16))
    (hd : d ≤ (64*W+4)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16))
    (hf : e ≤ 32*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16)) :
    a+b+c+d+e ≤ 1073741824*(R+1)^3 := by
  let P:=SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16
  have span : P ≤ 34*(R+1):=workspaceSpan R r n hr hn
  have sum : b+c+d+e ≤ (32*r+64*ell+64*W+44)*P:=by
    change b ≤ (32*r+4)*P at hb
    change c ≤ (64*ell+4)*P at hc
    change d ≤ (64*W+4)*P at hd
    change e ≤ 32*P at hf
    nlinarith only [hb,hc,hd,hf]
  have count : 32*r+64*ell+64*W+44 ≤ 160*(R+1):=by omega
  have price:=Nat.mul_le_mul count span
  have total : a+b+c+d+e ≤ 1048576*(R+1)^2:=by nlinarith only [ha,sum,price]
  have cube : (R+1)^2 ≤ (R+1)^3:=by nlinarith only [Nat.zero_le (R*(R+1)^2)]
  nlinarith only [total,cube,Nat.zero_le ((R+1)^2)]
end FullIngressClosure
