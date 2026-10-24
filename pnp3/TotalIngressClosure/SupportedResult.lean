import TotalIngressClosure.PositiveVirtual
import TotalIngressClosure.NormalTotal
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.CanonicalSpec","TotalIngressClosure","CanonicalResult","CanonicalResult"),
      ("TotalIngressClosure.PositiveVirtual","TotalIngressClosure","virtual_result","virtualResult"),
      ("TotalIngressClosure.NormalTotal","TotalIngressClosure","normal_consumer_heads","normalResult"),
      ("TotalIngressClosure.EofTotal","TotalIngressClosure","eof_raw_heads","eofRun"),
      ("TotalIngressClosure.VirtualTail","TotalIngressClosure","physical_virtual_heads","virtualRun"),
      ("TotalIngressClosure.WeightTotal","TotalIngressClosure","physical_weight_heads","weightRun"),
      ("TotalIngressClosure.FirstEvents","TotalIngressClosure","normal_first","normalFirst"),
      ("TotalIngressClosure.VirtualFrame","TotalIngressClosure","virtual_frame","sourceFrame"),
      ("TotalIngressClosure.Header","TotalIngressClosure","table_budget_width","tableWidth"),
      ("IngressAllocation.Geometry","IngressAllocation","twelve_fields_bound","twelveBound"),
      ("IngressAllocation.Geometry","IngressAllocation","envelope_room","envelopeRoom")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical supported totality {mod}/{key}: {found.map Prod.fst}"
private theorem eof_price(k R t:Nat)(price:t ≤ 65536*(R+1)^2):t ≤ 536870912*(k+1)*(R+1)^3:=by
  exact price.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by decide)))
set_option maxRecDepth 4000 in
private theorem supported_result(k:Nat){a m n z:Nat}(x:Bitstring a)(w:Bitstring m)
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    CanonicalResult k x w:=by
  let R:=pairLength a m;let S:=a+m;let p:=min (9+2*z+2^n) S;let r:=S-p
  let c:=initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation R) (encodePair x w)
  by_cases eof:p=S
  · obtain ⟨t,hH,price,done,heads⟩:=eofRun k x w header tag gamma physical cap rows eof
    have beyond:S ≤ Cursor.Target.M k n z:=by
      have lo:S ≤ 9+2*z+2^n:=by dsimp only [p] at eof;omega
      dsimp only [Cursor.Target.M];omega
    exact virtualResult k x w tag gamma header physical cap rows false (Or.inl ⟨rfl,eof⟩)
      t hH (eof_price k R t price) beyond (Or.inl eof) done heads
  · have phys:p < S:=lt_of_le_of_ne (Nat.min_le_right _ _) eof
    by_cases ell:bitLength n ≤ r
    · by_cases fits:Cursor.Target.W k n ≤ r
      · obtain ⟨t,hH,price,heads,done,source,first⟩:=normalResult k x w header tag gamma physical cap rows phys ell fits
        have safe:=normalFirst c (SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z)) (congrArg Config.state done) first
        obtain ⟨arena,_sep,_last,_digits⟩:=sourceFrame x w gamma cap rows
        have rR:r ≤ R:=(Nat.sub_le _ _).trans (by dsimp only [R,S,pairLength];omega)
        have nR:n ≤ R:=tableWidth R S z n (by dsimp only [R,pairLength];omega) arena
        have D12:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12 < tapeLength R (FixedRawLengthFence.allocation R):=
          (twelveBound R r n rR nR (by dsimp only [R,pairLength];omega)).trans_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (envelopeRoom R))
        refine ⟨t,price.trans (Nat.mul_le_mul_right _ (by omega :2147483648*(k+1) ≤ 4294967296*(k+1))),heads,safe.1,safe.2,Or.inr ?_⟩
        exact ⟨n,z,hH,tag,gamma,header,cap,arena,Or.inl ⟨phys,ell,fits,D12,source,done⟩⟩
      · have over:r < Cursor.Target.W k n:=Nat.lt_of_not_ge fits
        obtain ⟨t,_price,_heads,_before,result⟩:=weightRun k x w header tag gamma physical cap rows phys ell
        have caps:∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d:=by
          rcases result with ⟨fits,_⟩|⟨v2,v3,v4,v5,d,cap,_⟩
          · exact False.elim (Nat.not_lt_of_ge fits over)
          · exact ⟨v2,v3,v4,v5,d,cap⟩
        obtain ⟨t,hH,price,beyond,done,heads⟩:=virtualRun k x w header tag gamma physical cap rows phys over
        exact virtualResult k x w tag gamma header physical cap rows true (Or.inr ⟨rfl,phys,Or.inr ⟨ell,caps⟩⟩)
          t hH price beyond.le (Or.inr ⟨phys,over⟩) done heads
    · have over:r < Cursor.Target.W k n:=by
        have cover:bitLength n+4 ≤ Cursor.Target.W k n:=(VirtualLeaf.decode_leaf k n (fun _=>false)).1
        omega
      obtain ⟨t,hH,price,beyond,done,heads⟩:=virtualRun k x w header tag gamma physical cap rows phys over
      exact virtualResult k x w tag gamma header physical cap rows true (Or.inr ⟨rfl,phys,Or.inl (Nat.lt_of_not_ge ell)⟩)
        t hH price beyond.le (Or.inr ⟨phys,over⟩) done heads
end TotalIngressClosure
