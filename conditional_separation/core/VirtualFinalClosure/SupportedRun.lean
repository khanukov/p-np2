import VirtualFinalClosure.RawEof
import VirtualFinalClosure.RawLengthFinal
import VirtualFinalClosure.RawCapFinal
import VirtualFinalClosure.RawNormal
namespace VirtualFinalClosure.SupportedRun
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.RawEof","VirtualFinalClosure.RawEof","raw_eof","rawEof"),
      ("VirtualFinalClosure.RawLengthFinal","VirtualFinalClosure.RawLengthFinal","raw_final","rawLength"),
      ("VirtualFinalClosure.RawCapFinal","VirtualFinalClosure.RawCapFinal","raw_final","rawCap"),
      ("VirtualFinalClosure.RawNormal","VirtualFinalClosure.RawNormal","raw_normal","rawNormal"),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","length_shortage","lengthShort"),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth"),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue"),
      ("VirtualFinalClosure.FinalResources","VirtualFinalClosure.FinalResources","room","finiteRoom"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","scratch_bound","scratchBound"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","prefix_price","prefixPrice"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","prefix_space","prefixSpace"),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exhaustive actual supported raw branch {mod}/{key}"
private def Result (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n z : Nat) : Prop:=
    let S:=a+m;let R:=pairLength a m;let B:=allocation k R;let C0:=CertificateGuardClosure.allocation k R
    let M:=machine k;let O:=CertificateGuardClosure.machine k;let c:=initialConfig M B (encodePair x w)
    let old:=initialConfig O C0 (encodePair x w);let L:=S+z+2;let F:=FixedRawLengthFence.fencePos R
    let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p;let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
    let g:=n^k+k;let B0:=FixedRawLengthFence.allocation R
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) Q Q false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r;let Z:=AllArityBitLength.Target.seedImage Y F r n
    let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W
    ∃ (T : Nat) (hH:S+z+n+3 < tapeLength R B),T ≤ deadline k R ∧
      (∀ u,u ≤ T → (M.run u c).head.val ≤ spaceBound k R) ∧
      (∀ u,u < T → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject ∧
        ∀ (mode:Fin 3) (flag:Fin 144),(M.run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) flag) ∧
      ((p < S ∧ bitLength n ≤ r ∧ W ≤ r ∧ SerializedBody.delimiter F r n 12 < tapeLength R B ∧
          (∀ i,address ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
          ∃ h:C0 ≤ B,T ≤ CertificateGuardClosure.deadline k R ∧
            (∀ u,u ≤ T → ∃ flag:Fin 144,M.run u c=config k flag (IngressAllocation.extendConfig h (O.run u old))) ∧
            M.run T c=⟨control k (CertificateGuardClosure.old k (TotalIngressClosure.old k
              (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address))))) ⟨8,by decide⟩,
                ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared I S address F r n g W i.val⟩) ∨
       (S ≤ address ∧ ((p=S) ∨ (p < S ∧ (r < bitLength n ∨ (bitLength n ≤ r ∧
          ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d)))) ∧
        (∀ j:Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
        (n=0 → (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=none) ∧
        (∀ positive:0 < n,(treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=some (Pnp3.Models.Circuit.input ⟨0,positive⟩)) ∧
        ∃ C,((p=S ∧ C=0) ∨ (p < S ∧ r ≤ C ∧ C ≤ 2*(W+r+1))) ∧
          F+5*C+n+7 < tapeLength R B ∧
          M.run T c=⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then M.accept else M.reject,
            ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F p C i.val⟩))
private theorem decoder (k n : Nat) :
    (n=0 → (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=none) ∧
    (∀ positive:0 < n,(treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=some (Pnp3.Models.Circuit.input ⟨0,positive⟩)):=by
  constructor
  · intro zero;subst n;exact treeCircuitWitnessCodec_decode_blank_zero k
  · exact treeCircuitWitnessCodec_decode_blank_pos k
private theorem selected_virtual (k n z S : Nat)
    (why:min (9+2*z+2^n) S=S ∨ S-min (9+2*z+2^n) S < Cursor.Target.W k n) : S ≤ Cursor.Target.M k n z:=by
  change S ≤ 9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
  rcases why with eof|shortage <;> omega
/-- Exhaustive selection of the literal normal/EOF/elln-cap/four-W-cap
executions. All runtime work is already executed by the cited raw terms;
these proof cases only classify those real finite-table branches. -/
private theorem classified (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical:m=a+1) (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) : Result k x w n z:=by
  let S:=a+m;let R:=pairLength a m;let p:=min (9+2*z+2^n) S;let r:=S-p;let W:=Cursor.Target.W k n
  have pair:S ≤ R:=by dsimp only [S,R,pairLength];omega
  have rr:r ≤ R:=(Nat.sub_le _ _).trans pair
  have finite:=finiteRoom k R
  obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨arena,_source,_eof,_reg,_sep,_assn,_last,_marks,_gap,_fence⟩:=cells
  change S+z+n+3+2^n < 3*R+2 at arena
  by_cases eof:p=S
  · obtain ⟨t,hH,tp,done,first,heads⟩:=rawEof k x w canonical header tag gamma firstPhysical cap rows eof
    have virtual:=selected_virtual k n z S (Or.inl eof)
    have small:t ≤ CertificateGuardClosure.deadline k R:=by
      have pow:(R+1)^2 ≤ (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
      exact tp.trans (Nat.mul_le_mul (by omega : 8192 ≤ 137438953472*(k+1)) pow)
    refine ⟨t,hH,small.trans (prefixPrice k R),fun u hu=>(heads u hu).trans (prefixSpace k R),first,Or.inr ?_⟩
    refine ⟨virtual,Or.inl eof,fun j=>padRead_ge _ (virtual.trans (Nat.le_add_right _ j.val)),(decoder k n).1,(decoder k n).2,0,Or.inl ⟨eof,rfl⟩,?_,?_⟩
    · have bound:3*R+2+5*0+n+7 ≤ 12*(R+1)^2:=by
        nlinarith only [arena,Nat.zero_le S,Nat.zero_le z,Nat.zero_le (2^n),Nat.zero_le R,Nat.zero_le (R^2)]
      exact (bound.trans (prefixSpace k R)).trans_lt finite
    · have eofRaw:min (9+2*z+2^n) (a+m)=a+m:=eof
      simpa only [eofRaw] using done
  · have physical:p < S:=lt_of_le_of_ne (Nat.min_le_right _ _) eof
    have nr:n ≤ R:=actualWidth R S z n pair physical
    by_cases ellFits:bitLength n ≤ r
    · by_cases wFits:W ≤ r
      · obtain ⟨t,hH,h,tp,fit,source,every,done,first,heads⟩:=rawNormal k x w canonical header tag gamma firstPhysical cap rows physical ellFits wFits
        exact ⟨t,hH,tp.trans (prefixPrice k R),fun u hu=>(heads u hu).trans (prefixSpace k R),first,
          Or.inl ⟨physical,ellFits,wFits,fit,source,h,tp,every,done⟩⟩
      · have shortage:r < W:=Nat.lt_of_not_ge wFits
        obtain ⟨data,t,C,hH,rLower,limit,tp,done,first,heads⟩:=rawCap k x w canonical header tag gamma firstPhysical cap rows physical ellFits shortage
        have virtual:=selected_virtual k n z S (Or.inr shortage)
        exact ⟨t,hH,tp,heads,first,Or.inr ⟨virtual,Or.inr ⟨physical,Or.inr ⟨ellFits,data⟩⟩,
          fun j=>padRead_ge _ (virtual.trans (Nat.le_add_right _ j.val)),(decoder k n).1,(decoder k n).2,
          C,Or.inr ⟨physical,rLower,limit⟩,(scratchBound k R n r C nr rr limit).trans_lt finite,done⟩⟩
    · have shortage:r < bitLength n:=Nat.lt_of_not_ge ellFits
      obtain ⟨t,C,hH,rLower,limit,tp,done,first,heads⟩:=rawLength k x w canonical header tag gamma firstPhysical cap rows physical shortage
      have virtual:=selected_virtual k n z S (Or.inr (lengthShort k n r shortage))
      exact ⟨t,hH,tp,heads,first,Or.inr ⟨virtual,Or.inr ⟨physical,Or.inl shortage⟩,
        fun j=>padRead_ge _ (virtual.trans (Nat.le_add_right _ j.val)),(decoder k n).1,(decoder k n).2,
        C,Or.inr ⟨physical,rLower,limit⟩,(scratchBound k R n r C nr rr limit).trans_lt finite,done⟩⟩
#print axioms Result
#print axioms decoder
#print axioms selected_virtual
#print axioms classified
end VirtualFinalClosure.SupportedRun
