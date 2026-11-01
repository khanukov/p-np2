import FullFinalClosure.Prepared
import FullFinalClosure.Arithmetic
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`FullFinalClosure.Control,`FullFinalClosure,["entryA_safe","left_inj","right_accept","right_reject","right_reflect_accept","right_reflect_reject","runB","prefixA","handoff_config"]),
    (`FullFinalClosure.Arithmetic,`FullFinalClosure,["old_allocation","a_room"]),
    (`FullFinalClosure.Prepared,`FullFinalClosure,["prepared_final"]),
    (`IngressAllocation.Extension,`IngressAllocation,["extend_unique"]),
    (`IngressAllocation.Geometry,`IngressAllocation,["old_le_new"]),
    (`VirtualFinalClosure.NormalImage,`VirtualFinalClosure.NormalImage,["high_blank","extended_tape"])] do
    for leaf in leaves do
      let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some (.thmInfo ci):=e.find? n | throwError "Missing exact whole-raw interface {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing whole-raw owner"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong whole-raw owner"
      logInfo m!"registered-interface|{owner}|{n}|theorem|{(repr ci.type).pretty 1000000000}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private theorem raw_head_room (k N t : Nat) (y : Bitstring N) (price:t≤runtimeBound k N) :
    ∀ u,u≤t → ((machine k).run u (initialConfig (machine k) (allocation k N) y)).head.val+1 <
      tapeLength N (allocation k N) := by
  intro u hu
  have h:((machine k).run u (initialConfig (machine k) (allocation k N) y)).head.val≤u:=
    (machine k).run_initialConfig_head_le y
  have space:t+1≤allocation k N:=by unfold allocation;omega
  unfold tapeLength
  omega
private theorem normal_high (k N a m n z : Nat) (x:Bitstring a) (w:Bitstring m)
    (same:pairLength a m=N)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap:n<FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n<FixedRawLengthFence.fencePos N) :
    ∀ (i : Nat), tapeLength N (VirtualFinalClosure.allocation k N) ≤ i →
      SerializedBody.prepared (normalBase k N x w z n) (a+m) (Cursor.Target.M k n z)
        (FixedRawLengthFence.fencePos N) (a+m-min (9+2*z+2^n) (a+m)) n (n^k+k) (Cursor.Target.W k n) i=none := by
  subst N
  have small:FixedRawLengthFence.allocation (pairLength a m)≤VirtualFinalClosure.allocation k (pairLength a m):=
    (old_le_new k (pairLength a m)).trans (old_allocation k (pairLength a m))
  have fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos (pairLength a m))
      (a+m-min (9+2*z+2^n) (a+m)) n 12 <
      tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)):=by
    have sr:a+m≤pairLength a m:=by change a+m≤2*a+1+m;omega
    have rn:a+m-min (9+2*z+2^n) (a+m)≤pairLength a m:=(Nat.sub_le _ _).trans sr
    have positive:1≤pairLength a m:=by change 1≤2*a+1+m;omega
    have nt:n≤a+m+z+n+3+2^n:=
      ((Nat.le_add_left n (a+m+z)).trans (Nat.le_add_right (a+m+z+n) 3)).trans (Nat.le_add_right _ (2^n))
    have nn:n≤3*(pairLength a m)+2:=nt.trans arena.le
    change 3*(pairLength a m)+2+13*(a+m-min (9+2*z+2^n) (a+m))+2*n+16 <
      (pairLength a m)+16*((pairLength a m)+1)^2+1
    nlinarith only [sr,rn,positive,nn,Nat.zero_le ((pairLength a m)^2)]
  have high:=high_blank k x w gamma cap (by omega) fit
  intro i hi
  exact high i (by dsimp only [tapeLength] at hi ⊢;omega)
private theorem included_reject (k : Nat) {N C B : Nat} (h:C≤B)
    (c:Config (CertificateGuardClosure.machine k).stateCount N C)
    (no:c.state=(CertificateGuardClosure.machine k).reject) :
    (VirtualFinalClosure.config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h c)).state=
      (VirtualFinalClosure.machine k).reject := by
  change VirtualFinalClosure.control k c.state ⟨8,by decide⟩=(VirtualFinalClosure.machine k).reject
  rw [no]
  rfl
/-- Connected execution on the frozen single finite table. -/
private theorem raw_complete (k : Nat) : Target.Raw k := by
  intro N y B A M c ac
  let C:=VirtualFinalClosure.allocation k N
  let small:=initialConfig A C y
  obtain ⟨d,dp,heads,first,outcome⟩:=VirtualFinalClosure.raw k N y
  have h:C≤B:=by dsimp only [C,B,allocation];omega
  have ext:∀ u,u≤d → FixedPairParser.ConfigExtension h (A.run u small) (A.run u ac):=by
    intro u hu
    exact FixedPairParser.run_extension A h (FixedPairParser.initialConfig_extension A h y) u
      (fun v hv=>by
        have hb:(A.run v (initialConfig A C y)).head.val≤VirtualFinalClosure.spaceBound k N:=heads v (by omega)
        have room:VirtualFinalClosure.spaceBound k N+1<tapeLength N C:=a_room k N
        omega)
  have firstBig:∀ u,u<d → (A.run u ac).state≠A.accept ∧ (A.run u ac).state≠A.reject ∧
      ∀ (mode:Fin 3) (flag:Fin 144),(A.run u ac).state≠VirtualFinalClosure.control k
        (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) flag:=by
    intro u hu
    rw [←(ext u hu.le).1]
    exact first u hu
  have history:∀ u,u≤d → M.run u c=configA k (A.run u ac):=
    prefixA k N B d y (fun u hu mode=>(firstBig u hu).2.2 mode ⟨8,by decide⟩)
  have prior:∀ u,u<d → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject:=by
    intro u hu
    rw [history u hu.le]
    refine ⟨?_,?_⟩
    · intro bad;exact (firstBig u hu).1 (left_inj k bad)
    · intro bad;exact (firstBig u hu).2.1 (left_inj k bad)
  rcases outcome with rejected|normalOrVirtual
  · rcases rejected with ⟨h0,s,sd,_sp,oldReject,whole,no⟩
    have hit:(A.run d small).state=A.reject:=
      (congrArg Config.state whole).trans (included_reject k h0 _ oldReject)
    have arrived:(A.run d ac).state=A.reject:=(ext d le_rfl).1.symm.trans hit
    have answer:(A.run d ac).state=(if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y then A.accept else A.reject):=by rw [no];exact arrived
    refine ⟨d,d,le_rfl,by dsimp only [runtimeBound];omega,history,firstBig,prior,
      raw_head_room k N d y (by dsimp only [runtimeBound];omega),?_,Or.inl ⟨rfl,answer⟩⟩
    rw [history d le_rfl]
    change left k (A.run d ac).state=_
    rw [no,arrived]
    rfl
  · rcases normalOrVirtual with ⟨a,m,x,w,hN,decoded,word,length,n,z,hH,tag,gamma,header,capacity,arena,branch⟩
    rcases branch with normal|virtual
    · rcases normal with ⟨physical,ell,window,_fit,_source,_oldBudget,_oldPrice,_oldHistory,atBody⟩
      let S:=a+m;let F:=FixedRawLengthFence.fencePos N;let r:=S-min (9+2*z+2^n) S
      let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
      let mode:=SerializedBody.sourceMode (Fin.append x w) address
      have hHB:S+z+n+3<tapeLength N B:=by
        have mono:tapeLength N C≤tapeLength N B:=by unfold tapeLength;omega
        exact hH.trans_le mono
      let body:Config (NormalFinalClosure.machine2 k).stateCount N B:=
        ⟨entryB k mode,⟨S+z+n+3,hHB⟩,
          fun i=>SerializedBody.prepared (normalBase k N x w z n) S address F r n (n^k+k) W i.val⟩
      have atBig:A.run d ac=⟨entryA k mode,body.head,body.tape⟩:=by
        have eq:=extend_unique h (ext d le_rfl)
        rw [atBody] at eq
        exact eq.trans (extended_tape h _ _ _ (normal_high k N a m n z x w hN gamma capacity arena))
      have stay:M.run (d+1) c=configB k body:=by
        rw [UniformTM.run,history d le_rfl,atBig]
        exact handoff_config k N B mode body.head body.tape
      have oldBudget:RawCallerClosure.allocation k N≤B:=(old_allocation k N).trans h
      obtain ⟨s,sp,bfirst,bfinal⟩:=prepared_final k N B a m n z x w hN length tag gamma header capacity arena physical ell window oldBudget hHB
      have coupled:∀ v,M.run (d+1+v) c=configB k ((NormalFinalClosure.machine2 k).run v body):=by
        intro v
        rw [M.run_add,stay,runB]
      have correct:PartAEndpoint.thresholdContentWitnessRelation k a m x w=
          encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y:=by
        simp only [encodedRelationLanguage,decoded]
      have final:(M.run (d+1+s) c).state=(if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y then M.accept else M.reject):=by
        rw [coupled]
        change right k ((NormalFinalClosure.machine2 k).run s body).state=_
        rw [bfinal,correct]
        cases encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y
        · exact right_reject k
        · exact right_accept k
      have fullFirst:∀ v,v<d+1+s → (M.run v c).state≠M.accept ∧ (M.run v c).state≠M.reject:=by
        intro v hv
        by_cases early:v<d
        · exact prior v early
        by_cases same:v=d
        · subst v
          rw [history d le_rfl,atBig]
          refine ⟨?_,?_⟩
          · intro bad;exact (entryA_safe k mode).1 (left_inj k bad)
          · intro bad;exact (entryA_safe k mode).2 (left_inj k bad)
        · have tail:v=d+1+(v-(d+1)):=by omega
          rw [tail,coupled]
          refine ⟨?_,?_⟩
          · intro bad;exact (bfirst (v-(d+1)) (by omega)).1 (right_reflect_accept k _ bad)
          · intro bad;exact (bfirst (v-(d+1)) (by omega)).2 (right_reflect_reject k _ bad)
      have price:d+1+s≤runtimeBound k N:=by dsimp only [runtimeBound];omega
      refine ⟨d,d+1+s,by omega,price,history,firstBig,fullFirst,raw_head_room k N _ y price,final,Or.inr ?_⟩
      exact ⟨a,m,x,w,hN,decoded,word,length,n,z,tag,gamma,header,capacity,arena,physical,ell,window,
        hHB,atBig,stay,s,rfl,fun v _=>coupled v⟩
    · rcases virtual with ⟨_address,_domain,_zeros,_n0,_npos,C0,_capacity,_fit,finish⟩
      have hit:(A.run d small).state=(if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y then A.accept else A.reject):=
        congrArg Config.state finish
      have answer:(A.run d ac).state=(if encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y then A.accept else A.reject):=
        (ext d le_rfl).1.symm.trans hit
      refine ⟨d,d,le_rfl,by dsimp only [runtimeBound];omega,history,firstBig,prior,
        raw_head_room k N d y (by dsimp only [runtimeBound];omega),?_,Or.inl ⟨rfl,answer⟩⟩
      rw [history d le_rfl]
      change left k (A.run d ac).state=_
      rw [answer]
      cases encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y <;> rfl
end FullFinalClosure
