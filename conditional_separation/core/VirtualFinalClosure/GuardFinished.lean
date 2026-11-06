import VirtualFinalClosure.LeafZero
import VirtualFinalClosure.GuardCleanup
import VirtualFinalClosure.ZeroBranch
import VirtualFinalClosure.ZeroTail
import VirtualFinalClosure.DirtyBanks
import VirtualFinalClosure.DirtyReady
import VirtualFinalClosure.LeafFirst
import VirtualFinalClosure.GuardFinalize
namespace VirtualFinalClosure.GuardFinished
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardCleanup","VirtualFinalClosure.GuardCleanup","prepared","guardCleanup",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("VirtualFinalClosure.LeafZero","VirtualFinalClosure.LeafZero","after_prefix","leafZero",1),
      ("VirtualFinalClosure.ZeroBranch","VirtualFinalClosure.ZeroBranch","restored_outside","restoredOutside",(1:Nat)),
      ("VirtualFinalClosure.ZeroTail","VirtualFinalClosure.ZeroTail","prepared","zeroTail",(1:Nat)),
      ("VirtualFinalClosure.DirtyBanks","VirtualFinalClosure.DirtyBanks","frame","cleanFrame",1),
      ("VirtualFinalClosure.DirtyBanks","VirtualFinalClosure.DirtyBanks","cleared","cleared",1),
      ("VirtualFinalClosure.DirtyReady","VirtualFinalClosure.DirtyReady","prepared","cleanup",1),
      ("VirtualFinalClosure.LeafFirst","VirtualFinalClosure.LeafFirst","after_prefix","leaf",1),
      ("VirtualFinalClosure.GuardFinalize","VirtualFinalClosure.GuardFinalize","flags","cleanupFlags",1),
      ("VirtualFinalClosure.GuardFinalize","VirtualFinalClosure.GuardFinalize","scratch_low","scratchLow",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","protected_image","markedLow",1),
      ("VirtualFinalClosure.LengthGrowFrame","VirtualFinalClosure.LengthGrowFrame","marked_banks","markedBanks",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualReady.Raw","VirtualReady","bank","bank",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong executed seen0-to-FINAL term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique executed seen0-to-FINAL term {mod}/{key}"
private theorem prepared (k N B P S L n Q F C a b d e s : Nat) (U : Nat → Option Bool)
    (m : Fin 144) (c : Config (machine k).stateCount N B)
    (fr : Frame U S L (L+n+1) Q F) (banks : Banks U L n F C)
    (b0 : ∀ i,F+1 < i → i < F+C+2 → ∃ v,U i=some v)
    (b1 : ∀ i,F+C+2 < i → i < F+C+n+3 → ∃ v,U i=some v)
    (assignment : ∀ i,L < i → i < L+n+1 → U i=some false)
    (fit : F+5*C+n+7 ≤ P) (finite : P < tapeLength N B)
    (before : ∀ u,u ≤ s → ((machine k).run u c).head.val ≤ P)
    (arrived : (machine k).run s c=⟨nc k 238 m.val,⟨F+1,by omega⟩,
      fun i=>image U L n F C a b d e i.val⟩) :
    ∃ (t : Nat) (hH : L+n+1 < tapeLength N B),
      t ≤ F-(L+n+1)+18*C+6*n+51 ∧
      (machine k).run (s+t) c=
        ⟨if 0<n ∧ flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
          ⟨L+n+1,hH⟩,fun i=>if i.val=L+n+1 then (if n=0 then none else some false)
            else Cursor.Target.scratch U F C n i.val⟩ ∧
      (∀ u,u < s+t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ s+t → ((machine k).run u c).head.val ≤ P):=by
  obtain ⟨t,hH,tp,done,localHeads⟩:=guardCleanup k N B P S L n Q F C a b d e U m fr banks b0 b1 assignment fit finite
  have atReady : (machine k).run (s+t) c=
      ⟨ready k ⟨changeMeta 7 m.val,metaBound 7 _⟩,⟨L+n+1,hH⟩,
        fun i=>Cursor.Target.scratch U F C n i.val⟩:=by
    rw [UniformTM.run_add,arrived]
    exact done
  have heads (u : Nat) (hu : u ≤ s+t) : ((machine k).run u c).head.val ≤ P:=by
    by_cases early : u ≤ s
    · exact before u early
    · rw [show u=s+(u-s) by omega,UniformTM.run_add,arrived]
      exact localHeads _ (by omega)
  let md : Fin 144:=⟨changeMeta 7 m.val,metaBound 7 _⟩
  let T:=Cursor.Target.scratch U F C n
  have frCopy:=fr
  obtain ⟨_sl,_lh,_paid,arena,_eof,sep,last,_d0,_fence,_reg,_assn,_marks,_gap⟩:=frCopy
  have room : L+n+1 < F:=by omega
  have sepT : T L=none:=(scratchLow U F C n L (by omega)).trans sep
  have lastT : T (L+n+1)=none:=(scratchLow U F C n (L+n+1) (by omega)).trans last
  have headFit : L+n+1 ≤ P:=by omega
  by_cases positive : 0<n
  · obtain ⟨done,first,allHeads⟩:=leaf k N B P L n (s+t) md T (fun _=>false) c
      positive headFit finite sepT lastT (by
        intro j
        change Cursor.Target.scratch U F C n (L+n-j.val)=some false
        rw [scratchLow U F C n _ (by have bound:=j.isLt;omega)]
        exact assignment _ (by have bound:=j.isLt;omega) (by omega)) heads atReady
    have test : (flag md.val%2=1 ∧ bad md.val=0) ↔ (0<n ∧ flag m.val%2=1 ∧ bad m.val=0):=by
      dsimp only [md]
      rw [(cleanupFlags m).1,(cleanupFlags m).2]
      exact (and_iff_right positive).symm
    refine ⟨t+6,hH,by omega,?_,?_,?_⟩
    · have actual : (machine k).run (s+t+6) c=
          ⟨if 0<n ∧ flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
            ⟨L+n+1,hH⟩,fun i=>put T (L+n+1) (some false) i.val⟩:=by
        simpa only [test] using done
      have image : put T (L+n+1) (some false)=
          (fun i=>if i=L+n+1 then (if n=0 then none else some false) else T i):=by
        funext i
        change (if i=L+n+1 then some false else T i)=_
        rw [if_neg (Nat.ne_of_gt positive)]
      have eqtime : s+(t+6)=s+t+6:=by omega
      rw [eqtime]
      refine actual.trans ?_
      apply Config.ext_parts
      · rfl
      · rfl
      · exact congrArg (fun U=>fun i : Fin (tapeLength N B)=>U i.val) image
    · simpa only [Nat.add_assoc] using first
    · simpa only [Nat.add_assoc] using allHeads
  · have zeroN : n=0:=by omega
    subst n
    obtain ⟨done,first,allHeads⟩:=leafZero k N B P L (s+t) md T c
      (by simpa only [Nat.add_zero] using headFit) finite sepT (by simpa only [Nat.add_zero] using lastT)
      heads atReady
    refine ⟨t+5,hH,by omega,?_,?_,?_⟩
    · rw [show s+(t+5)=s+t+5 by omega]
      refine done.trans ?_
      apply Config.ext_parts
      · rw [if_neg (by omega : ¬(0<0 ∧ flag m.val%2=1 ∧ bad m.val=0))]
      · rfl
      · funext i
        change T i.val=(if i.val=L+0+1 then none else T i.val)
        by_cases hit : i.val=L+0+1
        · rw [if_pos hit,hit];exact lastT
        · rw [if_neg hit]
    · simpa only [Nat.add_assoc] using first
    · simpa only [Nat.add_assoc] using allHeads
#print axioms prepared
end VirtualFinalClosure.GuardFinished
