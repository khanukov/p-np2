import VirtualFinalClosure.LeafZero
import VirtualFinalClosure.ZeroCleanup
import VirtualFinalClosure.ZeroBranch
import VirtualFinalClosure.ZeroTail
import VirtualFinalClosure.DirtyBanks
import VirtualFinalClosure.DirtyReady
import VirtualFinalClosure.LeafFirst
import VirtualFinalClosure.GuardFinalize
namespace VirtualFinalClosure.ZeroFinished
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ZeroCleanup","VirtualFinalClosure.ZeroCleanup","prepared","zeroCleanup",(1:Nat)),
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
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
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
private theorem prepared (k N B P S L n Q F r s : Nat) (I V : Nat → Option Bool)
    (m : Fin 144) (c : Config (machine k).stateCount N B)
    (rp : 0 < r) (rs : r < S)
    (fr : Frame I S L (L+n+1) Q F) (gap : L+n+1+Q+1 < F)
    (blank : ∀ j,j ≤ 6 → I (SerializedBody.delimiter F r n j)=none)
    (cells : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ b,I i=some b)
    (suffix : ∀ i,S-r < i → i < S → ∃ b,I i=some b)
    (selected : I (S-r)=some false) (zero : seen m.val=0) (mode : sourceMode m.val=0)
    (assignment : ∀ i,L < i → i < L+n+1 → V i=some false)
    (outside : ∀ i,¬(L < i ∧ i < L+n+1) → ¬bank F r n i → I i=V i)
    (fit : F+5*r+n+7 ≤ P) (finite : P < tapeLength N B)
    (before : ∀ u,u ≤ s → ((machine k).run u c).head.val ≤ P)
    (arrived : (machine k).run s c=
      ⟨nc k 40 m.val,⟨S-r,by obtain ⟨sl,_lh,qp,_room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,
        fun i=>image I F r S r i.val⟩) :
    ∃ (t : Nat) (hH : L+n+1 < tapeLength N B),
      t ≤ (F-(S-r)+5)+(F-(L+n+1)+18*r+6*n+45)+6 ∧
      (machine k).run (s+t) c=
        ⟨if 0<n ∧ flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
          ⟨L+n+1,hH⟩,fun i=>if i.val=L+n+1 then (if n=0 then none else some false)
            else Cursor.Target.scratch V F r n i.val⟩ ∧
      (∀ u,u < s+t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ s+t → ((machine k).run u c).head.val ≤ P):=by
  obtain ⟨d,hH,dp,atReady,heads⟩:=zeroCleanup k N B P S L n Q F r s I V m c
    rp rs fr gap blank cells suffix selected zero mode assignment outside fit finite before arrived
  let md : Fin 144:=⟨changeMeta 7 m.val,metaBound 7 _⟩
  let T:=Cursor.Target.scratch V F r n
  have frCopy:=fr
  obtain ⟨_sl,_lh,_paid,arena,_eof,sep,last,_d0,_fence,_reg,_assn,_marks,_gap⟩:=frCopy
  have room : L+n+1 < F:=by omega
  have sepV : V L=none:=by
    have eq:=outside L (by omega) (by dsimp only [bank];omega)
    exact eq.symm.trans sep
  have lastV : V (L+n+1)=none:=by
    have eq:=outside (L+n+1) (by omega) (by dsimp only [bank];omega)
    exact eq.symm.trans last
  have sepT : T L=none:=(scratchLow V F r n L (by omega)).trans sepV
  have lastT : T (L+n+1)=none:=(scratchLow V F r n (L+n+1) (by omega)).trans lastV
  have headFit : L+n+1 ≤ P:=by omega
  by_cases positive : 0<n
  · obtain ⟨done,first,allHeads⟩:=leaf k N B P L n (s+d) md T (fun _=>false) c
      positive headFit finite sepT lastT (by
        intro j
        change Cursor.Target.scratch V F r n (L+n-j.val)=some false
        rw [scratchLow V F r n _ (by have bound:=j.isLt;omega)]
        exact assignment _ (by have bound:=j.isLt;omega) (by omega)) heads atReady
    have test : (flag md.val%2=1 ∧ bad md.val=0) ↔ (0<n ∧ flag m.val%2=1 ∧ bad m.val=0):=by
      dsimp only [md]
      rw [(cleanupFlags m).1,(cleanupFlags m).2]
      exact (and_iff_right positive).symm
    refine ⟨d+6,hH,by omega,?_,?_,?_⟩
    · have actual : (machine k).run (s+d+6) c=
          ⟨if 0<n ∧ flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
            ⟨L+n+1,hH⟩,fun i=>put T (L+n+1) (some false) i.val⟩:=by
        simpa only [test] using done
      have image : put T (L+n+1) (some false)=
          (fun i=>if i=L+n+1 then (if n=0 then none else some false) else T i):=by
        funext i
        change (if i=L+n+1 then some false else T i)=_
        rw [if_neg (Nat.ne_of_gt positive)]
      have eqtime : s+(d+6)=s+d+6:=by omega
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
    obtain ⟨done,first,allHeads⟩:=leafZero k N B P L (s+d) md T c
      (by simpa only [Nat.add_zero] using headFit) finite sepT (by simpa only [Nat.add_zero] using lastT)
      heads atReady
    refine ⟨d+5,hH,by omega,?_,?_,?_⟩
    · rw [show s+(d+5)=s+d+5 by omega]
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
end VirtualFinalClosure.ZeroFinished
