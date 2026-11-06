import VirtualFinalClosure.ZeroTail
import VirtualFinalClosure.DirtyBanks
import VirtualFinalClosure.DirtyReady
import VirtualFinalClosure.LeafFirst
import VirtualFinalClosure.GuardFinalize
namespace VirtualFinalClosure.ZeroBranch
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
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
private theorem restored_outside (I : Nat → Option Bool) (F r n S i : Nat)
    (source : r < S) (room : S < F) (selected : I (S-r)=some false)
    (outside : ¬bank F r n i) :
    put (image I F r S r) (S-r) (some false) i=I i:=by
  by_cases hit : i=S-r
  · subst i
    dsimp only [put]
    rw [if_pos rfl,selected]
  · dsimp only [put,image,unary,lifted]
    rw [if_neg hit,if_neg (by dsimp only [bank] at outside;omega),if_neg (by omega)]
/-- From an actually reached seen0 marker, the literal restore/return,
arbitrary dirty-bank cleanup, canonical five rows and sixth FINAL row execute
on the SAME table and SAME tape. The initial source I and reference V are fixed
before the run. Full raw callers must derive this frame and its zero-source bit. -/
private theorem after_prefix (k N B P S L n Q F r s : Nat) (I V : Nat → Option Bool)
    (m : Fin 144) (c : Config (machine k).stateCount N B)
    (positive : 0 < n) (rp : 0 < r) (rs : r < S)
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
        ⟨if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
          ⟨L+n+1,hH⟩,fun i=>put (Cursor.Target.scratch V F r n) (L+n+1) (some false) i.val⟩ ∧
      (∀ u,u < s+t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ s+t → ((machine k).run u c).head.val ≤ P):=by
  let A:=image I F r S r
  let J:=put A (S-r) (some false)
  have frCopy:=fr
  obtain ⟨sl,_lh,paid,arena,eof,sep,right,_d0,_fence,_reg,_assn,_marks,_gap⟩:=frCopy
  have room : L+n+1 < F:=by omega
  have sf : S < F:=by omega
  have framedA:=protect fr (by intro i lo hi;exact markedLow I F r S r i rs lo hi)
  have framedJ:=protect framedA (by
    intro i lo _hi
    change (if i=S-r then some false else A i)=A i
    rw [if_neg (by omega)])
  have hole : A (S-r)=none:=by
    dsimp only [A,image,unary,lifted]
    rw [if_neg (by omega),if_pos ⟨rp,rfl⟩]
  have source (i : Nat) (lo : S-r < i) (hi : i < S) : ∃ b,A i=some b:=by
    obtain ⟨b,cell⟩:=suffix i lo hi
    refine ⟨b,?_⟩
    dsimp only [A,image,unary,lifted]
    rw [if_neg (by omega),if_neg (by omega),cell]
  have path:=zeroTail k P m.val S L (L+n+1) Q F (S-r) A false m.isLt zero framedA gap
    (by omega) (by omega) mode hole source
  have at238 : (machine k).run (s+(F-(S-r)+5)) c=
      ⟨nc k 238 m.val,⟨F+1,by omega⟩,fun i=>J i.val⟩:=by
    rw [UniformTM.run_add,arrived]
    exact execute path finite
  obtain ⟨ba,ca⟩:=markedBanks I F r S n (by omega) blank cells
  have blankJ (j : Nat) (hj : j ≤ 6) : J (SerializedBody.delimiter F r n j)=none:=by
    change (if SerializedBody.delimiter F r n j=S-r then some false else A (SerializedBody.delimiter F r n j))=none
    rw [if_neg (by interval_cases j <;> dsimp only [SerializedBody.delimiter] <;> omega)]
    exact ba j hj
  have cellsJ (j : Nat) (hj : j < 6) (i : Nat)
      (lo : SerializedBody.delimiter F r n j < i) (hi : i < SerializedBody.delimiter F r n (j+1)) : ∃ b,J i=some b:=by
    change ∃ b,(if i=S-r then some false else A i)=some b
    rw [if_neg (by interval_cases j <;> dsimp only [SerializedBody.delimiter] at lo <;> omega)]
    exact ca j hj i lo hi
  have cf:=cleanFrame framedJ blankJ cellsJ
  have clearedTape:=cleared J V L n F r room assignment (by
    intro i assn bankOut
    exact (restored_outside I F r n S i rs sf selected bankOut).trans (outside i assn bankOut))
  obtain ⟨d,hH,dp,done,heads⟩:=cleanup k N B P L n Q F r J m cf fit finite
  rw [clearedTape] at done
  let md : Fin 144:=⟨changeMeta 7 m.val,metaBound 7 _⟩
  have atReady : (machine k).run (s+(F-(S-r)+5)+d) c=
      ⟨ready k md,⟨L+n+1,hH⟩,fun i=>Cursor.Target.scratch V F r n i.val⟩:=by
    rw [UniformTM.run_add,at238]
    exact done
  have prefixHeads (u : Nat) (hu : u ≤ s+(F-(S-r)+5)+d) : ((machine k).run u c).head.val ≤ P:=by
    by_cases initial : u ≤ s
    · exact before u initial
    · by_cases middle : u ≤ s+(F-(S-r)+5)
      · rw [show u=s+(u-s) by omega,UniformTM.run_add,arrived]
        exact through path finite (u-s) (by omega)
      · rw [show u=(s+(F-(S-r)+5))+(u-(s+(F-(S-r)+5))) by omega,UniformTM.run_add,at238]
        exact heads _ (by omega)
  have vL : V L=none:=(outside L (by omega) (by dsimp only [bank];omega)).symm.trans sep
  have vH : V (L+n+1)=none:=(outside (L+n+1) (by omega) (by dsimp only [bank];omega)).symm.trans right
  obtain ⟨lastRun,first,lastHeads⟩:=leaf k N B P L n (s+(F-(S-r)+5)+d) md
    (Cursor.Target.scratch V F r n) (fun _=>false) c positive (by omega) finite
    ((scratchLow V F r n L (by omega)).trans vL)
    ((scratchLow V F r n (L+n+1) (by omega)).trans vH)
    (by intro j;rw [scratchLow V F r n (L+n-j.val) (by omega)];exact assignment _ (by have h:=j.isLt;omega) (by omega))
    prefixHeads atReady
  have fields : (flag md.val%2=1 ∧ bad md.val=0) ↔ (flag m.val%2=1 ∧ bad m.val=0):=by
    dsimp only [md]
    rw [(cleanupFlags m).1,(cleanupFlags m).2]
  refine ⟨(F-(S-r)+5)+d+6,hH,by omega,?_,?_,?_⟩
  · simpa only [Nat.add_assoc,fields] using lastRun
  · simpa only [Nat.add_assoc] using first
  · simpa only [Nat.add_assoc] using lastHeads
#print axioms restored_outside
#print axioms after_prefix
end VirtualFinalClosure.ZeroBranch
