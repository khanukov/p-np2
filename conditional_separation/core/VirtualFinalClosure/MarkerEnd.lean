import VirtualFinalClosure.SourceFinish
namespace VirtualFinalClosure.MarkerEnd
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protectedFrame",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","mark_decrement","decrement",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","done_to_source","toSource",1),
      ("VirtualFinalClosure.SourceFinish","VirtualFinalClosure.SourceFinish","final_hole","findHole",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","mark_loop","markLoop",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","protected_image","protectedImage",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","delimiter","delimiter",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","digit","digit",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","lower","lower",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_bound","modeBound",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_mode","modeValue",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_seen_zero","seenZero",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong physical source-marker endpoint term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique real source-marker endpoint {mod}/{key}"
/-- Complete execution from the physical bank0 counter to the ACTUAL source p
hole. The r iterations and their source observations are proved, not installed.
The saved bit and the suffix-zero flag are returned as facts of finite control. -/
private theorem marked_source (k P m S L H Q F r : Nat) (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (eof : sourceMode m=2) (initialZero : seen m=0)
    (fr : Frame T S L H Q F) (gap : H+Q+1 < F) (positive : 0 < r) (source : r < S)
    (fit : F+r+2 ≤ P) (bank : ∀ i,F+1 < i → i < F+r+2 → T i=some true)
    (last : T (F+r+2)=none) (cells : ∀ i,i < r → T (S-1-i)=some (bits i)) :
    ∃ d,d ≤ r*(2*r+2*(F-S)+14)+(F-S)+r+7 ∧
      GPath (M:=machine k) P d (C k 6 m (F+1) T)
        (C k 40 (modes m bits r) (S-r) (image T F r S r)) ∧
      sourceMode (modes m bits r)=(if bits (r-1) then 1 else 0) ∧
      (seen (modes m bits r)=0 ↔ ∀ i,i < r → bits i=false) := by
  have copyFrame:=fr
  obtain ⟨sl,lh,_q,arena,sourceEnd,_l,_h,_d0,_f,_reg,_assign,_tally,_gap⟩:=copyFrame
  have room : S ≤ F+1 := by omega
  let U:=image T F r S r
  let m1:=modes m bits r
  have bound : m1 < 144 := modeBound m bits r hm
  obtain ⟨t,price,loop⟩:=markLoop k P m S L H Q F r T bits hm eof fr gap source fit bank last cells r le_rfl
  have frame : Frame U S L H Q F := protectedFrame fr (by
    intro i lo hi
    exact protectedImage T F r S r i source lo hi)
  have frameCopy:=frame
  obtain ⟨_sl,_lh,_q1,_arena,endBlank,_l1,_h1,d0,_f1,_reg1,_assn1,_tally1,_gap1⟩:=frameCopy
  have empty:=decrement k P m1 (F+1) r 0 U bound (by omega) (by omega) d0
    (by
      change image T F r S r (F+1+r+1)=none
      rw [show F+1+r+1=F+r+2 by omega,delimiter T F r S r room]
      exact last) (by
      intro i lo hi
      have cell:=digit T F r S r i lo (by omega)
      simpa only [Nat.sub_self,Nat.add_zero] using cell)
  simp only [Nat.mul_zero,Nat.zero_add,ite_true] at empty
  have walk:=toSource k P m1 S L H Q F U bound frame (by omega)
  have hole : U (S-r)=none := by
    change image T F r S r (S-r)=none
    rw [lower T F r S r (S-r) room (by omega),if_pos ⟨positive,rfl⟩]
  have suffix : ∀ i,S-r < i → i < S → ∃ b,U i=some b := by
    intro i lo hi
    let j:=S-1-i
    have small : j < r := by dsimp only [j];omega
    have cell:=cells j small
    have eq : S-1-j=i := by dsimp only [j];omega
    refine ⟨bits j,?_⟩
    change image T F r S r i=some (bits j)
    rw [lower T F r S r i room hi.le,if_neg (by omega)]
    exact (congrArg T eq.symm).trans cell
  have find:=findHole k P m1 S (S-r) U bound (by omega) (by omega) endBlank hole suffix
  have path:=joinPath (joinPath (joinPath loop empty) walk) find
  have span : S-(S-r)=r := by omega
  rw [span] at path
  refine ⟨t+3+(F-S+3)+(r+1),?_,path,modeValue m bits r positive,seenZero m bits r initialZero⟩
  omega
#print axioms marked_source
end VirtualFinalClosure.MarkerEnd
