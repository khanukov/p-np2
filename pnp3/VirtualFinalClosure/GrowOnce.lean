import VirtualFinalClosure.GrowEntry
import VirtualFinalClosure.GrowDispatch
namespace VirtualFinalClosure.GrowOnce
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual growing-bank path interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank path interface {mod}/{key}"
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.GrowDispatch","VirtualFinalClosure.GrowDispatch","to_reset","toReset",1),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","double","doubleBank",1),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.GrowReturn","VirtualFinalClosure.GrowReturn","return_source","returnSource",1),
      ("VirtualFinalClosure.GrowEntry","VirtualFinalClosure.GrowEntry","reentry_row","reentryRow",1),
      ("VirtualFinalClosure.GrowEntry","VirtualFinalClosure.GrowEntry","reentry_phase","reentryPhase",1),
      ("VirtualFinalClosure.MetaFields","VirtualFinalClosure.MetaFields","flag_preserved","flagPreserved",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","outside","outside",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual capacity-reentry composition {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual capacity-reentry composition {mod}/{key}"
/-- Every step of ONE full physical capacity-growth cycle, on the FROZEN
candidate. Arbitrary occupied assignment is physically returned to zero.
Arithmetic reexecution AFTER live q98 is a separate, still-open dependency. -/
private theorem grow_once (k P m S L H Q F p width : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (seenTrue : seen m=1) (fr : Frame T S L H Q F)
    (gap : H+Q+1 < F) (inside : p < S) (hole : T p=none)
    (suffix : ∀ i,p < i → i < S → ∃ b,T i=some b)
    (positive : 0 < width) (fit : F+5*width+(H-L-1)+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width (H-L-1) j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width (H-L-1) j < i →
      i < SerializedBody.delimiter F width (H-L-1) (j+1) → ∃ b,T i=some b) :
    ∃ t,t ≤ (F-p+5)+(width*(4*width+7)+2*(H-L-1)+14*width+27)+(F-S+3)+1 ∧
      GPath (M:=machine k) P t (C k 40 m p T)
        (node (control k (tableControl k 98) ⟨changeMeta 4 m,metaBound 4 m⟩)
          S (block (doubled T F width (H-L-1)) (L+1) (H-L-1) (some false))) ∧
      phase (changeMeta 4 m)=1 ∧ flag (changeMeta 4 m)=flag m := by
  have frameCopy:=fr
  obtain ⟨sl,lh,qp,arena,_s,_l,_h,_d0,_f,_reg,_assign,_marks,_gap⟩:=frameCopy
  have room : F+1 ≤ P := by omega
  have route:=toReset k P m S L H Q F p T hm seenTrue fr gap room inside hole suffix
  obtain ⟨d,price,doublePath⟩:=doubleBank k P m F width (H-L-1) T hm positive fit blank occupied
  let U:=doubled T F width (H-L-1)
  have framed : Frame U S L H Q F := protect fr (by
    intro i _lo hi
    dsimp only [U,doubled]
    rw [if_neg (by omega),if_neg (by omega)])
  have back:=returnSource k P m S L H Q F U hm framed room
  let V:=block U (L+1) (H-L-1) (some false)
  have framedCopy:=framed
  obtain ⟨_sl,_lh,_qp,_arena,endBlank,_l1,_h1,_d01,_f1,_reg1,_assign1,_marks1,_gap1⟩:=framedCopy
  have low : S < L+1 := by omega
  have atS : V S=none := (outside U (L+1) (H-L-1) S (some false) (Or.inl low)).trans endBlank
  have enter:=keep (M:=machine k) (P:=P) (nc k 88 m)
    (control k (tableControl k 98) ⟨changeMeta 4 m,metaBound 4 m⟩) S S V .stay
    (by omega)
    (by omega)
    (by rw [atS];exact reentryRow k m hm) rfl
  have path:=joinPath route doublePath
  have path:=joinPath path back
  have path:=joinPath path enter
  exact ⟨(F-p+5)+d+(F-S+3)+1,by omega,path,reentryPhase m,flagPreserved m 4⟩
#print axioms grow_once
end VirtualFinalClosure.GrowOnce
