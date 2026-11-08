import VirtualFinalClosure.SourceShift
namespace VirtualFinalClosure.SourceRound
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protectedFrame",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","mark_decrement","decrement",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","paid_to_source","toSource",1),
      ("VirtualFinalClosure.SourceReturn","VirtualFinalClosure.SourceReturn","source_to_paid","toPaid",1),
      ("VirtualFinalClosure.SourceShift","VirtualFinalClosure.SourceShift","first_cell","firstCell",1),
      ("VirtualFinalClosure.SourceShift","VirtualFinalClosure.SourceShift","previous_cell","previousCell",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","changed_bound","bitBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong physical source-round declaration {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique source-round interface {mod}/{key}"
/-- This image is specified BEFORE the round. The bank decrement and the two
possible source writes are the actual literal writes of the frozen program. -/
private def nextTape (T : Nat → Option Bool) (F v h S : Nat) (oldBit : Bool) : Nat → Option Bool :=
  let U:=put T (F+1+v) (some false)
  let V:=if h=S then U else put U h (some oldBit)
  put V (h-1) none
private theorem positive_round (k P m S L H Q F r v h : Nat)
    (T : Nat → Option Bool) (oldBit b : Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (gap : H+Q+1 < F)
    (hv : v ≤ r) (positive : 0 < v) (fit : F+r+2 ≤ P)
    (last : T (F+r+2)=none)
    (digits : ∀ i,F+1  <  i → i  <  F+r+2 → T i=some (decide (i ≤ F+1+v)))
    (hpos : 0 < h) (range : h ≤ S)
    (eofMode : h=S → sourceMode m=2)
    (liveMode : h < S → sourceMode m=(if oldBit then 1 else 0))
    (hole : h < S → T h=none) (selected : T (h-1)=some b)
    (suffix : ∀ i,h  <  i → i  <  S → ∃ bit,T i=some bit) :
    GPath (M:=machine k) P
      (2*v+3+(F-S+3)+(if h=S then 4 else 2*(S-h)+5)+(F-S+3))
      (C k 6 m (F+1) T)
      (C k 6 (changeMode (if b then 2 else 1) m) (F+1) (nextTape T F v h S oldBit)) := by
  have copyFrame:=fr
  obtain ⟨sl,lh,_qp,room,endBlank,_l0,_h0,sep,_ff,_reg,_assign,_tally,_gap⟩:=copyFrame
  let U:=put T (F+1+v) (some false)
  have sameU (i : Nat) (lo : S ≤ i) (hi : i ≤ F+1) : U i=T i := by
    dsimp only [U,put]
    rw [if_neg (by omega)]
  have sameBelow (i : Nat) (hi : i ≤ S) : U i=T i := by
    dsimp only [U,put]
    rw [if_neg (by omega)]
  have frameU : Frame U S L H Q F := protectedFrame fr sameU
  have count:=decrement k P m (F+1) r v T hm hv (by omega) sep
    (by simpa only [show F+1+r+1=F+r+2 by omega] using last) (by
      intro i lo hi
      exact digits i lo (by omega))
  simp only [if_neg (by omega : v ≠ 0)] at count
  have paid:=toSource k P m S L H Q F U hm frameU (by omega)
  let V:=nextTape T F v h S oldBit
  have shift : GPath (M:=machine k) P (if h=S then 4 else 2*(S-h)+5)
      (C k 17 m S U) (C k 24 (changeMode (if b then 2 else 1) m) S V) := by
    by_cases atEOF : h=S
    · have first:=firstCell k P m S U b hm (eofMode atEOF) (by omega) (by omega)
        ((sameBelow S le_rfl).trans endBlank)
        ((sameBelow (S-1) (by omega)).trans (by simpa only [atEOF] using selected))
      change GPath (M:=machine k) P _ _ _
      simpa only [atEOF,ite_true,V,nextTape] using first
    · have inside : h < S := by omega
      have later:=previousCell k P m S h U oldBit b hm (liveMode inside) hpos inside (by omega)
        ((sameBelow S le_rfl).trans endBlank) ((sameBelow h range).trans (hole inside))
        ((sameBelow (h-1) (by omega)).trans selected) (by
          intro i lo hi
          obtain ⟨bit,cell⟩:=suffix i lo hi
          exact ⟨bit,(sameBelow i hi.le).trans cell⟩)
      simpa only [atEOF,ite_false,V,nextTape] using later
  have sameV (i : Nat) (lo : S ≤ i) (hi : i ≤ F+1) : V i=U i := by
    change (if i=h-1 then none else (if h=S then U else put U h (some oldBit)) i)=U i
    rw [if_neg (by omega)]
    by_cases atEOF : h=S
    · rw [if_pos atEOF]
    · rw [if_neg atEOF]
      change (if i=h then some oldBit else U i)=U i
      rw [if_neg (by omega)]
  have frameV : Frame V S L H Q F := protectedFrame frameU sameV
  have back:=toPaid k P (changeMode (if b then 2 else 1) m) S L H Q F V
    (bitBound m b) frameV gap (by omega)
  exact joinPath (joinPath (joinPath count paid) shift) back
#print axioms nextTape
#print axioms positive_round
end VirtualFinalClosure.SourceRound
