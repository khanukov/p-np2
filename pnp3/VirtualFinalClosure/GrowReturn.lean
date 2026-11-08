import VirtualFinalClosure.GrowDouble
import VirtualFinalClosure.SourceWalk
namespace VirtualFinalClosure.GrowReturn
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
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
  for key in ["r081_0","r082_1","r083_0","r083_2","r084_0","r084_2","r085_0","r085_1","r085_2","r086_0","r087_0","r087_1","r087_2"] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.GrowStepRows." && name.toString.endsWith (".VirtualFinalClosure.GrowStepRows."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank row {key}"
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.PaintLeft","VirtualFinalClosure.PaintLeft","paint_left","paintLeft",1),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","outside","outside",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual growth-return interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual growth-return interface {mod}/{key}"
private theorem row85 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 85 m) (some b)=(nc k 85 m,some false,.left) := by
  cases b
  · exact r085_1 k m hm
  · exact r085_2 k m hm
private theorem row87 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 87 m) (some b)=(nc k 87 m,some b,.left) := by
  cases b
  · exact r087_1 k m hm
  · exact r087_2 k m hm
/-- After real doubling the frozen rows return across the original paid arena,
PHYSICALLY clear assignment cells, and reach actual source EOF. -/
private theorem return_source (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (fit : F+1 ≤ P) :
    GPath (M:=machine k) P (F-S+3) (C k 81 m (F+1) T)
      (C k 88 m S (block T (L+1) (H-L-1) (some false))) := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,d0,fence,register,assignment,tally,gap⟩:=fr
  let n:=H-L-1
  let z:=L-S-1
  let g:=F-(H+Q)-1
  let U:=block T (L+1) n (some false)
  have unchanged (i : Nat) (hi : i ≤ L) : U i=T i :=
    outside T (L+1) n i (some false) (Or.inl (by omega))
  have first:=keep (M:=machine k) (P:=P) (nc k 81 m) (nc k 82 m) (F+1) F T .left
    fit (by omega) (by rw [d0];exact r081_0 k m hm) (by dsimp only [dest];omega)
  have second:=keep (M:=machine k) (P:=P) (nc k 82 m) (nc k 83 m) F (F-1) T .left
    (by omega) (by omega) (by rw [fence];exact r082_1 k m hm) rfl
  have gaps:=sweepL (M:=machine k) (P:=P) (nc k 83 m) T (H+Q) g (by dsimp only [g];omega) (by
    intro i lo hi
    rw [gap i lo (by dsimp only [g] at hi;omega)]
    exact r083_0 k m hm)
  rw [show H+Q+g=F-1 by dsimp only [g];omega] at gaps
  have toTally:=keep (M:=machine k) (P:=P) (nc k 83 m) (nc k 84 m) (H+Q) (H+(Q-1)) T .left
    (by omega) (by omega) (by rw [tally _ (by omega) le_rfl];exact r083_2 k m hm)
    (by dsimp only [dest];omega)
  have paid:=sweepL (M:=machine k) (P:=P) (nc k 84 m) T H (Q-1) (by omega) (by
    intro i lo hi
    rw [tally i lo (by omega)]
    exact r084_2 k m hm)
  have toAssign:=keep (M:=machine k) (P:=P) (nc k 84 m) (nc k 85 m) H (H-1) T .left
    (by omega) (by omega) (by rw [h0];exact r084_0 k m hm) rfl
  have paint:=paintLeft (nc k 85 m) P L n T (some false) (by dsimp only [n];omega)
    (by intro i lo hi;exact assignment i lo (by dsimp only [n] at hi;omega)) (row85 k m hm)
  rw [show L+n=H-1 by dsimp only [n];omega] at paint
  have uL : U L=none := (unchanged L le_rfl).trans l0
  have atL:=keep (M:=machine k) (P:=P) (nc k 85 m) (nc k 86 m) L L U .stay
    (by omega) (by omega) (by rw [uL];exact r085_0 k m hm) rfl
  have toReg:=keep (M:=machine k) (P:=P) (nc k 86 m) (nc k 87 m) L (L-1) U .left
    (by omega) (by omega) (by rw [uL];exact r086_0 k m hm) rfl
  have reg:=sweepL (M:=machine k) (P:=P) (nc k 87 m) U S z (by dsimp only [z];omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=register i lo (by dsimp only [z] at hi;omega)
    rw [unchanged i (by dsimp only [z] at hi;omega),cell]
    exact row87 k m hm b)
  rw [show S+z=L-1 by dsimp only [z];omega] at reg
  have uS : U S=none := (unchanged S (by omega)).trans s0
  have ending:=keep (M:=machine k) (P:=P) (nc k 87 m) (nc k 88 m) S S U .stay
    (by omega) (by omega) (by rw [uS];exact r087_0 k m hm) rfl
  have path:=joinPath first second
  have path:=joinPath path gaps
  have path:=joinPath path toTally
  have path:=joinPath path paid
  have path:=joinPath path toAssign
  have path:=joinPath path paint
  have path:=joinPath path atL
  have path:=joinPath path toReg
  have path:=joinPath path reg
  have path:=joinPath path ending
  convert path using 1;dsimp only [g,n,z];omega
#print axioms row85
#print axioms row87
#print axioms return_source
end VirtualFinalClosure.GrowReturn
