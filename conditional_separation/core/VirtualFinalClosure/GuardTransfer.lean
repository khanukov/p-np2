import VirtualFinalClosure.GuardImage
import VirtualFinalClosure.GuardCross
namespace VirtualFinalClosure.GuardTransfer
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PostWeight.Kernel","PostWeight","Banks","Banks",(2:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",(0:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","digit","digit",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","occupied","occupied",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","take4","take4",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","add3","add3",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","transferDec4","dec4",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","transferInc3","inc3",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","transferAtD3","to4",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","transferTo3","to3",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","transferBack4","back4",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","transferDone4","done4",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","put","put",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",(0:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal BE transfer interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal BE transfer interface {mod}/{key}"
/-- Entire native transfer loop, preserving all actual source/exterior data.
This is the copy-back phase consumed by each BE doubling iteration. -/
private theorem loop (k P m L n F width a b c d : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Banks T L n F width)
    (fit : F+5*width+n+7 ≤ P) (capacity : b+c ≤ width)
    (b0 : ∀ i,F+1 < i → i < F+width+2 → ∃ v,T i=some v)
    (b1 : ∀ i,F+width+2 < i → i < F+width+n+3 → ∃ v,T i=some v) :
    ∃ t,t ≤ c*(6*width+13)+3 ∧
      GPath (M:=machine k) P t
        (C k 123 m (F+3*width+n+5) (image T L n F width a b c d))
        (C k 134 m (F+3*width+n+5) (image T L n F width a (b+c) 0 d)) := by
  induction c generalizing b with
  | zero=>
    have blank:=delimiters fr a b 0 d
    have part:=dec4 k P m (F+3*width+n+5) width 0 (image T L n F width a b 0 d)
      hm (by omega) (by omega) (blank 4 (by decide)) (by have h:=blank 5 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
      (by intro i lo hi;exact digit fr a b 0 d 4 i (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
    refine ⟨3,by omega,?_⟩
    simpa only [Nat.mul_zero,Nat.zero_add,if_pos rfl,Nat.add_zero] using part
  | succ c ih=>
    let A:=image T L n F width a b (c+1) d
    let B:=image T L n F width a b c d
    let D:=image T L n F width a (b+1) c d
    have blankA:=delimiters fr a b (c+1) d
    have dec:=dec4 k P m (F+3*width+n+5) width (c+1) A hm (by omega) (by omega)
      (blankA 4 (by decide)) (by have h:=blankA 5 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
      (by intro i lo hi;exact digit fr a b (c+1) d 4 i (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
    have update4 : put A (F+3*width+n+5+(c+1)) (some false)=B:=by
      simpa only [Nat.add_sub_cancel] using take4 fr a b (c+1) d (by omega) (by omega)
    simp only [if_neg (by omega : ¬c+1=0),update4] at dec
    have forward:=to3 k P m F width n B hm fit (delimiters fr a b c d) (occupied fr b0 b1 a b c d)
    have blankB:=delimiters fr a b c d
    have inc:=inc3 k P m (F+2*width+n+4) width b B hm (by omega) (by omega)
      (blankB 3 (by decide)) (by have h:=blankB 4 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
      (by intro i lo hi;exact digit fr a b c d 3 i (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
    have update3 : put B (F+2*width+n+4+b+1) (some true)=D:=add3 fr a b c d (by omega)
    rw [if_pos (by omega : b < width),if_pos (by omega : b < width),update3] at inc
    have returning:=back4 k P m F width n D hm fit (delimiters fr a (b+1) c d) (occupied fr b0 b1 a (b+1) c d)
    obtain ⟨t,tp,rest⟩:=ih (b+1) (by omega)
    have joined:=joinPath (joinPath (joinPath (joinPath dec forward) inc) returning) rest
    have sum : b+1+c=b+(c+1):=by omega
    rw [sum] at joined
    refine ⟨(2*(c+1)+3)+(width+2)+(2*b+3)+(width+2)+t,?_,joined⟩
    have step : (2*(c+1)+3)+(width+2)+(2*b+3)+(width+2) ≤ 6*width+13:=by omega
    nlinarith only [tp,step]
private theorem prepared (k P m L n F width a b c d : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Banks T L n F width)
    (fit : F+5*width+n+7 ≤ P) (capacity : b+c ≤ width)
    (b0 : ∀ i,F+1 < i → i < F+width+2 → ∃ v,T i=some v)
    (b1 : ∀ i,F+width+2 < i → i < F+width+n+3 → ∃ v,T i=some v) :
    ∃ t,t ≤ (c+1)*(16*width+32) ∧
      GPath (M:=machine k) P t
        (C k 121 m (F+2*width+n+4) (image T L n F width a b c d))
        (C k 136 m (F+2*width+n+4) (image T L n F width a (b+c) 0 d)) := by
  have enter:=to4 k P m F width n (image T L n F width a b c d) hm fit
    (delimiters fr a b c d) (occupied fr b0 b1 a b c d)
  obtain ⟨t,tp,middle⟩:=loop k P m L n F width a b c d T hm fr fit capacity b0 b1
  have finish:=done4 k P m F width n (image T L n F width a (b+c) 0 d) hm fit
    (delimiters fr a (b+c) 0 d) (occupied fr b0 b1 a (b+c) 0 d)
  exact ⟨(width+2)+t+(width+2),by nlinarith only [tp,Nat.zero_le c,Nat.zero_le width],joinPath (joinPath enter middle) finish⟩
#print axioms loop
#print axioms prepared
end VirtualFinalClosure.GuardTransfer
