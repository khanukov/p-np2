import VirtualFinalClosure.CapacityImage
import VirtualFinalClosure.GrowthCycle
import VirtualFinalClosure.RepeatEntry
namespace VirtualFinalClosure.CapacityCycle
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","image",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","digits","capacityDigits",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","tail","capacityTail",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","full_frame","fullFrame",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","doubled_image","doubledImage",1),
      ("VirtualFinalClosure.WorkspaceImage","VirtualFinalClosure.WorkspaceImage","cap_banks","capBanks",1),
      ("VirtualFinalClosure.GrowthCycle","VirtualFinalClosure.GrowthCycle","grow","grow",1),
      ("VirtualFinalClosure.RepeatEntry","VirtualFinalClosure.RepeatEntry","length_step","lengthStep",1),
      ("VirtualFinalClosure.RepeatEntry","VirtualFinalClosure.RepeatEntry","from_d2","route",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual repeated-growth execution interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual repeated-growth execution interface {mod}/{key}"
/-- One FULL phase1 cap -> real D2 route -> reset/copy/merge -> source return
and assignment paint -> native q98 reentry. Dirty parity counters are not
replaced by an assumed clean frame; their occupancy is proved from fullImage. -/
private theorem cycle (k N B S L n Q F width i : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (which : i=250 ∨ i=304) (positive : 0 < width)
    (fr : Frame T S L (L+n+1) Q F)
    (assignment : ∀ j,L < j → j < L+n+1 → T j=some false)
    (fit : F+5*width+n+7 < tapeLength N B) :
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (image T F width) L n F width) L n F width
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k i) m,⟨F+width+n+3,by omega⟩,fun j=>Y j.val⟩
    ∃ (t : Nat) (hs : S < tapeLength N B),
      t ≤ n+width+6+(width*(4*width+7)+2*n+14*width+27)+(F-S+3)+1 ∧
      (machine k).run t start=
        ⟨control k (tableControl k 98) m,⟨S,hs⟩,fun j=>image T F (2*width) j.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+5*width+n+7) := by
  intro Y start
  let P:=F+5*width+n+7
  have copyFr:=fr
  obtain ⟨sl,_lh,paid,room,_eof,_sep,_right,d0,_fence,_reg,_assn,_marks,_gap⟩:=copyFr
  have below : L+n+1 < F:=by omega
  have blank0 : image T F width (F+1)=none := by
    change (if F+1 < F+1 then _ else T (F+1))=none
    rw [if_neg (by omega)]
    exact d0
  obtain ⟨blank,occupied⟩:=capBanks (image T F width) L n F width below
    (capacityDigits T F width)
    (by intro j lo _hi;exact capacityTail T F width j lo) blank0
  have frY:=fullFrame T S L n Q F width fr
  have yd2 : Y (F+width+n+3)=none:=blank 2 (by decide)
  have headFit : F+width+n+3 ≤ P := by dsimp only [P];omega
  have enter:=keep (M:=machine k) (P:=P) (control k (tableControl k i) m) (nc k 0 m.val)
    (F+width+n+3) (F+width+n+3) Y .stay headFit headFit
    (by rw [yd2];exact lengthStep k i m.val m.isLt ph which) rfl
  have seek:=route k P F width n m.val Y m.isLt ph headFit
    (blank 0 (by decide)) (blank 1 (by decide)) (blank 2 (by decide))
    (by intro j lo hi;exact occupied 0 (by decide) j lo hi)
    (by intro j lo hi;exact occupied 1 (by decide) j lo hi)
  obtain ⟨v,vp,grown⟩:=grow k P m.val S L (L+n+1) Q F width Y m.isLt ph frY positive
    (by dsimp only [P];omega)
    (by intro j hj;simpa only [show (L+n+1)-L-1=n by omega] using blank j hj)
    (by
      intro j hj p lo hi
      exact occupied j hj p (by simpa only [show (L+n+1)-L-1=n by omega] using lo)
        (by simpa only [show (L+n+1)-L-1=n by omega] using hi))
  rw [show (L+n+1)-L-1=n by omega] at vp grown
  rw [doubledImage T L n F width below assignment] at grown
  have joined:=joinPath (joinPath enter seek) grown
  have actual:=execute (N:=N) (B:=B) joined fit
  have heads:=through (N:=N) (B:=B) joined fit
  refine ⟨1+(n+width+5)+v,by omega,by omega,?_,?_⟩
  · exact actual
  · exact heads
#print axioms cycle
end VirtualFinalClosure.CapacityCycle
