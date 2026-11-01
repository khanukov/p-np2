import VirtualFinalClosure.GrowMerge
namespace VirtualFinalClosure.GrowDouble
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
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GrowReset","VirtualFinalClosure.GrowReset","reset","reset",(1:Nat)),
      ("VirtualFinalClosure.GrowReset","VirtualFinalClosure.GrowReset","stage","resetImage",0),
      ("VirtualFinalClosure.GrowReset","VirtualFinalClosure.GrowReset","D","resetD",0),
      ("VirtualFinalClosure.GrowSeek","VirtualFinalClosure.GrowSeek","seek","seek",1),
      ("VirtualFinalClosure.GrowImage","VirtualFinalClosure.GrowImage","copying","copying",1),
      ("VirtualFinalClosure.GrowImage","VirtualFinalClosure.GrowImage","image","copyImage",0),
      ("VirtualFinalClosure.GrowImage","VirtualFinalClosure.GrowImage","outside","copyOutside",1),
      ("VirtualFinalClosure.GrowMerge","VirtualFinalClosure.GrowMerge","finish_scan","finishScan",1),
      ("VirtualFinalClosure.GrowMerge","VirtualFinalClosure.GrowMerge","merge","merge",1),
      ("VirtualFinalClosure.GrowMerge","VirtualFinalClosure.GrowMerge","grown","grown",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual whole-doubling interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual whole-doubling interface {mod}/{key}"
private def doubled (T : Nat → Option Bool) (F width n : Nat) : Nat → Option Bool := fun i=>
  if F+1 < i ∧ i < F+2*width+2 then some true else
  if F+2*width+2 ≤ i ∧ i ≤ F+5*width+n+7 then none else T i
private def doubled_type : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Option Bool := doubled
private theorem reset_cells (T : Nat → Option Bool) (F width n i : Nat)
    (lo : F+1 < i) (hi : i < F+width+2) : resetImage T F width n 6 i=some false := by
  dsimp only [resetImage,resetD,SerializedBody.delimiter]
  rw [if_neg (by decide : ¬(6:Nat)=0),if_pos ⟨lo,hi⟩]
private theorem reset_gap (T : Nat → Option Bool) (F width n i : Nat)
    (endBlank : T (F+5*width+n+7)=none)
    (lo : F+width+2 ≤ i) (hi : i ≤ F+5*width+n+7)
    (oldBlank : T (F+width+2)=none) : resetImage T F width n 6 i=none := by
  dsimp only [resetImage,resetD,SerializedBody.delimiter]
  rw [if_neg (by decide : ¬(6:Nat)=0),if_neg (by omega)]
  by_cases left : i=F+width+2
  · rw [if_neg (by omega),left,oldBlank]
  · by_cases right : i=F+5*width+n+7
    · rw [if_neg (by omega),right,endBlank]
    · rw [if_pos (by omega)]
private theorem full_image (T : Nat → Option Bool) (F width n : Nat) (pos : 0 < width)
    (d1 : T (F+width+2)=none) (d6 : T (F+5*width+n+7)=none) :
    grown (copyImage (resetImage T F width n 6) (F+1) width width) (F+1) width=
      doubled T F width n := by
  funext i
  by_cases bank : F+1 < i ∧ i < F+2*width+2
  · dsimp only [grown,doubled]
    rw [if_pos (by omega),if_pos bank]
  · dsimp only [grown,doubled]
    rw [if_neg (by omega),if_neg bank]
    by_cases newEnd : i=F+2*width+2
    · rw [if_pos (by omega),if_pos (by omega)]
    · rw [if_neg (by omega)]
      by_cases erased : F+2*width+2 ≤ i ∧ i ≤ F+5*width+n+7
      · rw [if_pos erased,copyOutside _ (F+1) width width i (Or.inr (Or.inl (by omega)))]
        exact reset_gap T F width n i d6 (by omega) erased.2 d1
      · rw [if_neg erased]
        rw [copyOutside _ (F+1) width width i (by omega)]
        dsimp only [resetImage,resetD,SerializedBody.delimiter]
        rw [if_neg (by decide : ¬(6:Nat)=0),if_neg (by omega),if_neg (by omega)]
/-- Complete six-bank reset, physical scan/copy loop, exhausted-marker scan,
and real delimiter merge. No runtime operand is installed by this theorem. -/
private theorem double (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (positive : 0 < width) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    ∃ t,t ≤ width*(4*width+7)+2*n+14*width+27 ∧
      GPath (M:=machine k) P t (C k 52 m (F+1) T)
        (C k 81 m (F+1) (doubled T F width n)) := by
  let B:=F+1
  let E:=F+5*width+n+7
  let U:=resetImage T F width n 6
  let V:=copyImage U B width width
  have d0 : T B=none := blank 0 (by decide)
  have d1 : T (F+width+2)=none := blank 1 (by decide)
  have d6 : T E=none := blank 6 (by decide)
  have resetPath:=reset k P m F width n T hm fit blank occupied
  have uB : U B=none := by
    dsimp only [U,resetImage,resetD,SerializedBody.delimiter,B]
    rw [if_neg (by decide : ¬(6:Nat)=0),if_neg (by omega),if_neg (by omega)]
    exact d0
  have old : ∀ i,B < i → i < B+width+1 → U i=some false := by
    intro i lo hi
    exact reset_cells T F width n i lo (by dsimp only [B] at hi;omega)
  have gap : ∀ i,B+width+1 ≤ i → i ≤ E → U i=none := by
    intro i lo hi
    exact reset_gap T F width n i d6 (by dsimp only [B] at lo;omega) hi d1
  have seekPath:=seek k P m B width E U hm positive (by dsimp only [B,E];omega) fit uB
    (by intro i lo hi;exact old i lo (by omega)) gap
  obtain ⟨t,price,copyPath⟩:=copying k P m B width U hm (by dsimp only [B,E] at *;omega)
    uB (gap _ le_rfl (by dsimp only [B,E];omega)) old
    (by intro i lo hi;exact gap i lo.le (by dsimp only [B,E] at *;omega))
  have vB : V B=none := (copyOutside U B width width B (Or.inl le_rfl)).trans uB
  have vD : V (B+width+1)=none :=
    (copyOutside U B width width _ (Or.inr (Or.inr rfl))).trans (gap _ le_rfl (by dsimp only [B,E];omega))
  have bank : ∀ i,B < i → i < B+width+1 → V i=some true := by
    intro i lo hi
    dsimp only [V,copyImage]
    rw [if_pos ⟨lo,hi⟩,decide_eq_true (by omega)]
  have temp : ∀ i,B+width+1 < i → i ≤ B+2*width+1 → V i=some false := by
    intro i lo hi
    dsimp only [V,copyImage]
    rw [if_neg (by omega),if_pos (by omega)]
  have last : V (B+2*width+2)=none :=
    (copyOutside U B width width _ (Or.inr (Or.inl (by omega)))).trans
      (gap _ (by omega) (by dsimp only [B,E];omega))
  have finishPath:=finishScan k P m B width V hm (by dsimp only [B,E] at *;omega) vB vD bank
  have mergePath:=merge k P m B width V hm positive (by dsimp only [B,E] at *;omega) vB vD last bank temp
  have joined:=joinPath (joinPath (joinPath (joinPath resetPath seekPath) copyPath) finishPath) mergePath
  have final : grown V B width=doubled T F width n := full_image T F width n positive d1 d6
  rw [final] at joined
  refine ⟨n+5*width+12+(E-(B+width+1)+width+2)+t+(width+2)+(3*width+6),?_,joined⟩
  dsimp only [B,E]
  omega
#print axioms doubled_type
#print axioms reset_cells
#print axioms reset_gap
#print axioms full_image
#print axioms double
end VirtualFinalClosure.GrowDouble
