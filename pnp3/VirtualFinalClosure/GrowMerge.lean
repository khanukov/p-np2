import VirtualFinalClosure.GrowImage
import VirtualFinalClosure.PaintLeft
namespace VirtualFinalClosure.GrowMerge
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
  for key in ["r067_0","r068_0","r068_2","r074_0","r075_0","r075_1","r076_0","r077_1","r078_0","r078_1","r078_2","r079_0","r080_0","r080_1","r080_2"] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.GrowStepRows." && name.toString.endsWith (".VirtualFinalClosure.GrowStepRows."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank row {key}"
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.PaintLeft","VirtualFinalClosure.PaintLeft","paint_left","paintLeft",(1:Nat)),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","outside","outside",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual merge-writing interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual merge-writing interface {mod}/{key}"
private def grown (T : Nat → Option Bool) (B width : Nat) : Nat → Option Bool := fun i=>
  if B < i ∧ i < B+2*width+1 then some true else if i=B+2*width+1 then none else T i
private def grown_type : (Nat → Option Bool) → Nat → Nat → Nat → Option Bool := grown
private theorem merge_image (T : Nat → Option Bool) (B width : Nat) (pos : 0 < width) :
    block (put (block (put T (B+width+1+width) none) (B+width+1+1) (width-1) (some true))
      (B+width+1) (some true)) (B+1) width (some true)=grown T B width := by
  funext i
  dsimp only [block,put,grown]
  split_ifs <;> first | rfl | omega
private theorem row78 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 78 m) (some b)=(nc k 78 m,some true,.left) := by
  cases b
  · exact r078_1 k m hm
  · exact r078_2 k m hm
private theorem row80 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 80 m) (some b)=(nc k 80 m,some true,.left) := by
  cases b
  · exact r080_1 k m hm
  · exact r080_2 k m hm
/-- The exhausted old marker scan is executed, rather than jumping to merge. -/
private theorem finish_scan (k P m B width : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : B+width+1 ≤ P) (base : T B=none) (sep : T (B+width+1)=none)
    (digits : ∀ i,B < i → i < B+width+1 → T i=some true) :
    GPath (M:=machine k) P (width+2) (C k 67 m B T) (C k 74 m (B+width+1) T) := by
  have enter:=keep (M:=machine k) (P:=P) (nc k 67 m) (nc k 68 m) B (B+1) T .right
    (by omega) (by omega) (by rw [base];exact r067_0 k m hm) rfl
  have scan:=sweepR (M:=machine k) (P:=P) (nc k 68 m) T (B+1) width (by omega) (by
    intro i lo hi
    rw [digits i (by omega) (by omega)]
    exact r068_2 k m hm)
  rw [show B+1+width=B+width+1 by omega] at scan
  have leave:=keep (M:=machine k) (P:=P) (nc k 68 m) (nc k 74 m) (B+width+1) (B+width+1) T .stay
    fit fit (by rw [sep];exact r068_0 k m hm) rfl
  have path:=joinPath (joinPath enter scan) leave
  convert path using 1;omega
/-- Real delimiter merge, including removal of the final temporary cell. -/
private theorem merge (k P m B width : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (pos : 0 < width) (fit : B+2*width+2 ≤ P)
    (base : T B=none) (sep : T (B+width+1)=none) (last : T (B+2*width+2)=none)
    (digits : ∀ i,B < i → i < B+width+1 → T i=some true)
    (temp : ∀ i,B+width+1 < i → i ≤ B+2*width+1 → T i=some false) :
    GPath (M:=machine k) P (3*width+6) (C k 74 m (B+width+1) T)
      (C k 81 m B (grown T B width)) := by
  let D:=B+width+1
  let U:=put T (D+width) none
  let V:=block U (D+1) (width-1) (some true)
  let Z:=put V D (some true)
  have enter:=keep (M:=machine k) (P:=P) (nc k 74 m) (nc k 75 m) D (D+1) T .right
    (by omega) (by omega) (by rw [sep];exact r074_0 k m hm) rfl
  have scan:=sweepR (M:=machine k) (P:=P) (nc k 75 m) T (D+1) width (by omega) (by
    intro i lo hi
    rw [temp i (by omega) (by omega)]
    exact r075_1 k m hm)
  have endBlank : T (D+1+width)=none := by rw [show D+1+width=B+2*width+2 by omega,last]
  have turn:=keep (M:=machine k) (P:=P) (nc k 75 m) (nc k 76 m) (D+1+width) (D+width+1) T .stay
    (by omega) (by omega) (by rw [endBlank];exact r075_0 k m hm) (by dsimp only [dest];omega)
  have toLast:=keep (M:=machine k) (P:=P) (nc k 76 m) (nc k 77 m) (D+width+1) (D+width) T .left
    (by omega) (by omega) (by rw [show D+width+1=D+1+width by omega,endBlank];exact r076_0 k m hm)
    (by dsimp only [dest];omega)
  have remove:=hop (M:=machine k) (P:=P) (nc k 77 m) (nc k 78 m) (D+width) (D+(width-1)) T none .left
    (by omega) (by omega) (by rw [temp _ (by omega) (by omega)];exact r077_1 k m hm)
    (by dsimp only [dest];omega)
  have paintTemp:=paintLeft (nc k 78 m) P D (width-1) U (some true) (by omega) (by
    intro i lo hi
    change ∃ b,(if i=D+width then none else T i)=some b
    rw [if_neg (by omega)]
    exact ⟨false,temp i (by omega) (by omega)⟩) (row78 k m hm)
  have lowV (i : Nat) (hi : i ≤ D) : V i=T i := by
    dsimp only [V]
    rw [outside U (D+1) (width-1) i (some true) (Or.inl (by omega))]
    change (if i=D+width then none else T i)=T i
    rw [if_neg (by omega)]
  have vD : V D=none := (lowV D le_rfl).trans sep
  have atSep:=keep (M:=machine k) (P:=P) (nc k 78 m) (nc k 79 m) D D V .stay
    (by omega) (by omega) (by rw [vD];exact r078_0 k m hm) rfl
  have fill:=hop (M:=machine k) (P:=P) (nc k 79 m) (nc k 80 m) D (B+width) V (some true) .left
    (by omega) (by omega) (by rw [vD];exact r079_0 k m hm) (by dsimp only [dest];omega)
  have paintOld:=paintLeft (nc k 80 m) P B width Z (some true) (by omega) (by
    intro i lo hi
    change ∃ b,(if i=D then some true else V i)=some b
    rw [if_neg (by omega),lowV i (by omega)]
    exact ⟨true,digits i lo (by omega)⟩) (row80 k m hm)
  let out:=block Z (B+1) width (some true)
  have outBase : out B=none := by
    dsimp only [out]
    rw [outside Z (B+1) width B (some true) (Or.inl (by omega))]
    change (if B=D then some true else V B)=none
    rw [if_neg (by omega),lowV B (by omega),base]
  have endStep:=keep (M:=machine k) (P:=P) (nc k 80 m) (nc k 81 m) B B out .stay
    (by omega) (by omega) (by rw [outBase];exact r080_0 k m hm) rfl
  have path:=joinPath enter scan
  have path:=joinPath path turn
  have path:=joinPath path toLast
  have path:=joinPath path remove
  have path:=joinPath path paintTemp
  have path:=joinPath path atSep
  have path:=joinPath path fill
  have path:=joinPath path paintOld
  have path:=joinPath path endStep
  have image : out=grown T B width := merge_image T B width pos
  rw [image] at path
  have price : 1+width+1+1+1+(width-1)+1+1+width+1=3*width+6 := by omega
  simpa only [price] using path
#print axioms grown_type
#print axioms merge_image
#print axioms row78
#print axioms row80
#print axioms finish_scan
#print axioms merge
end VirtualFinalClosure.GrowMerge
