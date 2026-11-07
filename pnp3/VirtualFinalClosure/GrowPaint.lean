import VirtualFinalClosure.GrowRows
namespace VirtualFinalClosure.GrowPaint
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  let names:=(List.range 6).flatMap fun j=>
    let first:=52+2*j;let scan:=first+1
    [("r"++toString first++"_0","e"++toString j),
      ("r"++toString scan++"_0","l"++toString j),
      ("r"++toString scan++"_1","f"++toString j),
      ("r"++toString scan++"_2","t"++toString j)]
  for (key,aliasName) in names do
    let padded:=key.replace "r5" "r05" |>.replace "r6" "r06"
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.GrowRows." &&
      name.toString.endsWith (".VirtualFinalClosure.GrowRows."++padded)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal clearing/painting row {padded}"
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","paint_right","paintRight",1),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","outside","outside",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual grow paint path interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual grow paint path interface {mod}/{key}"
private theorem enter (k m j : Nat) (hm : m < 144) (hj : j < 6) :
    (machine k).step (nc k (52+2*j) m) none=(nc k (53+2*j) m,none,.right) := by
  interval_cases j
  · simpa only [show 52+2*0=52 by decide,show 53+2*0=53 by decide] using e0 k m hm
  · simpa only [show 52+2*1=54 by decide,show 53+2*1=55 by decide] using e1 k m hm
  · simpa only [show 52+2*2=56 by decide,show 53+2*2=57 by decide] using e2 k m hm
  · simpa only [show 52+2*3=58 by decide,show 53+2*3=59 by decide] using e3 k m hm
  · simpa only [show 52+2*4=60 by decide,show 53+2*4=61 by decide] using e4 k m hm
  · simpa only [show 52+2*5=62 by decide,show 53+2*5=63 by decide] using e5 k m hm
private theorem leave (k m j : Nat) (hm : m < 144) (hj : j < 6) :
    (machine k).step (nc k (53+2*j) m) none=(nc k (54+2*j) m,none,.stay) := by
  interval_cases j
  · simpa only [show 53+2*0=53 by decide,show 54+2*0=54 by decide] using l0 k m hm
  · simpa only [show 53+2*1=55 by decide,show 54+2*1=56 by decide] using l1 k m hm
  · simpa only [show 53+2*2=57 by decide,show 54+2*2=58 by decide] using l2 k m hm
  · simpa only [show 53+2*3=59 by decide,show 54+2*3=60 by decide] using l3 k m hm
  · simpa only [show 53+2*4=61 by decide,show 54+2*4=62 by decide] using l4 k m hm
  · simpa only [show 53+2*5=63 by decide,show 54+2*5=64 by decide] using l5 k m hm
private theorem paint (k m j : Nat) (hm : m < 144) (hj : j < 6) (b : Bool) :
    (machine k).step (nc k (53+2*j) m) (some b)=
      (nc k (53+2*j) m,(if j=0 then some false else none),.right) := by
  interval_cases j <;> cases b
  · simpa only [show 53+2*0=53 by decide,if_pos (show (0:Nat)=0 from rfl)] using f0 k m hm
  · simpa only [show 53+2*0=53 by decide,if_pos (show (0:Nat)=0 from rfl)] using t0 k m hm
  · simpa only [show 53+2*1=55 by decide,if_neg (by decide : ¬(1:Nat)=0)] using f1 k m hm
  · simpa only [show 53+2*1=55 by decide,if_neg (by decide : ¬(1:Nat)=0)] using t1 k m hm
  · simpa only [show 53+2*2=57 by decide,if_neg (by decide : ¬(2:Nat)=0)] using f2 k m hm
  · simpa only [show 53+2*2=57 by decide,if_neg (by decide : ¬(2:Nat)=0)] using t2 k m hm
  · simpa only [show 53+2*3=59 by decide,if_neg (by decide : ¬(3:Nat)=0)] using f3 k m hm
  · simpa only [show 53+2*3=59 by decide,if_neg (by decide : ¬(3:Nat)=0)] using t3 k m hm
  · simpa only [show 53+2*4=61 by decide,if_neg (by decide : ¬(4:Nat)=0)] using f4 k m hm
  · simpa only [show 53+2*4=61 by decide,if_neg (by decide : ¬(4:Nat)=0)] using t4 k m hm
  · simpa only [show 53+2*5=63 by decide,if_neg (by decide : ¬(5:Nat)=0)] using f5 k m hm
  · simpa only [show 53+2*5=63 by decide,if_neg (by decide : ¬(5:Nat)=0)] using t5 k m hm
/-- Six actual native finite phases, including zero-width bank1. Bank0 is
painted OCCUPIED false; the other five banks are erased to NONE. -/
private theorem paint_bank (k P m j base width : Nat) (T : Nat  →  Option Bool)
    (hm : m < 144) (hj : j < 6) (fit : base+width+1 ≤ P)
    (start : T base=none) (finish : T (base+width+1)=none)
    (occupied : ∀ i,base < i  →  i < base+width+1  →  ∃ b,T i=some b) :
    GPath (M:=machine k) P (width+2)
      (C k (52+2*j) m base T)
      (C k (54+2*j) m (base+width+1)
        (block T (base+1) width (if j=0 then some false else none))) := by
  let out:Option Bool:=if j=0 then some false else none
  have entry:=keep (M:=machine k) (P:=P) (nc k (52+2*j) m) (nc k (53+2*j) m)
    base (base+1) T .right (by omega) (by omega) (by rw [start];exact enter k m j hm hj) rfl
  have scan:=paintRight (nc k (53+2*j) m) P (base+1) width T out (by omega)
    (by intro i lo hi;exact occupied i (by omega) (by omega)) (paint k m j hm hj)
  rw [show base+1+width=base+width+1 by omega] at scan
  let U:=block T (base+1) width out
  have blank : U (base+width+1)=none :=
    (outside T (base+1) width (base+width+1) out (Or.inr (by omega))).trans finish
  have ending:=keep (M:=machine k) (P:=P) (nc k (53+2*j) m) (nc k (54+2*j) m)
    (base+width+1) (base+width+1) U .stay fit fit (by rw [blank];exact leave k m j hm hj) rfl
  have path:=joinPath (joinPath entry scan) ending
  convert path using 1;omega
#print axioms enter
#print axioms leave
#print axioms paint
#print axioms paint_bank
end VirtualFinalClosure.GrowPaint
