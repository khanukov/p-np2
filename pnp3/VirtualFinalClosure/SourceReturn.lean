import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.SourceReturn
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong source-return declaration kind {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique source-return term {mod}/{key}"
private theorem row24_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 24 m) (none)=(nc k 25 m,none,.right) := by
  have rr:=literalRow k 24 m 25 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 72)
  rw [mode0 m hm] at rr
  exact rr
private theorem row25_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 25 m) (none)=(nc k 26 m,none,.stay) := by
  have rr:=literalRow k 25 m 26 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 75)
  rw [mode0 m hm] at rr
  exact rr
private theorem row25_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 25 m) (some false)=(nc k 25 m,some false,.right) := by
  have rr:=literalRow k 25 m 25 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 76)
  rw [mode0 m hm] at rr
  exact rr
private theorem row25_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 25 m) (some true)=(nc k 25 m,some true,.right) := by
  have rr:=literalRow k 25 m 25 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 77)
  rw [mode0 m hm] at rr
  exact rr
private theorem row26_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 26 m) (none)=(nc k 27 m,none,.right) := by
  have rr:=literalRow k 26 m 27 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 78)
  rw [mode0 m hm] at rr
  exact rr
private theorem row27_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 27 m) (none)=(nc k 28 m,none,.stay) := by
  have rr:=literalRow k 27 m 28 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 81)
  rw [mode0 m hm] at rr
  exact rr
private theorem row27_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 27 m) (some false)=(nc k 27 m,some false,.right) := by
  have rr:=literalRow k 27 m 27 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 82)
  rw [mode0 m hm] at rr
  exact rr
private theorem row27_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 27 m) (some true)=(nc k 27 m,some true,.right) := by
  have rr:=literalRow k 27 m 27 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 83)
  rw [mode0 m hm] at rr
  exact rr
private theorem row28_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 28 m) (none)=(nc k 29 m,none,.right) := by
  have rr:=literalRow k 28 m 29 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 84)
  rw [mode0 m hm] at rr
  exact rr
private theorem row29_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 29 m) (none)=(nc k 30 m,none,.right) := by
  have rr:=literalRow k 29 m 30 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 87)
  rw [mode0 m hm] at rr
  exact rr
private theorem row29_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 29 m) (some true)=(nc k 29 m,some true,.right) := by
  have rr:=literalRow k 29 m 29 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 89)
  rw [mode0 m hm] at rr
  exact rr
private theorem row30_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 30 m) (none)=(nc k 30 m,none,.right) := by
  have rr:=literalRow k 30 m 30 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 90)
  rw [mode0 m hm] at rr
  exact rr
private theorem row30_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 30 m) (some false)=(nc k 6 m,some false,.right) := by
  have rr:=literalRow k 30 m 6 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 91)
  rw [mode0 m hm] at rr
  exact rr
private theorem row25 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 25 m) (some b)=(nc k 25 m,some b,.right) := by
  cases b
  · exact row25_1 k m hm
  · exact row25_2 k m hm
private theorem row27 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 27 m) (some b)=(nc k 27 m,some b,.right) := by
  cases b
  · exact row27_1 k m hm
  · exact row27_2 k m hm
/-- Literal return from the actual source EOF to the bank0 delimiter.
The extra blank is required by controls29/30 and is derived from raw geometry. -/
private theorem source_to_paid (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m<144) (fr : Frame T S L H Q F) (gap : H+Q+1<F) (fit : F+1≤P) :
    GPath (M:=machine k) P (F-S+3) (C k 24 m S T) (C k 6 m (F+1) T) := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,f0,ff,register,assignment,tally,gaps⟩:=fr
  let z:=L-S-1
  let n:=H-L-1
  let g:=F-(H+Q)-2
  have p1:=keep (M:=machine k) (P:=P) (nc k 24 m) (nc k 25 m) S (S+1) T .right
    (by omega) (by omega) (by rw [s0];exact row24_0 k m hm) rfl
  have pr:=sweepR (M:=machine k) (P:=P) (nc k 25 m) T (S+1) z (by dsimp only [z];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=register i (by omega) (by dsimp only [z] at hi;omega)
    rw [hb];exact row25 k m hm b)
  rw [show S+1+z=L by dsimp only [z];omega] at pr
  have p2:=keep (M:=machine k) (P:=P) (nc k 25 m) (nc k 26 m) L L T .stay
    (by omega) (by omega) (by rw [l0];exact row25_0 k m hm) rfl
  have p3:=keep (M:=machine k) (P:=P) (nc k 26 m) (nc k 27 m) L (L+1) T .right
    (by omega) (by omega) (by rw [l0];exact row26_0 k m hm) rfl
  have pa:=sweepR (M:=machine k) (P:=P) (nc k 27 m) T (L+1) n (by dsimp only [n];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=assignment i (by omega) (by dsimp only [n] at hi;omega)
    rw [hb];exact row27 k m hm b)
  rw [show L+1+n=H by dsimp only [n];omega] at pa
  have p4:=keep (M:=machine k) (P:=P) (nc k 27 m) (nc k 28 m) H H T .stay
    (by omega) (by omega) (by rw [h0];exact row27_0 k m hm) rfl
  have p5:=keep (M:=machine k) (P:=P) (nc k 28 m) (nc k 29 m) H (H+1) T .right
    (by omega) (by omega) (by rw [h0];exact row28_0 k m hm) rfl
  have pt:=sweepR (M:=machine k) (P:=P) (nc k 29 m) T (H+1) Q (by omega) (by
    intro i lo hi
    rw [tally i (by omega) (by omega)]
    exact row29_2 k m hm)
  have p6:=keep (M:=machine k) (P:=P) (nc k 29 m) (nc k 30 m) (H+1+Q) (H+Q+2) T .right
    (by omega) (by omega) (by rw [gaps _ (by omega) (by omega)];exact row29_0 k m hm)
    (by change H+1+Q+1=H+Q+2;omega)
  have pg:=sweepR (M:=machine k) (P:=P) (nc k 30 m) T (H+Q+2) g (by dsimp only [g];omega) (by
    intro i lo hi
    rw [gaps i (by omega) (by dsimp only [g] at hi;omega)]
    exact row30_0 k m hm)
  rw [show H+Q+2+g=F by dsimp only [g];omega] at pg
  have p7:=keep (M:=machine k) (P:=P) (nc k 30 m) (nc k 6 m) F (F+1) T .right
    (by omega) fit (by rw [ff];exact row30_1 k m hm) rfl
  have combined:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p1 pr) p2) p3) pa) p4) p5) pt) p6) pg) p7
  have price : 1+z+1+1+n+1+1+Q+1+g+1=F-S+3 := by dsimp only [z,n,g];omega
  rw [price] at combined
  exact combined
#print axioms source_to_paid
end VirtualFinalClosure.SourceReturn
