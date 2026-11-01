import VirtualFinalClosure.Paths
namespace VirtualFinalClosure.SourceWalk
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong framed-source path/row kind {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique existing framed-source interface {mod}/{key}"
private def node_type : ∀ M,Fin M.stateCount → Nat → (Nat → Option Bool) → GNode M := fun _=>node
private def cell_tactic_type : Nat → TacticM Unit := cellTac
private structure Frame (T : Nat → Option Bool) (S L H Q F : Nat) : Prop where
  SL : S < L
  LH : L < H
  positive : 0 < Q
  room : H+Q < F
  sourceEnd : T S=none
  separator : T L=none
  assignmentEnd : T H=none
  scratchStart : T (F+1)=none
  fence : T F=some false
  register : ∀ i,S < i → i < L → ∃ b,T i=some b
  assignment : ∀ i,L < i → i < H → ∃ b,T i=some b
  tally : ∀ i,H < i → i ≤ H+Q → T i=some true
  gap : ∀ i,H+Q < i → i < F → T i=none
private theorem row10_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 10 m) (none)=(nc k 11 m,none,.left) := by
  have rr:=literalRow k 10 m 11 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 30)
  rw [mode0 m hm] at rr
  exact rr
private theorem row11_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 11 m) (some false)=(nc k 12 m,some false,.left) := by
  have rr:=literalRow k 11 m 12 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 34)
  rw [mode0 m hm] at rr
  exact rr
private theorem row12_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 12 m) (none)=(nc k 12 m,none,.left) := by
  have rr:=literalRow k 12 m 12 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 36)
  rw [mode0 m hm] at rr
  exact rr
private theorem row12_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 12 m) (some true)=(nc k 13 m,some true,.left) := by
  have rr:=literalRow k 12 m 13 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 38)
  rw [mode0 m hm] at rr
  exact rr
private theorem row13_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 13 m) (none)=(nc k 14 m,none,.left) := by
  have rr:=literalRow k 13 m 14 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 39)
  rw [mode0 m hm] at rr
  exact rr
private theorem row13_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 13 m) (some true)=(nc k 13 m,some true,.left) := by
  have rr:=literalRow k 13 m 13 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 41)
  rw [mode0 m hm] at rr
  exact rr
private theorem row14_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 14 m) (none)=(nc k 15 m,none,.stay) := by
  have rr:=literalRow k 14 m 15 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 42)
  rw [mode0 m hm] at rr
  exact rr
private theorem row14_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 14 m) (some false)=(nc k 14 m,some false,.left) := by
  have rr:=literalRow k 14 m 14 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 43)
  rw [mode0 m hm] at rr
  exact rr
private theorem row14_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 14 m) (some true)=(nc k 14 m,some true,.left) := by
  have rr:=literalRow k 14 m 14 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 44)
  rw [mode0 m hm] at rr
  exact rr
private theorem row15_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 15 m) (none)=(nc k 16 m,none,.left) := by
  have rr:=literalRow k 15 m 16 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 45)
  rw [mode0 m hm] at rr
  exact rr
private theorem row16_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 16 m) (none)=(nc k 17 m,none,.stay) := by
  have rr:=literalRow k 16 m 17 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 48)
  rw [mode0 m hm] at rr
  exact rr
private theorem row16_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 16 m) (some false)=(nc k 16 m,some false,.left) := by
  have rr:=literalRow k 16 m 16 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 49)
  rw [mode0 m hm] at rr
  exact rr
private theorem row16_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 16 m) (some true)=(nc k 16 m,some true,.left) := by
  have rr:=literalRow k 16 m 16 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 50)
  rw [mode0 m hm] at rr
  exact rr
private theorem row14 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 14 m) (some b)=(nc k 14 m,some b,.left) := by
  cases b
  · exact row14_1 k m hm
  · exact row14_2 k m hm
private theorem row16 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 16 m) (some b)=(nc k 16 m,some b,.left) := by
  cases b
  · exact row16_1 k m hm
  · exact row16_2 k m hm
/-- The SAME frozen candidate physically crosses fence, gap, paid tally,
occupied assignment and register to genuine source EOF. Entire tape is unchanged. -/
private theorem paid_to_source (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m<144) (fr : Frame T S L H Q F) (fit : F+1≤P) :
    GPath (M:=machine k) P (F-S+3) (C k 10 m (F+1) T) (C k 17 m S T) := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,f0,ff,register,assignment,tally,gaps⟩:=fr
  let gap:=F-(H+Q)-1
  let n:=H-L-1
  let z:=L-S-1
  have p1:=keep (M:=machine k) (P:=P) (nc k 10 m) (nc k 11 m) (F+1) F T .left
    fit (by omega) (by rw [f0];exact row10_0 k m hm) (by dsimp only [dest];omega)
  have p2:=keep (M:=machine k) (P:=P) (nc k 11 m) (nc k 12 m) F (F-1) T .left
    (by omega) (by omega) (by rw [ff];exact row11_1 k m hm) rfl
  have pg:=sweepL (M:=machine k) (P:=P) (nc k 12 m) T (H+Q) gap (by dsimp only [gap];omega) (by
    intro i lo hi
    rw [gaps i lo (by dsimp only [gap] at hi;omega)]
    exact row12_0 k m hm)
  rw [show H+Q+gap=F-1 by dsimp only [gap];omega] at pg
  have p3:=keep (M:=machine k) (P:=P) (nc k 12 m) (nc k 13 m) (H+Q) (H+(Q-1)) T .left
    (by omega) (by omega) (by rw [tally _ (by omega) le_rfl];exact row12_2 k m hm) (by dsimp only [dest];omega)
  have pt:=sweepL (M:=machine k) (P:=P) (nc k 13 m) T H (Q-1) (by omega) (by
    intro i lo hi
    rw [tally i lo (by omega)]
    exact row13_2 k m hm)
  have p4:=keep (M:=machine k) (P:=P) (nc k 13 m) (nc k 14 m) H (H-1) T .left
    (by omega) (by omega) (by rw [h0];exact row13_0 k m hm) rfl
  have pa:=sweepL (M:=machine k) (P:=P) (nc k 14 m) T L n (by dsimp only [n];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=assignment i lo (by dsimp only [n] at hi;omega)
    rw [hb];exact row14 k m hm b)
  rw [show L+n=H-1 by dsimp only [n];omega] at pa
  have p5:=keep (M:=machine k) (P:=P) (nc k 14 m) (nc k 15 m) L L T .stay
    (by omega) (by omega) (by rw [l0];exact row14_0 k m hm) rfl
  have p6:=keep (M:=machine k) (P:=P) (nc k 15 m) (nc k 16 m) L (L-1) T .left
    (by omega) (by omega) (by rw [l0];exact row15_0 k m hm) rfl
  have pr:=sweepL (M:=machine k) (P:=P) (nc k 16 m) T S z (by dsimp only [z];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=register i lo (by dsimp only [z] at hi;omega)
    rw [hb];exact row16 k m hm b)
  rw [show S+z=L-1 by dsimp only [z];omega] at pr
  have p7:=keep (M:=machine k) (P:=P) (nc k 16 m) (nc k 17 m) S S T .stay
    (by omega) (by omega) (by rw [s0];exact row16_0 k m hm) rfl
  have combined:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p1 p2) pg) p3) pt) p4) pa) p5) p6) pr) p7
  have price : 1+1+gap+1+(Q-1)+1+n+1+1+z+1=F-S+3 := by dsimp only [gap,n,z];omega
  rw [price] at combined
  exact combined
#print axioms node_type
#print axioms cell_tactic_type
#print axioms paid_to_source
end VirtualFinalClosure.SourceWalk
