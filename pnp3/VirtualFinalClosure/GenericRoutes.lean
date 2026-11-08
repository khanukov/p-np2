import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.GenericRoutes
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong generic framed route term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique framed route interface {mod}/{key}"
/-- A framed physical route on an OPAQUE machine, using the existing path
engine. Callers prove every supplied premise from their actual literal rows. -/
private theorem left_route {M : UniformTM} (q0 q1 q2 q3 q4 q5 q6 q7 : Fin M.stateCount)
    (P S L H Q F : Nat) (T : Nat → Option Bool) (fr : Frame T S L H Q F) (fit : F+1 ≤ P)
    (r0 : M.step q0 none=(q1,none,.left))
    (r1 : M.step q1 (some false)=(q2,some false,.left))
    (r20 : M.step q2 none=(q2,none,.left))
    (r22 : M.step q2 (some true)=(q3,some true,.left))
    (r30 : M.step q3 none=(q4,none,.left))
    (r32 : M.step q3 (some true)=(q3,some true,.left))
    (r40 : M.step q4 none=(q5,none,.stay))
    (r4 : ∀ b : Bool,M.step q4 (some b)=(q4,some b,.left))
    (r50 : M.step q5 none=(q6,none,.left))
    (r60 : M.step q6 none=(q7,none,.stay))
    (r6 : ∀ b : Bool,M.step q6 (some b)=(q6,some b,.left)) :
    GPath (M:=M) P (F-S+3) (node q0 (F+1) T) (node q7 S T) := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,f0,ff,register,assignment,tally,gaps⟩:=fr
  let gap:=F-(H+Q)-1
  let n:=H-L-1
  let z:=L-S-1
  have p1:=keep (M:=M) (P:=P) q0 q1 (F+1) F T .left
    fit (by omega) (by rw [f0];exact r0) (by dsimp only [dest];omega)
  have p2:=keep (M:=M) (P:=P) q1 q2 F (F-1) T .left
    (by omega) (by omega) (by rw [ff];exact r1) rfl
  have pg:=sweepL (M:=M) (P:=P) q2 T (H+Q) gap (by dsimp only [gap];omega) (by
    intro i lo hi
    rw [gaps i lo (by dsimp only [gap] at hi;omega)]
    exact r20)
  rw [show H+Q+gap=F-1 by dsimp only [gap];omega] at pg
  have p3:=keep (M:=M) (P:=P) q2 q3 (H+Q) (H+(Q-1)) T .left
    (by omega) (by omega) (by rw [tally _ (by omega) le_rfl];exact r22) (by dsimp only [dest];omega)
  have pt:=sweepL (M:=M) (P:=P) q3 T H (Q-1) (by omega) (by
    intro i lo hi
    rw [tally i lo (by omega)]
    exact r32)
  have p4:=keep (M:=M) (P:=P) q3 q4 H (H-1) T .left
    (by omega) (by omega) (by rw [h0];exact r30) rfl
  have pa:=sweepL (M:=M) (P:=P) q4 T L n (by dsimp only [n];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=assignment i lo (by dsimp only [n] at hi;omega)
    rw [hb];exact r4 b)
  rw [show L+n=H-1 by dsimp only [n];omega] at pa
  have p5:=keep (M:=M) (P:=P) q4 q5 L L T .stay
    (by omega) (by omega) (by rw [l0];exact r40) rfl
  have p6:=keep (M:=M) (P:=P) q5 q6 L (L-1) T .left
    (by omega) (by omega) (by rw [l0];exact r50) rfl
  have pr:=sweepL (M:=M) (P:=P) q6 T S z (by dsimp only [z];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=register i lo (by dsimp only [z] at hi;omega)
    rw [hb];exact r6 b)
  rw [show S+z=L-1 by dsimp only [z];omega] at pr
  have p7:=keep (M:=M) (P:=P) q6 q7 S S T .stay
    (by omega) (by omega) (by rw [s0];exact r60) rfl
  have combined:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p1 p2) pg) p3) pt) p4) pa) p5) p6) pr) p7
  have price : 1+1+gap+1+(Q-1)+1+n+1+1+z+1=F-S+3 := by dsimp only [gap,n,z];omega
  rw [price] at combined
  exact combined
private theorem right_route {M : UniformTM} (q0 q1 q2 q3 q4 q5 q6 q7 : Fin M.stateCount)
    (P S L H Q F : Nat) (T : Nat → Option Bool) (fr : Frame T S L H Q F)
    (gap : H+Q+1 < F) (fit : F+1 ≤ P)
    (r0 : M.step q0 none=(q1,none,.right))
    (r10 : M.step q1 none=(q2,none,.stay))
    (r1 : ∀ b : Bool,M.step q1 (some b)=(q1,some b,.right))
    (r20 : M.step q2 none=(q3,none,.right))
    (r30 : M.step q3 none=(q4,none,.stay))
    (r3 : ∀ b : Bool,M.step q3 (some b)=(q3,some b,.right))
    (r40 : M.step q4 none=(q5,none,.right))
    (r50 : M.step q5 none=(q6,none,.right))
    (r52 : M.step q5 (some true)=(q5,some true,.right))
    (r60 : M.step q6 none=(q6,none,.right))
    (r61 : M.step q6 (some false)=(q7,some false,.right)) :
    GPath (M:=M) P (F-S+3) (node q0 S T) (node q7 (F+1) T) := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,f0,ff,register,assignment,tally,gaps⟩:=fr
  let z:=L-S-1
  let n:=H-L-1
  let g:=F-(H+Q)-2
  have p1:=keep (M:=M) (P:=P) q0 q1 S (S+1) T .right
    (by omega) (by omega) (by rw [s0];exact r0) rfl
  have pr:=sweepR (M:=M) (P:=P) q1 T (S+1) z (by dsimp only [z];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=register i (by omega) (by dsimp only [z] at hi;omega)
    rw [hb];exact r1 b)
  rw [show S+1+z=L by dsimp only [z];omega] at pr
  have p2:=keep (M:=M) (P:=P) q1 q2 L L T .stay
    (by omega) (by omega) (by rw [l0];exact r10) rfl
  have p3:=keep (M:=M) (P:=P) q2 q3 L (L+1) T .right
    (by omega) (by omega) (by rw [l0];exact r20) rfl
  have pa:=sweepR (M:=M) (P:=P) q3 T (L+1) n (by dsimp only [n];omega) (by
    intro i lo hi
    obtain ⟨b,hb⟩:=assignment i (by omega) (by dsimp only [n] at hi;omega)
    rw [hb];exact r3 b)
  rw [show L+1+n=H by dsimp only [n];omega] at pa
  have p4:=keep (M:=M) (P:=P) q3 q4 H H T .stay
    (by omega) (by omega) (by rw [h0];exact r30) rfl
  have p5:=keep (M:=M) (P:=P) q4 q5 H (H+1) T .right
    (by omega) (by omega) (by rw [h0];exact r40) rfl
  have pt:=sweepR (M:=M) (P:=P) q5 T (H+1) Q (by omega) (by
    intro i lo hi
    rw [tally i (by omega) (by omega)]
    exact r52)
  have p6:=keep (M:=M) (P:=P) q5 q6 (H+1+Q) (H+Q+2) T .right
    (by omega) (by omega) (by rw [gaps _ (by omega) (by omega)];exact r50)
    (by change H+1+Q+1=H+Q+2;omega)
  have pg:=sweepR (M:=M) (P:=P) q6 T (H+Q+2) g (by dsimp only [g];omega) (by
    intro i lo hi
    rw [gaps i (by omega) (by dsimp only [g] at hi;omega)]
    exact r60)
  rw [show H+Q+2+g=F by dsimp only [g];omega] at pg
  have p7:=keep (M:=M) (P:=P) q6 q7 F (F+1) T .right
    (by omega) fit (by rw [ff];exact r61) rfl
  have combined:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p1 pr) p2) p3) pa) p4) p5) pt) p6) pg) p7
  have price : 1+z+1+1+n+1+1+Q+1+g+1=F-S+3 := by dsimp only [z,n,g];omega
  rw [price] at combined
  exact combined
#print axioms left_route
#print axioms right_route
end VirtualFinalClosure.GenericRoutes
