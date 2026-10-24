import FullIngressClosure.Move
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("BodyIngress.Native","BodyIngress","keep","pKeep"),
      ("BodyIngress.Native","BodyIngress","sweepL","pSweepL"),
      ("BodyIngress.Native","BodyIngress","sweepR","pSweepR"),
      ("BodyIngress.Native","BodyIngress","dest","dest"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel","Travel"),
      ("FullIngressClosure.Move","FullIngressClosure","travel","travel"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique physical arena path term {mod}/{key}: {found.map Prod.fst}"
private structure Arena (T : Nat → Option Bool) (H F Q : Nat) : Prop where
  positive : 0 < Q
  gap : H+Q < F
  blank : T H=none
  fence : T F=some false
  marks : ∀ i,H < i → i ≤ H+Q → T i=some true
  space : ∀ i,H+Q < i → i < F → T i=none
private structure ToHCode (k a : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  at0 : Fin (BodyIngress.machine k).stateCount
  atFence : Fin (BodyIngress.machine k).stateCount
  gap : Fin (BodyIngress.machine k).stateCount
  marks : Fin (BodyIngress.machine k).stateCount
  inward : Travel k a 0 entry at0
  safe0 : Safe k at0
  safeFence : Safe k atFence
  safeGap : Safe k gap
  safeMarks : Safe k marks
  left0 : (BodyIngress.machine k).step at0 none=(atFence,none,.left)
  leftFence : (BodyIngress.machine k).step atFence (some false)=(gap,some false,.left)
  gapNone : (BodyIngress.machine k).step gap none=(gap,none,.left)
  gapTrue : (BodyIngress.machine k).step gap (some true)=(marks,some true,.left)
  markTrue : (BodyIngress.machine k).step marks (some true)=(marks,some true,.left)
  markNone : (BodyIngress.machine k).step marks none=(out,none,.stay)
private theorem to_assignment_end {k lo P D T H F Q a entry out}
    (code : ToHCode k a entry out) (grid : Grid D T) (frame : Arena T H F Q)
    (ha : a ≤ 12) (d0 : D 0=F+1) (lower : lo ≤ H) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 4*(P+16) ∧ PPath k lo P t (pNode entry (D a) T) (pNode out H T) := by
  have hQ:=frame.positive
  have hGap:=frame.gap
  have low0 : lo ≤ D 0:=by omega
  have hi0 : D 0 ≤ P:=(gridMono grid 0 12 (by decide) le_rfl).trans upper
  obtain ⟨t,price,go⟩:=travel (k:=k) (lo:=lo) (P:=P) code.inward grid ha (by decide) low0 upper
  have from0:=pKeep (k:=k) (lo:=lo) (hi:=P) code.at0 code.atFence (D 0) F T .left
    ⟨code.safe0.1,code.safe0.2.1⟩ code.safe0.2.2 ⟨low0,hi0⟩ ⟨by omega,by omega⟩
    (by rw [gridBlank grid 0 (by decide)]; exact code.left0) (by simp only [dest]; omega)
  have fence:=pKeep (k:=k) (lo:=lo) (hi:=P) code.atFence code.gap F (F-1) T .left
    ⟨code.safeFence.1,code.safeFence.2.1⟩ code.safeFence.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [frame.fence]; exact code.leftFence) rfl
  have scanGap:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.gap T (H+Q) (F-(H+Q)-1) (by omega) (by omega)
    ⟨code.safeGap.1,code.safeGap.2.1⟩ code.safeGap.2.2 (by
      intro i il iu
      rw [frame.space i il (by omega)]
      exact code.gapNone)
  have eqGap : H+Q+(F-(H+Q)-1)=F-1:=by omega
  rw [eqGap] at scanGap
  have take:=pKeep (k:=k) (lo:=lo) (hi:=P) code.gap code.marks (H+Q) (H+Q-1) T .left
    ⟨code.safeGap.1,code.safeGap.2.1⟩ code.safeGap.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [frame.marks (H+Q) (by omega) le_rfl]; exact code.gapTrue) rfl
  have scanMarks:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.marks T H (Q-1) lower (by omega)
    ⟨code.safeMarks.1,code.safeMarks.2.1⟩ code.safeMarks.2.2 (by
      intro i il iu
      rw [frame.marks i il (by omega)]
      exact code.markTrue)
  rw [show H+(Q-1)=H+Q-1 by omega] at scanMarks
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.marks out H H T .stay
    ⟨code.safeMarks.1,code.safeMarks.2.1⟩ code.safeMarks.2.2 ⟨lower,by omega⟩ ⟨lower,by omega⟩
    (by rw [frame.blank]; exact code.markNone) rfl
  refine ⟨_,?_,pAppend go (pAppend from0 (pAppend fence (pAppend scanGap (pAppend take (pAppend scanMarks stop)))))⟩
  omega
private structure FromHCode (k a : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  seek : Fin (BodyIngress.machine k).stateCount
  at0 : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeSeek : Safe k seek
  enter : (BodyIngress.machine k).step entry none=(seek,none,.right)
  space : (BodyIngress.machine k).step seek none=(seek,none,.right)
  marks : (BodyIngress.machine k).step seek (some true)=(seek,some true,.right)
  stop : (BodyIngress.machine k).step seek (some false)=(at0,some false,.right)
  outward : Travel k 0 a at0 out
private theorem from_assignment_end {k lo P D T H F Q a entry out}
    (code : FromHCode k a entry out) (grid : Grid D T) (frame : Arena T H F Q)
    (ha : a ≤ 12) (d0 : D 0=F+1) (lower : lo ≤ H) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 4*(P+16) ∧ PPath k lo P t (pNode entry H T) (pNode out (D a) T) := by
  have hQ:=frame.positive
  have hGap:=frame.gap
  have hi0 : D 0 ≤ P:=(gridMono grid 0 12 (by decide) le_rfl).trans upper
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry code.seek H (H+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2 ⟨lower,by omega⟩ ⟨by omega,by omega⟩
    (by rw [frame.blank]; exact code.enter) rfl
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=P) code.seek T (H+1) (F-H-1) (by omega) (by omega)
    ⟨code.safeSeek.1,code.safeSeek.2.1⟩ code.safeSeek.2.2 (by
      intro i il iu
      by_cases mark : i ≤ H+Q
      · rw [frame.marks i (by omega) mark]; exact code.marks
      · rw [frame.space i (by omega) (by omega)]; exact code.space)
  rw [show H+1+(F-H-1)=F by omega] at scan
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.seek code.at0 F (D 0) T .right
    ⟨code.safeSeek.1,code.safeSeek.2.1⟩ code.safeSeek.2.2 ⟨by omega,by omega⟩ ⟨by omega,hi0⟩
    (by rw [frame.fence]; exact code.stop) (by simp only [dest]; omega)
  obtain ⟨t,price,go⟩:=travel (k:=k) (lo:=lo) (P:=P) code.outward grid (by decide) ha (by omega) upper
  refine ⟨_,?_,pAppend first (pAppend scan (pAppend stop go))⟩
  omega
end FullIngressClosure
