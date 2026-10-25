import FullIngressClosure.SourceArena
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
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena","Arena"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.gap","arenaGap"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.positive","arenaPositive"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","ToHCode","ToHCode"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","to_assignment_end","toH"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","FromHCode","FromHCode"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","from_assignment_end","fromH") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique source/register physical scan proof {mod}/{key}: {found.map Prod.fst}"
private structure Corridor (T : Nat → Option Bool) (S L H : Nat) : Prop where
  order : S < L ∧ L < H
  eof : T S=none
  sep : T L=none
  endBlank : T H=none
  register : ∀ i,S < i → i < L → T i=some false
  assignment : ∀ i,L < i → i < H → ∃ bit,T i=some bit
private structure ToHoleCode (k a : Nat) (virtual : Bool)
    (entry out : Fin (BodyIngress.machine k).stateCount) where
  atH : Fin (BodyIngress.machine k).stateCount
  assignment : Fin (BodyIngress.machine k).stateCount
  register : Fin (BodyIngress.machine k).stateCount
  source : Fin (BodyIngress.machine k).stateCount
  toH : ToHCode k a entry atH
  safeH : Safe k atH
  safeAssignment : Safe k assignment
  safeRegister : Safe k register
  safeSource : Safe k source
  enter : (BodyIngress.machine k).step atH none=(assignment,none,.left)
  assignmentSome : ∀ bit,(BodyIngress.machine k).step assignment (some bit)=(assignment,some bit,.left)
  assignmentNone : (BodyIngress.machine k).step assignment none=(register,none,.left)
  registerFalse : (BodyIngress.machine k).step register (some false)=(register,some false,.left)
  registerNone : (BodyIngress.machine k).step register none=
    (if virtual then (out,none,.stay) else (source,none,.left))
  sourceSome : virtual=false → ∀ bit,(BodyIngress.machine k).step source (some bit)=(source,some bit,.left)
  sourceNone : virtual=false → (BodyIngress.machine k).step source none=(out,none,.stay)
private theorem to_source_hole {k lo P D T S L H F Q a virtual entry out q}
    (code : ToHoleCode k a virtual entry out) (grid : Grid D T) (corridor : Corridor T S L H)
    (arena : Arena T H F Q) (ha : a ≤ 12) (d0 : D 0=F+1)
    (lower : lo ≤ q) (qp : q ≤ S) (edge : virtual=true ↔ q=S)
    (hole : T q=none) (source : ∀ i,q < i → i < S → ∃ bit,T i=some bit)
    (upper : D 12 ≤ P) :
    ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t (pNode entry (D a) T) (pNode out q T) := by
  have order:=corridor.order
  have gap:=arenaGap arena
  have hQ:=arenaPositive arena
  have high0:=(gridMono grid 0 12 (by decide) le_rfl).trans upper
  have bounds : lo ≤ S ∧ H ≤ P:=by omega
  obtain ⟨t,price,first⟩:=toH (k:=k) (lo:=lo) (P:=P) code.toH grid arena ha d0 (by omega) upper
  have enter:=pKeep (k:=k) (lo:=lo) (hi:=P) code.atH code.assignment H (H-1) T .left
    ⟨code.safeH.1,code.safeH.2.1⟩ code.safeH.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [corridor.endBlank]; exact code.enter) rfl
  have assignment:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.assignment T L (H-L-1) (by omega) (by omega)
    ⟨code.safeAssignment.1,code.safeAssignment.2.1⟩ code.safeAssignment.2.2 (by
      intro i il iu
      obtain ⟨bit,hbit⟩:=corridor.assignment i il (by omega)
      rw [hbit]; exact code.assignmentSome bit)
  rw [show L+(H-L-1)=H-1 by omega] at assignment
  have sep:=pKeep (k:=k) (lo:=lo) (hi:=P) code.assignment code.register L (L-1) T .left
    ⟨code.safeAssignment.1,code.safeAssignment.2.1⟩ code.safeAssignment.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [corridor.sep]; exact code.assignmentNone) rfl
  have register:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.register T S (L-S-1) (by omega) (by omega)
    ⟨code.safeRegister.1,code.safeRegister.2.1⟩ code.safeRegister.2.2 (by
      intro i il iu
      rw [corridor.register i il (by omega)]; exact code.registerFalse)
  rw [show S+(L-S-1)=L-1 by omega] at register
  have tail : ∃ u,u ≤ 2*(P+16) ∧ PPath k lo P u (pNode code.register S T) (pNode out q T) := by
    by_cases virtualCase : virtual=true
    · have qs : q=S:=edge.mp virtualCase
      subst q
      have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.register out S S T .stay
        ⟨code.safeRegister.1,code.safeRegister.2.1⟩ code.safeRegister.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
        (by rw [corridor.eof,code.registerNone]; simp only [virtualCase,↓reduceIte]) rfl
      exact ⟨1,by omega,stop⟩
    · have neq : q < S:=by
        have h : q ≠ S:=by
          intro e
          exact virtualCase (edge.mpr e)
        omega
      have ev : virtual=false:=by cases virtual <;> simp_all
      have step:=pKeep (k:=k) (lo:=lo) (hi:=P) code.register code.source S (S-1) T .left
        ⟨code.safeRegister.1,code.safeRegister.2.1⟩ code.safeRegister.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
        (by rw [corridor.eof,code.registerNone]; rw [if_neg virtualCase]) rfl
      have scan:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.source T q (S-q-1) lower (by omega)
        ⟨code.safeSource.1,code.safeSource.2.1⟩ code.safeSource.2.2 (by
          intro i il iu
          obtain ⟨bit,hbit⟩:=source i il (by omega)
          rw [hbit]; exact code.sourceSome ev bit)
      rw [show q+(S-q-1)=S-1 by omega] at scan
      have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.source out q q T .stay
        ⟨code.safeSource.1,code.safeSource.2.1⟩ code.safeSource.2.2 ⟨lower,by omega⟩ ⟨lower,by omega⟩
        (by rw [hole]; exact code.sourceNone ev) rfl
      exact ⟨_,by omega,pAppend step (pAppend scan stop)⟩
  obtain ⟨u,hu,tail⟩:=tail
  refine ⟨_,?_,pAppend first (pAppend enter (pAppend assignment (pAppend sep (pAppend register tail))))⟩
  omega
private structure RegReturnCode (k a : Nat) (register out : Fin (BodyIngress.machine k).stateCount) where
  assignment : Fin (BodyIngress.machine k).stateCount
  atH : Fin (BodyIngress.machine k).stateCount
  safeRegister : Safe k register
  safeAssignment : Safe k assignment
  regFalse : (BodyIngress.machine k).step register (some false)=(register,some false,.right)
  regNone : (BodyIngress.machine k).step register none=(assignment,none,.right)
  assSome : ∀ bit,(BodyIngress.machine k).step assignment (some bit)=(assignment,some bit,.right)
  assNone : (BodyIngress.machine k).step assignment none=(atH,none,.stay)
  fromH : FromHCode k a atH out
private theorem from_register {k lo P D T S L H F Q a register out}
    (code : RegReturnCode k a register out) (grid : Grid D T) (corridor : Corridor T S L H)
    (arena : Arena T H F Q) (ha : a ≤ 12) (d0 : D 0=F+1)
    (lower : lo ≤ S) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 6*(P+16) ∧ PPath k lo P t (pNode register (S+1) T) (pNode out (D a) T) := by
  have order:=corridor.order
  have gap:=arenaGap arena
  have hQ:=arenaPositive arena
  have high0:=(gridMono grid 0 12 (by decide) le_rfl).trans upper
  have reg:=pSweepR (k:=k) (lo:=lo) (hi:=P) register T (S+1) (L-S-1) (by omega) (by omega)
    ⟨code.safeRegister.1,code.safeRegister.2.1⟩ code.safeRegister.2.2 (by
      intro i il iu
      rw [corridor.register i (by omega) (by omega)]; exact code.regFalse)
  rw [show S+1+(L-S-1)=L by omega] at reg
  have sep:=pKeep (k:=k) (lo:=lo) (hi:=P) register code.assignment L (L+1) T .right
    ⟨code.safeRegister.1,code.safeRegister.2.1⟩ code.safeRegister.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [corridor.sep]; exact code.regNone) rfl
  have ass:=pSweepR (k:=k) (lo:=lo) (hi:=P) code.assignment T (L+1) (H-L-1) (by omega) (by omega)
    ⟨code.safeAssignment.1,code.safeAssignment.2.1⟩ code.safeAssignment.2.2 (by
      intro i il iu
      obtain ⟨bit,hbit⟩:=corridor.assignment i (by omega) (by omega)
      rw [hbit]; exact code.assSome bit)
  rw [show L+1+(H-L-1)=H by omega] at ass
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.assignment code.atH H H T .stay
    ⟨code.safeAssignment.1,code.safeAssignment.2.1⟩ code.safeAssignment.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [corridor.endBlank]; exact code.assNone) rfl
  obtain ⟨t,price,path⟩:=fromH (k:=k) (lo:=lo) (P:=P) code.fromH grid arena ha d0 (by omega) upper
  refine ⟨_,?_,pAppend reg (pAppend sep (pAppend ass (pAppend stop path)))⟩
  omega
private structure SourceReturnCode (k a : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  source : Fin (BodyIngress.machine k).stateCount
  register : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeSource : Safe k source
  enter : (BodyIngress.machine k).step entry none=(source,none,.right)
  scanSome : ∀ bit,(BodyIngress.machine k).step source (some bit)=(source,some bit,.right)
  stop : (BodyIngress.machine k).step source none=(register,none,.right)
  regReturn : RegReturnCode k a register out
private theorem from_source_hole {k lo P D T S L H F Q a entry out q}
    (code : SourceReturnCode k a entry out) (grid : Grid D T) (corridor : Corridor T S L H)
    (arena : Arena T H F Q) (ha : a ≤ 12) (d0 : D 0=F+1)
    (lower : lo ≤ q) (qs : q < S) (hole : T q=none)
    (source : ∀ i,q < i → i < S → ∃ bit,T i=some bit) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t (pNode entry q T) (pNode out (D a) T) := by
  have order:=corridor.order
  have gap:=arenaGap arena
  have hQ:=arenaPositive arena
  have high0:=(gridMono grid 0 12 (by decide) le_rfl).trans upper
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry code.source q (q+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2 ⟨lower,by omega⟩ ⟨by omega,by omega⟩
    (by rw [hole]; exact code.enter) rfl
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=P) code.source T (q+1) (S-q-1) (by omega) (by omega)
    ⟨code.safeSource.1,code.safeSource.2.1⟩ code.safeSource.2.2 (by
      intro i il iu
      obtain ⟨bit,hbit⟩:=source i (by omega) (by omega)
      rw [hbit]; exact code.scanSome bit)
  rw [show q+1+(S-q-1)=S by omega] at scan
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.source code.register S (S+1) T .right
    ⟨code.safeSource.1,code.safeSource.2.1⟩ code.safeSource.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [corridor.eof]; exact code.stop) rfl
  obtain ⟨t,price,path⟩:=from_register (k:=k) (lo:=lo) (P:=P) code.regReturn grid corridor arena ha d0 (by omega) upper
  refine ⟨_,?_,pAppend first (pAppend scan (pAppend stop path))⟩
  omega
end FullIngressClosure
