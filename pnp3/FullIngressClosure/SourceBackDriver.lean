import FullIngressClosure.SourceRoundCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_grid","bankGrid"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_unary","bankUnary"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_idempotent","bankIdempotent"),
      ("FullIngressClosure.Move","FullIngressClosure","asUnary","asUnary"),
      ("FullIngressClosure.Move","FullIngressClosure","travel","travel"),
      ("FullIngressClosure.Counters","FullIngressClosure","decrement_zero","decrementZero"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena","Arena"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.gap","arenaGap"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor","Corridor"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.order","corridorOrder"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.eof","corridorEof"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted","lifted"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted_here","liftedHere"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_lifted","bankLifted"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted_grid","liftedGrid"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted_unary","liftedUnary"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_below","bankBelow"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_corridor","bankCorridor"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_arena","bankArena"),
      ("FullIngressClosure.SourceBackRound","FullIngressClosure","BackCode","BackCode"),
      ("FullIngressClosure.SourceBackRound","FullIngressClosure","back_round","backRound"),
      ("FullIngressClosure.SourceRoundCertificates","FullIngressClosure","back0","back0"),
      ("FullIngressClosure.SourceRoundCertificates","FullIngressClosure","back1","back1"),
      ("FullIngressClosure.SourceRoundCertificates","FullIngressClosure","back2","back2"),
      ("FullIngressClosure.SourceRoundCertificates","FullIngressClosure","backExit0","backExit0"),
      ("FullIngressClosure.SourceRoundCertificates","FullIngressClosure","backExit1","backExit1"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1389","dec1389"),
      ("FullIngressClosure.Certificates","FullIngressClosure","dec1425","dec1425") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique full backward source driver term {mod}/{key}: {found.map Prod.fst}"
/-- Proof-side description of the bit already carried by the literal control. -/
private def savedAt {S : Nat} (source : Fin S → Bool) (q : Nat) : Option Bool :=
  if h : q < S then some (source ⟨q,h⟩) else none
private def backState (k : Nat) {S : Nat} (source : Fin S → Bool) (q : Nat) : Fin (BodyIngress.machine k).stateCount :=
  match savedAt source q with
  | none => st k 1461
  | some false => st k 1389
  | some true => st k 1425
private def skip9State (k : Nat) {S : Nat} (source : Fin S → Bool) (p : Nat) (hp : p < S) : Fin (BodyIngress.machine k).stateCount :=
  if source ⟨p,hp⟩ then st k 1587 else st k 1547
private theorem source_saved {S p q : Nat} {T : Nat → Option Bool} (source : Fin S → Bool) (qp : p ≤ q) (qs : q ≤ S)
    (cells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) (eof : T S=none) :
    T q=savedAt source q := by
  dsimp only [savedAt]
  split_ifs with phys
  · exact cells q qp phys
  · have eq : q=S:=by omega
    rwa [eq]
private theorem back_step {k lo P D T S L H F Q p q} (source : Fin S → Bool)
    (grid : Grid D T) (corridor : Corridor T S L H) (arena : Arena T H F Q)
    (d0 : D 0=F+1) (lower : lo ≤ p) (pq : p < q) (qs : q ≤ S)
    (cells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (w v : Nat) (len : D 11=D 10+w+1) (unary : BankUnary D T 10 (v+1))
    (fit : v+1 ≤ w) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 32*(P+16) ∧ PPath k lo P t
      (pNode (backState k source q) (D 10) (lifted T S q))
      (pNode (backState k source (q-1)) (D 10) (lifted (setBank T D 10 v) S (q-1))) := by
  have prev : q-1 < S:=by omega
  have applyRound {saved entry zero}
      (code : BackCode k saved entry (st k 1389) (st k 1425) zero)
      (cell : T q=saved) (virtual : saved.isNone=true ↔ q=S) :
      ∃ t,t ≤ 32*(P+16) ∧ PPath k lo P t
        (pNode entry (D 10) (lifted T S q))
        (pNode (backState k source (q-1)) (D 10) (lifted (setBank T D 10 v) S (q-1))) := by
    obtain ⟨bit,t,price,read,path⟩:=backRound (k:=k) (lo:=lo) (P:=P) code grid corridor arena d0
      (by omega) qs cell virtual (by
        intro i il iu
        exact ⟨source ⟨i,iu⟩,cells i (by omega) iu⟩) w v len unary fit upper
    have hb : bit=source ⟨q-1,prev⟩:=Option.some.inj (read.symm.trans (cells (q-1) (by omega) prev))
    rw [hb] at path
    have state : (if source ⟨q-1,prev⟩ then st k 1425 else st k 1389)=backState k source (q-1) := by
      dsimp only [backState,savedAt]
      rw [dif_pos prev]
      cases source ⟨q-1,prev⟩ <;> rfl
    rw [state] at path
    exact ⟨t,price,path⟩
  have value:=source_saved source (by omega : p ≤ q) qs cells (corridorEof corridor)
  by_cases phys : q < S
  · cases hbit : source ⟨q,phys⟩
    · have h : backState k source q=st k 1389:=by simp only [backState,savedAt,dif_pos phys,hbit]
      rw [h]
      exact applyRound (back0 k) (by simpa only [savedAt,dif_pos phys,hbit] using value) (by
        constructor
        · intro h; cases h
        · intro h; omega)
    · have h : backState k source q=st k 1425:=by simp only [backState,savedAt,dif_pos phys,hbit]
      rw [h]
      exact applyRound (back1 k) (by simpa only [savedAt,dif_pos phys,hbit] using value) (by
        constructor
        · intro h; cases h
        · intro h; omega)
  · have eq : q=S:=by omega
    have h : backState k source q=st k 1461:=by simp only [backState,savedAt,dif_neg phys]
    rw [h]
    exact applyRound (back2 k) (by simpa only [savedAt,dif_neg phys] using value) (by
      constructor
      · intro _; exact eq
      · intro _; rfl)
private theorem back_driver {k lo P D T S L H F Q p} (source : Fin S → Bool)
    (grid : Grid D T) (corridor : Corridor T S L H) (arena : Arena T H F Q)
    (d0 : D 0=F+1) (lower : lo ≤ p) (phys : p < S)
    (cells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (w : Nat) (len : D 11=D 10+w+1) (upper : D 12 ≤ P) :
    ∀ v,v ≤ w → p+v ≤ S → ∃ t,t ≤ (32*v+4)*(P+16) ∧ PPath k lo P t
      (pNode (backState k source (p+v)) (D 10) (lifted (setBank T D 10 v) S (p+v)))
      (pNode (skip9State k source p phys) (D 9) (lifted (setBank T D 10 0) S p)) := by
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have below : S < D 0:=by omega
  have low0 : lo ≤ D 0:=by omega
  have high10 : D 10+w+1 ≤ P:=by rw [← len]; exact (gridMono grid 11 12 (by decide) le_rfl).trans upper
  intro v
  induction v with
  | zero =>
    intro _ _
    simp only [Nat.add_zero,Nat.mul_zero,Nat.zero_add]
    let B:=setBank T D 10 0
    have gridB:=bankGrid grid 10 0 (by decide)
    have gridHole:=liftedGrid gridB below (by omega : p ≤ S)
    have unary:=liftedUnary gridB below (by omega : p ≤ S) (by decide) (bankUnary T D 10 0)
    have endBlank : lifted B S p (D 10+w+1)=none:=by rw [← len]; exact gridBlank gridHole 11 (by decide)
    cases hbit : source ⟨p,phys⟩
    · have state : backState k source p=st k 1389:=by simp only [backState,savedAt,dif_pos phys,hbit]
      have out : skip9State k source p phys=st k 1547:=by simp only [skip9State,hbit,Bool.false_eq_true,↓reduceIte]
      rw [state,out]
      have decPath:=decrementZero (k:=k) (lo:=lo) (hi:=P) (dec1389 k) (lifted B S p) (D 10) w
        (low0.trans (gridMono grid 0 10 (by decide) (by decide))) high10
        (gridBlank gridHole 10 (by decide)) endBlank (asUnary unary len)
      obtain ⟨t,price,path⟩:=travel (k:=k) (lo:=lo) (P:=P) (backExit0 k) gridHole (by decide) (by decide) low0 upper
      exact ⟨_,by omega,pAppend decPath path⟩
    · have state : backState k source p=st k 1425:=by simp only [backState,savedAt,dif_pos phys,hbit]
      have out : skip9State k source p phys=st k 1587:=by simp only [skip9State,hbit,↓reduceIte]
      rw [state,out]
      have decPath:=decrementZero (k:=k) (lo:=lo) (hi:=P) (dec1425 k) (lifted B S p) (D 10) w
        (low0.trans (gridMono grid 0 10 (by decide) (by decide))) high10
        (gridBlank gridHole 10 (by decide)) endBlank (asUnary unary len)
      obtain ⟨t,price,path⟩:=travel (k:=k) (lo:=lo) (P:=P) (backExit1 k) gridHole (by decide) (by decide) low0 upper
      exact ⟨_,by omega,pAppend decPath path⟩
  | succ v ih =>
    intro fit span
    let B:=setBank T D 10 (v+1)
    have gridB:=bankGrid grid 10 (v+1) (by decide)
    have corridorB:=bankCorridor grid corridor (by decide : 10<12) (by omega : H ≤ D 0) (v:=v+1)
    have arenaB:=bankArena grid arena (by decide : 10<12) d0 (v:=v+1)
    have cellsB (i : Nat) (il : p ≤ i) (iu : i < S) : B i=some (source ⟨i,iu⟩) := by
      change setBank T D 10 (v+1) i=some (source ⟨i,iu⟩)
      rw [bankBelow grid (j:=10) (v:=v+1) (i:=i) (by decide) (by omega)]
      exact cells i il iu
    obtain ⟨t0,h0,path0⟩:=back_step (k:=k) (lo:=lo) (P:=P) source gridB corridorB arenaB d0 lower
      (by omega : p < p+(v+1)) span cellsB w v len (bankUnary T D 10 (v+1)) fit upper
    have eq : setBank B D 10 v=setBank T D 10 v:=bankIdempotent T D 10 (v+1) v
    have address : p+(v+1)-1=p+v:=by omega
    rw [eq,address] at path0
    obtain ⟨t1,h1,path1⟩:=ih (by omega) (by omega)
    refine ⟨_,?_,pAppend path0 path1⟩
    nlinarith only [h0,h1]
end FullIngressClosure
