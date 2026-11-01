import Complexity.PrivateInterfaceLookupResolvedSourceScan
import FullIngressClosure.SourceImage
import FullIngressClosure.SourceEOF
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateSourceScan.bindings `FullIngressClosure.SourceForwardRound
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated source-scan identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private structure ForwardCode (k a : Nat) (saved : Bool)
    (entry next0 next1 zero eofEntry eofOut : Fin (BodyIngress.machine k).stateCount) where
  take : Fin (BodyIngress.machine k).stateCount
  atAnchor : Fin (BodyIngress.machine k).stateCount
  takeAnchor : Fin (BodyIngress.machine k).stateCount
  anchorBad : Fin (BodyIngress.machine k).stateCount
  hole : Fin (BodyIngress.machine k).stateCount
  lift : Fin (BodyIngress.machine k).stateCount
  return0 : Fin (BodyIngress.machine k).stateCount
  return1 : Fin (BodyIngress.machine k).stateCount
  dec : Decrement k entry take zero
  goAnchor : Travel k a 7 take atAnchor
  decAnchor : Decrement k atAnchor takeAnchor anchorBad
  seek : ToHoleCode k 7 false takeAnchor hole
  safeHole : Safe k hole
  safeLift : Safe k lift
  restore : (BodyIngress.machine k).step hole none=(lift,some saved,.right)
  read0 : (BodyIngress.machine k).step lift (some false)=(return0,none,.stay)
  read1 : (BodyIngress.machine k).step lift (some true)=(return1,none,.stay)
  readEOF : (BodyIngress.machine k).step lift none=(eofEntry,none,.stay)
  back0 : SourceReturnCode k a return0 next0
  back1 : SourceReturnCode k a return1 next1
  eof : EOFCode k eofEntry eofOut
private theorem forward_read_row {k a saved entry next0 next1 zero eofEntry eofOut}
    (code : ForwardCode k a saved entry next0 next1 zero eofEntry eofOut) (bit : Bool) :
    (BodyIngress.machine k).step code.lift (some bit)=
      (if bit then code.return1 else code.return0,none,.stay) := by
  cases bit with
  | false => exact code.read0
  | true => exact code.read1
private theorem forward_round {k lo P D T S L H F Q q a saved entry next0 next1 zero eofEntry eofOut}
    (code : ForwardCode k a saved entry next0 next1 zero eofEntry eofOut) (grid : Grid D T)
    (corridor : Corridor T S L H) (arena : Arena T H F Q) (d0 : D 0=F+1)
    (ha : a < 12) (a7 : a ≠ 7) (lower : lo ≤ q) (qs : q < S) (savedCell : T q=some saved)
    (source : ∀ i,q < i → i < S → ∃ bit,T i=some bit)
    (w r v : Nat) (lenA : D (a+1)=D a+w+1) (len7 : D 8=D 7+r+1)
    (unaryA : BankUnary D T a (v+1)) (unary7 : BankUnary D T 7 (S-q))
    (fitA : v+1 ≤ w) (fit7 : S-q ≤ r) (upper : D 12 ≤ P) :
    let B:=setBank (setBank T D a v) D 7 (S-q-1)
    ∃ t,t ≤ 64*(P+16) ∧
      ((q+1 < S ∧ ∃ bit,B (q+1)=some bit ∧ PPath k lo P t
        (pNode entry (D a) (lifted T S q))
        (pNode (if bit then next1 else next0) (D a) (lifted B S (q+1)))) ∨
      (q+1=S ∧ PPath k lo P t (pNode entry (D a) (lifted T S q)) (pNode eofOut (D 0) B))) := by
  intro B
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have below : S < D 0:=by omega
  have low0 : lo ≤ D 0:=by omega
  have highA : D a+w+1 ≤ P:=by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
  have high7 : D 7+r+1 ≤ P:=by rw [← len7]; exact (gridMono grid 8 12 (by decide) le_rfl).trans upper
  have grid0:=liftedGrid grid below (by omega : q ≤ S)
  have unary0:=liftedUnary grid below (by omega : q ≤ S) ha unaryA
  have decA:=decrementPositive (k:=k) (lo:=lo) (hi:=P) code.dec (lifted T S q) (D a) w (v+1)
    (low0.trans (gridMono grid 0 a (by omega) (by omega))) highA (gridBlank grid0 a (by omega))
    (by rw [← lenA]; exact gridBlank grid0 (a+1) (by omega)) (asUnary unary0 lenA) (by omega) fitA
  have eqA : put (lifted T S q) (D a+(v+1)) (some false)=setBank (lifted T S q) D a v:=by
    rw [show D a+(v+1)=D a+v+1 by omega]; exact bankTake grid0 ha lenA unary0 (by omega)
  rw [eqA,bankLifted grid below (by omega) ha] at decA
  let A:=setBank T D a v
  have gridA:=bankGrid grid a v ha
  have gridAHole:=liftedGrid gridA below (by omega : q ≤ S)
  obtain ⟨t0,h0,goAnchor⟩:=travel (k:=k) (lo:=lo) (P:=P) code.goAnchor gridAHole (by omega) (by decide) low0 upper
  have anchorA : BankUnary D A 7 (S-q):=bankOther grid 7 a (S-q) v (by decide) ha (Ne.symm a7) unary7
  have anchorHole:=liftedUnary gridA below (by omega : q ≤ S) (by decide) anchorA
  have dec7:=decrementPositive (k:=k) (lo:=lo) (hi:=P) code.decAnchor (lifted A S q) (D 7) r (S-q)
    (low0.trans (gridMono grid 0 7 (by decide) (by decide))) high7 (gridBlank gridAHole 7 (by decide))
    (by rw [← len7]; exact gridBlank gridAHole 8 (by decide)) (asUnary anchorHole len7) (by omega) fit7
  have rem : S-q=(S-q-1)+1:=by omega
  have eq7 : put (lifted A S q) (D 7+(S-q)) (some false)=setBank (lifted A S q) D 7 (S-q-1):=by
    have unary' : BankUnary D (lifted A S q) 7 ((S-q-1)+1):=by rwa [← rem]
    rw [rem,show D 7+(S-q-1+1)=D 7+(S-q-1)+1 by omega]
    exact bankTake gridAHole (by decide) len7 unary' (by omega)
  rw [eq7,bankLifted gridA below (by omega) (by decide)] at dec7
  have gridB:=bankGrid gridA 7 (S-q-1) (by decide)
  have corridorA:=bankCorridor grid corridor ha (by omega : H ≤ D 0) (v:=v)
  have arenaA:=bankArena grid arena ha d0 (v:=v)
  have corridorB:=bankCorridor gridA corridorA (by decide : 7<12) (by omega : H ≤ D 0) (v:=S-q-1)
  have arenaB:=bankArena gridA arenaA (by decide : 7<12) d0 (v:=S-q-1)
  have sourceB (i : Nat) (il : q < i) (iu : i < S) : ∃ bit,B i=some bit := by
    change ∃ bit,setBank (setBank T D a v) D 7 (S-q-1) i=some bit
    rw [bankBelow gridA (j:=7) (v:=S-q-1) (i:=i) (by decide) (by omega),
      bankBelow grid (j:=a) (v:=v) (i:=i) ha (by omega)]
    exact source i il iu
  have valueB : B q=some saved:=by
    change setBank (setBank T D a v) D 7 (S-q-1) q=some saved
    rw [bankBelow gridA (j:=7) (v:=S-q-1) (i:=q) (by decide) (by omega),
      bankBelow grid (j:=a) (v:=v) (i:=q) ha (by omega),savedCell]
  have gridHole:=liftedGrid gridB below (by omega : q ≤ S)
  have corridorHole:=liftedCorridor corridorB (by omega : q ≤ S)
  have arenaHole:=liftedArena arenaB (by omega : S < H) (by omega : q ≤ S)
  have hole : lifted B S q q=none:=liftedHere (by omega) (corridorEof corridorB)
  have occupied (i : Nat) (il : q < i) (iu : i < S) : ∃ bit,lifted B S q i=some bit:=by
    rw [liftedOld (by omega)]
    exact sourceB i il iu
  obtain ⟨t1,h1,seek⟩:=toSource (k:=k) (lo:=lo) (P:=P) code.seek gridHole corridorHole arenaHole (by decide) d0
    lower (by omega) (by
      constructor
      · intro h; cases h
      · intro h; omega) hole occupied upper
  have restore:=hop (k:=k) (lo:=lo) (hi:=P) code.hole code.lift q (q+1) (lifted B S q) (some saved) .right
    code.safeHole ⟨lower,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
    ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
    (by rw [hole]; exact code.restore) rfl
  have restoreEq : put (lifted B S q) q (some saved)=B:=by rw [← valueB]; exact restoreLifted
  rw [restoreEq] at restore
  have eofB : B S=none:=corridorEof corridorB
  have first:=pAppend decA (pAppend goAnchor (pAppend dec7 (pAppend seek restore)))
  by_cases physical : q+1 < S
  · obtain ⟨bit,hbit⟩:=sourceB (q+1) (by omega) physical
    have read:=hop (k:=k) (lo:=lo) (hi:=P) code.lift (if bit then code.return1 else code.return0)
      (q+1) (q+1) B none .stay code.safeLift
      ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
      ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
      (by rw [hbit]; exact forward_read_row code bit) rfl
    have liftEq : put B (q+1) none=lifted B S (q+1):=by dsimp only [lifted]; rw [if_pos physical]
    rw [liftEq] at read
    have gridNext:=liftedGrid gridB below (by omega : q+1 ≤ S)
    have corridorNext:=liftedCorridor corridorB (by omega : q+1 ≤ S)
    have arenaNext:=liftedArena arenaB (by omega : S < H) (by omega : q+1 ≤ S)
    have nextHole : lifted B S (q+1) (q+1)=none:=liftedHere (by omega) (corridorEof corridorB)
    have nextSource (i : Nat) (il : q+1 < i) (iu : i < S) : ∃ bit,lifted B S (q+1) i=some bit:=by
      rw [liftedOld (by omega)]
      exact sourceB i (by omega) iu
    have back : ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t
        (pNode (if bit then code.return1 else code.return0) (q+1) (lifted B S (q+1)))
        (pNode (if bit then next1 else next0) (D a) (lifted B S (q+1))) := by
      cases bit
      · exact fromSource (k:=k) (lo:=lo) (P:=P) code.back0 gridNext corridorNext arenaNext (by omega) d0 (by omega) physical nextHole nextSource upper
      · exact fromSource (k:=k) (lo:=lo) (P:=P) code.back1 gridNext corridorNext arenaNext (by omega) d0 (by omega) physical nextHole nextSource upper
    obtain ⟨t2,h2,back⟩:=back
    refine ⟨_,?_,Or.inl ⟨physical,bit,hbit,pAppend first (pAppend read back)⟩⟩
    nlinarith only [h0,h1,h2,highA,high7,fitA,fit7,Nat.zero_le (D a),Nat.zero_le (D 7)]
  · have endSource : q+1=S:=by omega
    have read:=hop (k:=k) (lo:=lo) (hi:=P) code.lift eofEntry (q+1) (q+1) B none .stay code.safeLift
      ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
      ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
      (by rw [endSource,eofB]; exact code.readEOF) rfl
    have unchanged : put B (q+1) none=B:=by
      have current:=putCurrent B (q+1)
      have cell : B (q+1)=none:=by rw [endSource]; exact corridorEof corridorB
      rwa [cell] at current
    rw [unchanged,endSource] at read
    obtain ⟨t2,h2,back⟩:=eofReturn (k:=k) (lo:=lo) (P:=P) code.eof gridB corridorB arenaB d0 (by omega) upper
    rw [endSource] at first
    have fullPath:=pAppend first read
    refine ⟨_,?_,Or.inr ⟨endSource,pAppend fullPath back⟩⟩
    nlinarith only [h0,h1,h2,highA,high7,fitA,fit7,Nat.zero_le (D a),Nat.zero_le (D 7)]
end FullIngressClosure
