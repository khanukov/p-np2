import Complexity.PrivateInterfaceLookupResolvedSourceRound
import FullIngressClosure.SourceImage
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateSourceRound.bindings `FullIngressClosure.SourceBackRound
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated source-round identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private structure BackCode (k : Nat) (saved : Option Bool)
    (entry next0 next1 zero : Fin (BodyIngress.machine k).stateCount) where
  take : Fin (BodyIngress.machine k).stateCount
  hole : Fin (BodyIngress.machine k).stateCount
  lift : Fin (BodyIngress.machine k).stateCount
  return0 : Fin (BodyIngress.machine k).stateCount
  return1 : Fin (BodyIngress.machine k).stateCount
  dec : Decrement k entry take zero
  seek : ToHoleCode k 10 saved.isNone take hole
  safeHole : Safe k hole
  safeLift : Safe k lift
  restore : (BodyIngress.machine k).step hole none=(lift,saved,.left)
  read0 : (BodyIngress.machine k).step lift (some false)=(return0,none,.stay)
  read1 : (BodyIngress.machine k).step lift (some true)=(return1,none,.stay)
  back0 : SourceReturnCode k 10 return0 next0
  back1 : SourceReturnCode k 10 return1 next1
private theorem back_read_row {k saved entry next0 next1 zero}
    (code : BackCode k saved entry next0 next1 zero) (bit : Bool) :
    (BodyIngress.machine k).step code.lift (some bit)=
      (if bit then code.return1 else code.return0,none,.stay) := by
  cases bit with
  | false => exact code.read0
  | true => exact code.read1
private theorem back_round {k lo P D T S L H F Q q saved entry next0 next1 zero}
    (code : BackCode k saved entry next0 next1 zero) (grid : Grid D T)
    (corridor : Corridor T S L H) (arena : Arena T H F Q) (d0 : D 0=F+1)
    (lower : lo < q) (qs : q ≤ S) (savedCell : T q=saved) (virtual : saved.isNone=true ↔ q=S)
    (source : ∀ i,q-1 ≤ i → i < S → ∃ bit,T i=some bit)
    (w v : Nat) (len : D 11=D 10+w+1) (unary : BankUnary D T 10 (v+1))
    (fit : v+1 ≤ w) (upper : D 12 ≤ P) :
    ∃ bit t,t ≤ 32*(P+16) ∧ T (q-1)=some bit ∧ PPath k lo P t
      (pNode entry (D 10) (lifted T S q))
      (pNode (if bit then next1 else next0) (D 10) (lifted (setBank T D 10 v) S (q-1))) := by
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have below : S < D 0:=by omega
  have grid0:=liftedGrid grid below qs
  have unary0:=liftedUnary grid below qs (by decide) unary
  have low0 : lo ≤ D 0:=by omega
  have high10 : D 10+w+1 ≤ P:=by rw [← len]; exact (gridMono grid 11 12 (by decide) le_rfl).trans upper
  have decPath:=decrementPositive (k:=k) (lo:=lo) (hi:=P) code.dec (lifted T S q) (D 10) w (v+1)
    (low0.trans (gridMono grid 0 10 (by decide) (by decide))) high10 (gridBlank grid0 10 (by decide)) (by rw [← len]; exact gridBlank grid0 11 (by decide))
    (asUnary unary0 len) (by omega) fit
  have decEq : put (lifted T S q) (D 10+(v+1)) (some false)=setBank (lifted T S q) D 10 v := by
    rw [show D 10+(v+1)=D 10+v+1 by omega]
    exact bankTake grid0 (by decide) len unary0 (by omega)
  rw [decEq,bankLifted grid below qs (by decide)] at decPath
  let B:=setBank T D 10 v
  have gridB:=bankGrid grid 10 v (by decide)
  have corridorB:=bankCorridor grid corridor (by decide : 10<12) (by omega : H ≤ D 0) (v:=v)
  have arenaB:=bankArena grid arena (by decide : 10<12) d0 (v:=v)
  have valueB : B q=saved:=by
    change setBank T D 10 v q=saved
    rw [bankBelow grid (j:=10) (v:=v) (i:=q) (by decide) (by omega),savedCell]
  have sourceB (i : Nat) (il : q-1 ≤ i) (iu : i < S) : ∃ bit,B i=some bit := by
    change ∃ bit,setBank T D 10 v i=some bit
    rw [bankBelow grid (j:=10) (v:=v) (i:=i) (by decide) (by omega)]
    exact source i il iu
  have gridHole:=liftedGrid gridB below qs
  have corridorHole:=liftedCorridor corridorB qs
  have arenaHole:=liftedArena arenaB (by omega : S < H) qs
  have hole : lifted B S q q=none:=liftedHere qs (corridorEof corridorB)
  have remaining (i : Nat) (il : q < i) (iu : i < S) : ∃ bit,lifted B S q i=some bit := by
    rw [liftedOld (by omega)]
    exact sourceB i (by omega) iu
  obtain ⟨t0,h0,seek⟩:=toSource (k:=k) (lo:=lo) (P:=P) code.seek gridHole corridorHole arenaHole (by decide) d0
    (by omega) qs virtual hole remaining upper
  have restore:=hop (k:=k) (lo:=lo) (hi:=P) code.hole code.lift q (q-1) (lifted B S q) saved .left
    code.safeHole ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
    ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
    (by rw [hole]; exact code.restore) rfl
  have restored : put (lifted B S q) q saved=B:=by rw [← valueB]; exact restoreLifted
  rw [restored] at restore
  obtain ⟨bit,hbit⟩:=sourceB (q-1) le_rfl (by omega)
  have read:=hop (k:=k) (lo:=lo) (hi:=P) code.lift (if bit then code.return1 else code.return0)
    (q-1) (q-1) B none .stay code.safeLift
    ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
    ⟨by omega,(by have h:=(gridMono grid 0 12 (by decide) le_rfl).trans upper; omega)⟩
    (by rw [hbit]; exact back_read_row code bit) rfl
  have liftEq : put B (q-1) none=lifted B S (q-1):=by
    dsimp only [lifted]
    rw [if_pos (by omega)]
  rw [liftEq] at read
  have gridNext:=liftedGrid gridB below (by omega : q-1 ≤ S)
  have corridorNext:=liftedCorridor corridorB (by omega : q-1 ≤ S)
  have arenaNext:=liftedArena arenaB (by omega : S < H) (by omega : q-1 ≤ S)
  have nextHole : lifted B S (q-1) (q-1)=none:=liftedHere (by omega) (corridorEof corridorB)
  have nextSource (i : Nat) (il : q-1 < i) (iu : i < S) : ∃ bit,lifted B S (q-1) i=some bit := by
    rw [liftedOld (by omega)]
    exact sourceB i (by omega) iu
  have back : ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t
      (pNode (if bit then code.return1 else code.return0) (q-1) (lifted B S (q-1)))
      (pNode (if bit then next1 else next0) (D 10) (lifted B S (q-1))) := by
    cases bit
    · exact fromSource (k:=k) (lo:=lo) (P:=P) code.back0 gridNext corridorNext arenaNext (by decide) d0 (by omega) (by omega) nextHole nextSource upper
    · exact fromSource (k:=k) (lo:=lo) (P:=P) code.back1 gridNext corridorNext arenaNext (by decide) d0 (by omega) (by omega) nextHole nextSource upper
  obtain ⟨t1,h1,back⟩:=back
  have originalBit : T (q-1)=some bit:=by
    change setBank T D 10 v (q-1)=some bit at hbit
    rwa [bankBelow grid (j:=10) (v:=v) (i:=q-1) (by decide) (by omega)] at hbit
  refine ⟨bit,_,?_,originalBit,pAppend decPath (pAppend seek (pAppend restore (pAppend read back)))⟩
  nlinarith only [h0,h1,high10,fit,Nat.zero_le (D 10)]
end FullIngressClosure
