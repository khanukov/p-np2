import Complexity.PrivateInterfaceLookupResolvedSourceScan
import FullIngressClosure.SourceForwardCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateSourceScan.bindings `FullIngressClosure.SourceSkipDriver
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated source-scan identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private def skipTape (T : Nat → Option Bool) (D : Nat → Nat) (a v u : Nat) : Nat → Option Bool :=
  setBank (setBank T D a v) D 7 u
private theorem shadow_skip (T : Nat → Option Bool) (D : Nat → Nat) (a v u V U : Nat) :
    skipTape (skipTape T D a v u) D a V U=skipTape T D a V U := by
  funext i
  dsimp only [skipTape,setBank]
  by_cases right : D 7 < i ∧ i < D 8
  · simp only [if_pos right]
  · by_cases left : D a < i ∧ i < D (a+1)
    · simp only [if_neg right,if_pos left]
    · simp only [if_neg right,if_neg left]
private structure SkipCodes (k a b : Nat) (entry out : Bool → Fin (BodyIngress.machine k).stateCount)
    (eofEntry eofOut : Fin (BodyIngress.machine k).stateCount) where
  zeroState : Bool → Fin (BodyIngress.machine k).stateCount
  forward : ∀ bit,ForwardCode k a bit (entry bit) (entry false) (entry true) (zeroState bit) eofEntry eofOut
  zeroTravel : ∀ bit,Travel k a b (zeroState bit) (out bit)
private theorem skip_driver {k lo P D T S L H F Q p a b entry out eofEntry eofOut}
    (code : SkipCodes k a b entry out eofEntry eofOut) (source : Fin S → Bool)
    (grid : Grid D T) (corridor : Corridor T S L H) (arena : Arena T H F Q)
    (d0 : D 0=F+1) (ha : a < 12) (hb : b ≤ 12) (a7 : a ≠ 7) (lower : lo ≤ p)
    (cells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (w r : Nat) (lenA : D (a+1)=D a+w+1) (len7 : D 8=D 7+r+1) (upper : D 12 ≤ P)
    (v : Nat) : ∀ q,p ≤ q → ∀ qs:q < S,v ≤ w → S-q ≤ r →
    ∃ t,t ≤ (64*v+4)*(P+16) ∧
      ((∃ physical:q+v < S,PPath k lo P t
        (pNode (entry (source ⟨q,qs⟩)) (D a) (lifted (skipTape T D a v (S-q)) S q))
        (pNode (out (source ⟨q+v,physical⟩)) (D b) (lifted (skipTape T D a 0 (S-(q+v))) S (q+v)))) ∨
      (S ≤ q+v ∧ PPath k lo P t
        (pNode (entry (source ⟨q,qs⟩)) (D a) (lifted (skipTape T D a v (S-q)) S q))
        (pNode eofOut (D 0) (skipTape T D a (v-(S-q)) 0)))) := by
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have highA : D a+w+1 ≤ P:=by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
  induction v with
  | zero =>
    intro q pq qs _ _
    simp only [Nat.add_zero,Nat.mul_zero,Nat.zero_add]
    let A:=setBank T D a 0
    let B:=skipTape T D a 0 (S-q)
    have below : S < D 0:=by omega
    have gridA:=bankGrid grid a 0 ha
    have gridB:=bankGrid gridA 7 (S-q) (by decide)
    have gridHole:=liftedGrid gridB below (by omega : q ≤ S)
    have unaryB : BankUnary D B a 0:=bankOther gridA a 7 0 (S-q) ha (by decide) a7 (bankUnary T D a 0)
    have unaryHole:=liftedUnary gridB below (by omega : q ≤ S) ha unaryB
    have dec:=decrementZero (k:=k) (lo:=lo) (hi:=P) (forwardDec (code.forward (source ⟨q,qs⟩)))
      (lifted B S q) (D a) w
      (by have h:=gridMono grid 0 a (by omega) (by omega); omega) highA
      (gridBlank gridHole a (by omega)) (by rw [← lenA]; exact gridBlank gridHole (a+1) (by omega)) (asUnary unaryHole lenA)
    obtain ⟨t,price,path⟩:=travel (k:=k) (lo:=lo) (P:=P) (code.zeroTravel (source ⟨q,qs⟩)) gridHole (by omega) hb (by omega) upper
    exact ⟨_,by omega,Or.inl ⟨qs,pAppend dec path⟩⟩
  | succ v ih =>
    intro q pq qs fit fitsR
    let A:=setBank T D a (v+1)
    let B:=skipTape T D a (v+1) (S-q)
    have below : S < D 0:=by omega
    have gridA:=bankGrid grid a (v+1) ha
    have gridB:=bankGrid gridA 7 (S-q) (by decide)
    have corridorA:=bankCorridor grid corridor ha (by omega : H ≤ D 0) (v:=v+1)
    have arenaA:=bankArena grid arena ha d0 (v:=v+1)
    have corridorB:=bankCorridor gridA corridorA (by decide : 7<12) (by omega : H ≤ D 0) (v:=S-q)
    have arenaB:=bankArena gridA arenaA (by decide : 7<12) d0 (v:=S-q)
    have old (i : Nat) (iu : i < S) : B i=T i:=by
      change setBank (setBank T D a (v+1)) D 7 (S-q) i=T i
      rw [bankBelow gridA (j:=7) (v:=S-q) (i:=i) (by decide) (by omega),
        bankBelow grid (j:=a) (v:=v+1) (i:=i) ha (by omega)]
    have unaryA : BankUnary D B a (v+1):=bankOther gridA a 7 (v+1) (S-q) ha (by decide) a7 (bankUnary T D a (v+1))
    have unary7 : BankUnary D B 7 (S-q):=bankUnary _ D 7 (S-q)
    obtain ⟨t0,h0,step⟩:=forwardRound (k:=k) (lo:=lo) (P:=P) (code.forward (source ⟨q,qs⟩)) gridB corridorB arenaB d0 ha a7
      (by omega) qs (by change B q=some (source ⟨q,qs⟩); rw [old q qs]; exact cells q pq qs)
      (by intro i il iu; exact ⟨source ⟨i,iu⟩,by change B i=some (source ⟨i,iu⟩); rw [old i iu]; exact cells i (by omega) iu⟩)
      w r v lenA len7 unaryA unary7 fit fitsR upper
    change (q+1 < S ∧ ∃ bit,skipTape B D a v (S-q-1) (q+1)=some bit ∧ PPath k lo P t0 _
      (pNode (if bit then entry true else entry false) (D a) (lifted (skipTape B D a v (S-q-1)) S (q+1)))) ∨
      (q+1=S ∧ PPath k lo P t0 _ (pNode eofOut (D 0) (skipTape B D a v (S-q-1)))) at step
    have shadow : skipTape B D a v (S-q-1)=skipTape T D a v (S-(q+1)):=by
      change skipTape (skipTape T D a (v+1) (S-q)) D a v (S-q-1)=_
      rw [shadow_skip,show S-q-1=S-(q+1) by omega]
    rw [shadow] at step
    rcases step with ⟨physical,bit,read,path0⟩ | ⟨eof,path0⟩
    · have nextBit : bit=source ⟨q+1,physical⟩:=by
        have oldCell : skipTape T D a v (S-(q+1)) (q+1)=some (source ⟨q+1,physical⟩):=by
          change setBank (setBank T D a v) D 7 (S-(q+1)) (q+1)=_
          rw [bankBelow (bankGrid grid a v ha) (j:=7) (v:=S-(q+1)) (i:=q+1) (by decide) (by omega),
            bankBelow grid (j:=a) (v:=v) (i:=q+1) ha (by omega)]
          exact cells (q+1) (by omega) physical
        exact Option.some.inj (read.symm.trans oldCell)
      have state : (if bit then entry true else entry false)=entry (source ⟨q+1,physical⟩):=by rw [nextBit]; cases source ⟨q+1,physical⟩ <;> rfl
      rw [state] at path0
      obtain ⟨t1,h1,tail⟩:=ih (q+1) (by omega) physical (by omega) (by omega)
      have sum : q+1+v=q+(v+1):=by omega
      have residue : v-(S-(q+1))=(v+1)-(S-q):=by omega
      rcases tail with ⟨phys,path1⟩ | ⟨past,path1⟩
      · have physicalOut : q+(v+1) < S:=by omega
        have indexEq : (⟨q+1+v,phys⟩ : Fin S)=⟨q+(v+1),physicalOut⟩:=Fin.ext sum
        rw [indexEq,sum] at path1
        refine ⟨_,?_,Or.inl ⟨physicalOut,pAppend path0 path1⟩⟩
        nlinarith only [h0,h1]
      · rw [sum] at past
        rw [residue] at path1
        refine ⟨_,?_,Or.inr ⟨past,pAppend path0 path1⟩⟩
        nlinarith only [h0,h1]
    · have anchor : S-(q+1)=0:=by omega
      have residue : (v+1)-(S-q)=v:=by omega
      rw [anchor] at path0
      refine ⟨t0,?_,Or.inr ⟨by omega,?_⟩⟩
      · nlinarith only [h0]
      · rw [residue]
        exact path0
end FullIngressClosure
