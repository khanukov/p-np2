import Complexity.PrivateInterfaceLookupResolvedHalving
import FullIngressClosure.HalfFinishCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateHalving.bindings `FullIngressClosure.HalfIteration
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated halving identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem half_start {D T a b} (empty : BankUnary D T b 0) :
    halfTape T D a b 0 0=T := by
  have eq : burn T (D a) 0=T := by
    funext i
    dsimp only [burn]
    rw [if_neg (by omega)]
  dsimp only [halfTape]
  rw [eq,bankOriginal empty]
private theorem half_done {D T a b n v j} (len : D (a+1)=D a+n+1)
    (source : BankUnary D T a v) (vf : v ≤ n) :
    halfTape T D a b v j=setBank (setBank T D a 0) D b j := by
  dsimp only [halfTape]
  rw [burnDone source len vf]
private theorem pair_iterations {k lo P D a b state} (code : PairCode k a b state state)
    (T : Nat → Option Bool) (grid : Grid D T) (ha : a < 12) (hb : b < 12) (ab : a ≠ b)
    (n v c j m : Nat) (lenA : D (a+1)=D a+n+1) (lenB : D (b+1)=D b+n+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P) (source : BankUnary D T a v)
    (vf : v ≤ n) (remaining : c+2*m ≤ v) (room : j+m ≤ n) :
    ∃ t,t ≤ 64*m*(P+16) ∧ PPath k lo P t
      (pNode state (D a) (halfTape T D a b c j))
      (pNode state (D a) (halfTape T D a b (c+2*m) (j+m))) := by
  induction m with
  | zero =>
    refine ⟨0,by omega,?_⟩
    simp only [Nat.mul_zero,Nat.add_zero]
    exact pNil _ ⟨lower.trans (gridMono grid 0 a (by omega) (by omega)),
      (gridMono grid a 12 (by omega) le_rfl).trans upper⟩
  | succ m ih =>
    obtain ⟨t0,h0,path⟩:=ih (by omega) (by omega)
    obtain ⟨t1,h1,step⟩:=halvingPair code T grid ha hb ab n n v (c+2*m) (j+m)
      lenA lenB lower upper source vf (by omega) (by omega)
    have eqC : c+2*m+2=c+2*(m+1):=by omega
    have eqJ : j+m+1=j+(m+1):=by omega
    rw [eqC,eqJ] at step
    refine ⟨_,?_,pAppend path step⟩
    nlinarith only [h0,h1]
private structure HalveCode (k a b : Nat) (first loopState scanFirst scanLoop second back next : Fin (BodyIngress.machine k).stateCount) where
  firstPair : PairCode k a b first loopState
  nextPair : PairCode k a b loopState loopState
  finish : FinishCode k a b back next
  safeFirst : Safe k first
  safeLoop : Safe k loopState
  safeScanFirst : Safe k scanFirst
  safeScanLoop : Safe k scanLoop
  safeSecond : Safe k second
  enterFirst : (BodyIngress.machine k).step first none=(scanFirst,none,.right)
  passFirst : (BodyIngress.machine k).step scanFirst (some false)=(scanFirst,some false,.right)
  takeFirst : (BodyIngress.machine k).step scanFirst (some true)=(second,some false,.right)
  enterLoop : (BodyIngress.machine k).step loopState none=(scanLoop,none,.right)
  passLoop : (BodyIngress.machine k).step scanLoop (some false)=(scanLoop,some false,.right)
  takeLoop : (BodyIngress.machine k).step scanLoop (some true)=(second,some false,.right)
  oddFalse : (BodyIngress.machine k).step second (some false)=(back,some false,.left)
  oddNone : (BodyIngress.machine k).step second none=(back,none,.left)
  evenNone : (BodyIngress.machine k).step scanLoop none=(back,none,.left)
private theorem positive_half {k lo P D a b first loopState scanFirst scanLoop second back next}
    (code : HalveCode k a b first loopState scanFirst scanLoop second back next)
    (T : Nat → Option Bool) (grid : Grid D T) (ha : a < 12) (hb : b < 12)
    (ab : a ≠ b) (a2 : a ≠ 2) (b2 : b ≠ 2)
    (n r v u : Nat) (lenA : D (a+1)=D a+n+1) (lenB : D (b+1)=D b+n+1)
    (lenC : D 3=D 2+r+1) (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (source : BankUnary D T a v) (target : BankUnary D T b 0) (count : BankUnary D T 2 u)
    (positive : 0 < v) (vf : v ≤ n) (room : u < r) :
    ∃ t,t ≤ 128*(v+1)*(P+16) ∧ PPath k lo P t (pNode first (D a) T)
      (pNode next (D b) (setBank (setBank (setBank T D a 0) D b (v/2)) D 2 (u+1))) := by
  let q:=v/2
  have qv : q ≤ v:=Nat.div_le_self _ _
  have qr : 2*q ≤ v ∧ v ≤ 2*q+1:=by have h:=Nat.mod_add_div v 2; have h2:=Nat.mod_lt v (by decide : 0<2); omega
  have go : ∃ t,t ≤ (64*q+4)*(P+16) ∧ PPath k lo P t
      (pNode first (D a) T) (pNode back (D a) (halfTape T D a b v q)) := by
    by_cases zq : q=0
    · have lone : v=1:=by omega
      obtain ⟨t,price,path⟩:=oddFinish code.finish grid ha hb ab n v 0 0 lenA source vf (by omega) lower upper
        code.safeFirst code.safeScanFirst code.safeSecond code.enterFirst code.passFirst code.takeFirst code.oddFalse code.oddNone
      rw [half_start target] at path
      rw [zq]
      exact ⟨t,by omega,path⟩
    · obtain ⟨t0,h0,firstPath⟩:=halvingPair code.firstPair T grid ha hb ab n n v 0 0
        lenA lenB lower upper source vf (by omega) (by omega)
      rw [half_start target] at firstPath
      obtain ⟨t1,h1,rest⟩:=pair_iterations code.nextPair T grid ha hb ab n v 2 1 (q-1)
        lenA lenB lower upper source vf (by omega) (by omega)
      have eqC : 2+2*(q-1)=2*q:=by omega
      have eqJ : 1+(q-1)=q:=by omega
      rw [eqC,eqJ] at rest
      have finish : ∃ t,t ≤ 4*(P+16) ∧ PPath k lo P t
          (pNode loopState (D a) (halfTape T D a b (2*q) q))
          (pNode back (D a) (halfTape T D a b v q)) := by
        by_cases odd : v=2*q+1
        · exact oddFinish code.finish grid ha hb ab n v (2*q) q lenA source vf odd lower upper
            code.safeLoop code.safeScanLoop code.safeSecond code.enterLoop code.passLoop code.takeLoop code.oddFalse code.oddNone
        · have even : v=2*q:=by omega
          rw [← even]
          exact evenFinish code.finish grid ha hb ab n v q lenA source vf lower upper code.safeLoop code.safeScanLoop
            code.enterLoop code.passLoop code.evenNone
      obtain ⟨t2,h2,tail⟩:=finish
      refine ⟨_,?_,pAppend firstPath (pAppend rest tail)⟩
      nlinarith only [h0,h1,h2,show q-1+1=q by omega]
  obtain ⟨t0,h0,body⟩:=go
  have eq : halfTape T D a b v q=setBank (setBank T D a 0) D b q:=half_done lenA source vf
  rw [eq] at body
  have gridA:=bankGrid grid a 0 ha
  have gridB:=bankGrid gridA b q hb
  have countA : BankUnary D (setBank T D a 0) 2 u:=bankOther grid 2 a u 0 (by decide) ha (Ne.symm a2) count
  have countB : BankUnary D (setBank (setBank T D a 0) D b q) 2 u:=
    bankOther gridA 2 b u q (by decide) hb (Ne.symm b2) countA
  obtain ⟨t1,h1,tail⟩:=finishCount code.finish gridB ha hb r u lenC countB room lower upper
  refine ⟨_,?_,pAppend body tail⟩
  nlinarith only [h0,h1,qv]
end FullIngressClosure
