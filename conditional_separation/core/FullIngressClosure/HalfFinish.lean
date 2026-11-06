import Complexity.PrivateInterfaceLookupResolvedHalving
import FullIngressClosure.HalfCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateHalving.bindings `FullIngressClosure.HalfFinish
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated halving identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem burn_done {D T a w v} (source : BankUnary D T a v)
    (len : D (a+1)=D a+w+1) (vf : v ≤ w) :
    burn T (D a) v=setBank T D a 0 := by
  funext i
  dsimp only [burn,setBank]
  by_cases inside : D a < i ∧ i < D (a+1)
  · rw [if_pos inside]
    by_cases used : i ≤ D a+v
    · rw [if_pos ⟨inside.1,used⟩,decide_eq_false (by omega)]
    · rw [if_neg (by omega),source i inside.1 inside.2,decide_eq_false (by omega),decide_eq_false (by omega)]
  · rw [if_neg inside,if_neg (by omega)]
private structure FinishCode (k a b : Nat) (back next : Fin (BodyIngress.machine k).stateCount) where
  toCount : Fin (BodyIngress.machine k).stateCount
  atCount : Fin (BodyIngress.machine k).stateCount
  afterCount : Fin (BodyIngress.machine k).stateCount
  safeBack : Safe k back
  retreat : ∀ bit,(BodyIngress.machine k).step back (some bit)=(back,some bit,.left)
  stop : (BodyIngress.machine k).step back none=(toCount,none,.stay)
  outward : Travel k a 2 toCount atCount
  count : Increment k atCount afterCount
  inward : Travel k 2 b afterCount next
private theorem finish_count {k lo P D T a b back next} (code : FinishCode k a b back next)
    (grid : Grid D T) (ha : a < 12) (hb : b < 12) (r u : Nat)
    (len : D 3=D 2+r+1) (unary : BankUnary D T 2 u) (room : u < r)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t (pNode back (D a) T)
      (pNode next (D b) (setBank T D 2 (u+1))) := by
  have lowA:=lower.trans (gridMono grid 0 a (by omega) (by omega))
  have highA:=(gridMono grid a 12 (by omega) le_rfl).trans upper
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) back code.toCount (D a) (D a) T .stay
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 ⟨lowA,highA⟩ ⟨lowA,highA⟩
    (by rw [gridBlank grid a (by omega)]; exact code.stop) rfl
  obtain ⟨t0,h0,outward⟩:=travel code.outward grid (by omega) (by decide) lower upper
  have fit : D 2+r+1 ≤ P:=by rw [← len]; exact (gridMono grid 3 12 (by decide) le_rfl).trans upper
  have add:=increment (k:=k) (lo:=lo) (hi:=P) code.count T (D 2) r u
    (lower.trans (gridMono grid 0 2 (by decide) (by decide))) fit
    (gridBlank grid 2 (by decide)) (asUnary unary len) room
  rw [bankAdd grid (by decide) len unary room] at add
  obtain ⟨t1,h1,inward⟩:=travel code.inward (bankGrid grid 2 (u+1) (by decide)) (by decide) (by omega) lower upper
  refine ⟨_,?_,pAppend stop (pAppend outward (pAppend add inward))⟩
  omega
private theorem odd_finish {k lo P D T a b entry scan second back next}
    (code : FinishCode k a b back next) (grid : Grid D T) (ha : a < 12) (hb : b < 12) (ab : a ≠ b)
    (wa v c j : Nat) (len : D (a+1)=D a+wa+1) (source : BankUnary D T a v)
    (vf : v ≤ wa) (last : v=c+1) (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (se : Safe k entry) (ss : Safe k scan) (sd : Safe k second)
    (enter : (BodyIngress.machine k).step entry none=(scan,none,.right))
    (pass : (BodyIngress.machine k).step scan (some false)=(scan,some false,.right))
    (take : (BodyIngress.machine k).step scan (some true)=(second,some false,.right))
    (stopFalse : (BodyIngress.machine k).step second (some false)=(back,some false,.left))
    (stopNone : (BodyIngress.machine k).step second none=(back,none,.left)) :
    ∃ t,t ≤ 4*(P+16) ∧ PPath k lo P t
      (pNode entry (D a) (halfTape T D a b c j)) (pNode back (D a) (halfTape T D a b v j)) := by
  let E (u : Nat):=halfTape T D a b u j
  have low:=lower.trans (gridMono grid 0 a (by omega) (by omega))
  have high : D a+wa+1 ≤ P:=by rw [← len]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
  have grid0:=halfGrid grid ha hb len c j (by omega)
  have grid1:=halfGrid grid ha hb len v j vf
  have blank0 : E c (D a)=none:=gridBlank grid0 a (by omega)
  have blank1 : E v (D (a+1))=none:=gridBlank grid1 (a+1) (by omega)
  have digit (u i : Nat) (uw : u ≤ wa) (il : D a < i) (iu : i < D (a+1)) :
      E u i=some (decide (D a+u < i ∧ i-D a ≤ v)):=halfSource grid ha hb ab len source uw i il iu
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry scan (D a) (D a+1) (E c) .right
    ⟨se.1,se.2.1⟩ se.2.2 ⟨low,by omega⟩ ⟨by omega,by omega⟩
    (by rw [blank0]; exact enter) rfl
  have skip:=pSweepR (k:=k) (lo:=lo) (hi:=P) scan (E c) (D a+1) c (by omega) (by omega)
    ⟨ss.1,ss.2.1⟩ ss.2.2 (by
      intro i il iu
      rw [digit _ i (by omega) (by omega) (by omega),decide_eq_false (by omega)]
      exact pass)
  rw [show D a+1+c=D a+c+1 by omega] at skip
  have take1:=hop (k:=k) (lo:=lo) (hi:=P) scan second (D a+c+1) (D a+c+2) (E c) (some false) .right
    ss ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by
      rw [digit _ _ (by omega) (by omega) (by omega),decide_eq_true (by omega)]
      exact take) rfl
  have eq1 : put (E c) (D a+c+1) (some false)=E v := by
    rw [show v=c+1 by omega]
    exact halfBurn grid ha hb ab len (by omega)
  rw [eq1] at take1
  have step : (BodyIngress.machine k).step second (E v (D a+c+2))=(back,E v (D a+c+2),.left) := by
    by_cases edge : v=wa
    · have h : D a+c+2=D (a+1):=by omega
      rw [h,blank1]
      exact stopNone
    · rw [digit _ _ vf (by omega) (by omega),decide_eq_false (by omega)]
      exact stopFalse
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) second back (D a+c+2) (D a+c+1) (E v) .left
    ⟨sd.1,sd.2.1⟩ sd.2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ step (by simp [dest])
  have retreat:=pSweepL (k:=k) (lo:=lo) (hi:=P) back (E v) (D a) (c+1) low (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i il iu
      obtain ⟨bit,hbit⟩:=gridCells grid1 a i ha il (by omega)
      change E v i=some bit at hbit
      rw [hbit]; exact code.retreat bit)
  rw [show D a+(c+1)=D a+c+1 by omega] at retreat
  refine ⟨_,?_,pAppend first (pAppend skip (pAppend take1 (pAppend stop retreat)))⟩
  omega
private theorem even_finish {k lo P D T a b entry scan back next}
    (code : FinishCode k a b back next) (grid : Grid D T) (ha : a < 12) (hb : b < 12) (ab : a ≠ b)
    (wa v j : Nat) (len : D (a+1)=D a+wa+1) (source : BankUnary D T a v)
    (vf : v ≤ wa) (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (se : Safe k entry) (ss : Safe k scan)
    (enter : (BodyIngress.machine k).step entry none=(scan,none,.right))
    (pass : (BodyIngress.machine k).step scan (some false)=(scan,some false,.right))
    (stopNone : (BodyIngress.machine k).step scan none=(back,none,.left)) :
    ∃ t,t ≤ 4*(P+16) ∧ PPath k lo P t
      (pNode entry (D a) (halfTape T D a b v j)) (pNode back (D a) (halfTape T D a b v j)) := by
  let E:=halfTape T D a b v j
  have low:=lower.trans (gridMono grid 0 a (by omega) (by omega))
  have high : D a+wa+1 ≤ P:=by rw [← len]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
  have grid1:=halfGrid grid ha hb len v j vf
  have blank0 : E (D a)=none:=gridBlank grid1 a (by omega)
  have blank1 : E (D (a+1))=none:=gridBlank grid1 (a+1) (by omega)
  have digit (i : Nat) (il : D a < i) (iu : i < D (a+1)) :
      E i=some (decide (D a+v < i ∧ i-D a ≤ v)):=halfSource grid ha hb ab len source vf i il iu
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry scan (D a) (D a+1) E .right
    ⟨se.1,se.2.1⟩ se.2.2 ⟨low,by omega⟩ ⟨by omega,by omega⟩
    (by rw [blank0]; exact enter) rfl
  have skip:=pSweepR (k:=k) (lo:=lo) (hi:=P) scan E (D a+1) wa (by omega) (by omega)
    ⟨ss.1,ss.2.1⟩ ss.2.2 (by
      intro i il iu
      rw [digit i (by omega) (by omega),decide_eq_false (by omega)]
      exact pass)
  rw [show D a+1+wa=D a+wa+1 by omega] at skip
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) scan back (D a+wa+1) (D a+wa) E .left
    ⟨ss.1,ss.2.1⟩ ss.2.2 ⟨by omega,high⟩ ⟨by omega,by omega⟩
    (by rw [← len,blank1]; exact stopNone) (by simp [dest])
  have retreat:=pSweepL (k:=k) (lo:=lo) (hi:=P) back E (D a) wa low (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i il iu
      obtain ⟨bit,hbit⟩:=gridCells grid1 a i ha il (by omega)
      change E i=some bit at hbit
      rw [hbit]; exact code.retreat bit)
  exact ⟨_,by omega,pAppend first (pAppend skip (pAppend stop retreat))⟩
end FullIngressClosure
