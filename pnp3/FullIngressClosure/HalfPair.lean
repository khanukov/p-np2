import FullIngressClosure.Move
import FullIngressClosure.Padding
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("BodyIngress.Native","BodyIngress","dest","dest"),
      ("BodyIngress.Native","BodyIngress","keep","pKeep"),
      ("BodyIngress.Native","BodyIngress","sweepR","pSweepR"),
      ("BodyIngress.Native","BodyIngress","sweepL","pSweepL"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mk","gridMk"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.rise","gridRise"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.cells","gridCells"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Paths","FullIngressClosure","hop","hop"),
      ("FullIngressClosure.Move","FullIngressClosure","Travel","Travel"),
      ("FullIngressClosure.Move","FullIngressClosure","travel","travel"),
      ("FullIngressClosure.Move","FullIngressClosure","asUnary","asUnary"),
      ("FullIngressClosure.Counters","FullIngressClosure","Increment","Increment"),
      ("FullIngressClosure.Counters","FullIngressClosure","increment","increment"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_disjoint","bankDisjoint"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_grid","bankGrid"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_unary","bankUnary"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_add","bankAdd"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_idempotent","bankIdempotent"),
      ("FullIngressClosure.Padding","FullIngressClosure","prefixFalse","burn"),
      ("FullIngressClosure.Padding","FullIngressClosure","prefix_put","burnPut") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique literal halving-pair term {mod}/{key}: {found.map Prod.fst}"
private theorem burn_grid {D T a w} (grid : Grid D T) (ha : a < 12)
    (len : D (a+1)=D a+w+1) (c : Nat) (cw : c ≤ w) : Grid D (burn T (D a) c) := by
  refine gridMk (gridRise grid) (gridMono grid) ?_ ?_
  · intro j hj
    have outside : ¬(D a < D j ∧ D j ≤ D a+c) := by
      by_cases order : j ≤ a
      · have h:=gridMono grid j a order (by omega); omega
      · have h:=gridMono grid (a+1) j (by omega) hj; omega
    dsimp only [burn]
    rw [if_neg outside]
    exact gridBlank grid j hj
  · intro j i hj il iu
    by_cases hit : D a < i ∧ i ≤ D a+c
    · exact ⟨false,by dsimp only [burn]; rw [if_pos hit]⟩
    · dsimp only [burn]
      rw [if_neg hit]
      exact gridCells grid j i hj il iu
private def halfTape (T : Nat → Option Bool) (D : Nat → Nat) (a b c j : Nat) : Nat → Option Bool :=
  setBank (burn T (D a) c) D b j
private theorem half_grid {D T a b w} (grid : Grid D T) (ha : a < 12) (hb : b < 12)
    (len : D (a+1)=D a+w+1) (c j : Nat) (cw : c ≤ w) : Grid D (halfTape T D a b c j) :=
  bankGrid (burn_grid grid ha len c cw) b j hb
private theorem half_source {D T a b w v c j} (grid : Grid D T) (ha : a < 12) (hb : b < 12)
    (ab : a ≠ b) (_len : D (a+1)=D a+w+1) (source : BankUnary D T a v) (_cw : c ≤ w)
    (i : Nat) (il : D a < i) (iu : i < D (a+1)) :
    halfTape T D a b c j i=some (decide (D a+c < i ∧ i-D a ≤ v)) := by
  have outside:=bankDisjoint grid ha hb ab il iu
  dsimp only [halfTape,setBank,burn]
  rw [if_neg outside]
  by_cases old : i ≤ D a+c
  · rw [if_pos ⟨il,old⟩,decide_eq_false (by omega)]
  · rw [if_neg (by omega),source i il iu]
    congr 1
    apply decide_eq_decide.mpr
    omega
private theorem half_burn {D T a b w c j} (grid : Grid D T) (ha : a < 12) (hb : b < 12)
    (ab : a ≠ b) (len : D (a+1)=D a+w+1) (room : c < w) :
    put (halfTape T D a b c j) (D a+c+1) (some false)=halfTape T D a b (c+1) j := by
  have outside:=bankDisjoint grid ha hb ab (by omega : D a < D a+c+1) (by omega : D a+c+1 < D (a+1))
  funext i
  by_cases hit : i=D a+c+1
  · subst i
    dsimp only [put,halfTape,setBank,burn]
    rw [if_pos rfl,if_neg outside,if_pos (by omega)]
  · have point:=congrFun (burnPut T (D a) c) i
    dsimp only [put] at point
    rw [if_neg hit] at point
    dsimp only [put,halfTape,setBank]
    rw [if_neg hit]
    by_cases other : D b < i ∧ i < D (b+1)
    · rw [if_pos other,if_pos other]
    · rw [if_neg other,if_neg other]
      exact point
private structure PairCode (k a b : Nat) (entry loopState : Fin (BodyIngress.machine k).stateCount) where
  scan : Fin (BodyIngress.machine k).stateCount
  second : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  toB : Fin (BodyIngress.machine k).stateCount
  atB : Fin (BodyIngress.machine k).stateCount
  toA : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeScan : Safe k scan
  safeSecond : Safe k second
  safeBack : Safe k back
  enter : (BodyIngress.machine k).step entry none=(scan,none,.right)
  scanFalse : (BodyIngress.machine k).step scan (some false)=(scan,some false,.right)
  takeFirst : (BodyIngress.machine k).step scan (some true)=(second,some false,.right)
  takeSecond : (BodyIngress.machine k).step second (some true)=(back,some false,.left)
  returnSome : ∀ value,(BodyIngress.machine k).step back (some value)=(back,some value,.left)
  returnBlank : (BodyIngress.machine k).step back none=(toB,none,.stay)
  outward : Travel k a b toB atB
  append : Increment k atB toA
  inward : Travel k b a toA loopState
private theorem halving_pair {k lo P D a b entry loopState} (code : PairCode k a b entry loopState)
    (T : Nat → Option Bool) (grid : Grid D T) (ha : a < 12) (hb : b < 12) (ab : a ≠ b)
    (wa wb v c j : Nat) (lenA : D (a+1)=D a+wa+1) (lenB : D (b+1)=D b+wb+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P) (source : BankUnary D T a v)
    (vf : v ≤ wa) (remaining : c+2 ≤ v) (jf : j < wb) :
    ∃ t,t ≤ 64*(P+16) ∧ PPath k lo P t
      (pNode entry (D a) (halfTape T D a b c j))
      (pNode loopState (D a) (halfTape T D a b (c+2) (j+1))) := by
  let E (u : Nat):=halfTape T D a b u j
  have lowA:=lower.trans (gridMono grid 0 a (by omega) (by omega))
  have fitA : D a+wa+1 ≤ P:=by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
  have fitB : D b+wb+1 ≤ P:=by rw [← lenB]; exact (gridMono grid (b+1) 12 (by omega) le_rfl).trans upper
  have grid0:=half_grid grid ha hb lenA c j (by omega)
  have grid1:=half_grid grid ha hb lenA (c+1) j (by omega)
  have grid2:=half_grid grid ha hb lenA (c+2) j (by omega)
  have digit (u i : Nat) (uw : u ≤ wa) (il : D a < i) (iu : i < D (a+1)) :
      E u i=some (decide (D a+u < i ∧ i-D a ≤ v)):=half_source grid ha hb ab lenA source uw i il iu
  have blank0 : E c (D a)=none:=gridBlank grid0 a (by omega)
  have blank2 : E (c+2) (D a)=none:=gridBlank grid2 a (by omega)
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry code.scan (D a) (D a+1) (E c) .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2 ⟨lowA,by omega⟩ ⟨by omega,by omega⟩
    (by rw [blank0]; exact code.enter) rfl
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=P) code.scan (E c) (D a+1) c (by omega) (by omega)
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2 (by
      intro i il iu
      rw [digit _ i (by omega) (by omega) (by omega),decide_eq_false (by omega)]
      exact code.scanFalse)
  rw [show D a+1+c=D a+c+1 by omega] at scan
  have take1:=hop (k:=k) (lo:=lo) (hi:=P) code.scan code.second (D a+c+1) (D a+c+2) (E c) (some false) .right
    code.safeScan ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by
      rw [digit _ _ (by omega) (by omega) (by omega),decide_eq_true (by omega)]
      exact code.takeFirst) rfl
  have eq1 : put (E c) (D a+c+1) (some false)=E (c+1):=half_burn grid ha hb ab lenA (by omega)
  rw [eq1] at take1
  have take2:=hop (k:=k) (lo:=lo) (hi:=P) code.second code.back (D a+c+2) (D a+c+1) (E (c+1)) (some false) .left
    code.safeSecond ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by
      rw [digit _ _ (by omega) (by omega) (by omega),decide_eq_true (by omega)]
      exact code.takeSecond) (by simp [dest])
  have eq2 : put (E (c+1)) (D a+c+2) (some false)=E (c+2) := by
    rw [show D a+c+2=D a+(c+1)+1 by omega]
    exact half_burn grid ha hb ab lenA (by omega)
  rw [eq2] at take2
  have back:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.back (E (c+2)) (D a) (c+1) lowA (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i il iu
      obtain ⟨bit,hbit⟩:=gridCells grid2 a i ha il (by omega)
      change E (c+2) i=some bit at hbit
      rw [hbit]; exact code.returnSome bit)
  rw [show D a+(c+1)=D a+c+1 by omega] at back
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.back code.toB (D a) (D a) (E (c+2)) .stay
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 ⟨lowA,by omega⟩ ⟨lowA,by omega⟩
    (by rw [blank2]; exact code.returnBlank) rfl
  obtain ⟨t0,h0,go⟩:=travel code.outward grid2 (by omega) (by omega) lower upper
  have unaryB : BankUnary D (E (c+2)) b j:=bankUnary (burn T (D a) (c+2)) D b j
  have add:=increment (k:=k) (lo:=lo) (hi:=P) code.append (E (c+2)) (D b) wb j
    (lower.trans (gridMono grid 0 b (by omega) (by omega))) fitB (gridBlank grid2 b (by omega)) (asUnary unaryB lenB) jf
  have eqAdd : put (E (c+2)) (D b+j+1) (some true)=setBank (E (c+2)) D b (j+1):=
    bankAdd grid2 hb lenB unaryB jf
  rw [eqAdd] at add
  have eq : setBank (E (c+2)) D b (j+1)=halfTape T D a b (c+2) (j+1):=bankIdempotent _ D b j (j+1)
  rw [eq] at add
  have grid3:=half_grid grid ha hb lenA (c+2) (j+1) (by omega)
  obtain ⟨t1,h1,come⟩:=travel code.inward grid3 (by omega) (by omega) lower upper
  have path:=pAppend first (pAppend scan (pAppend take1 (pAppend take2 (pAppend back (pAppend stop (pAppend go (pAppend add come)))))))
  refine ⟨_,?_,path⟩
  nlinarith only [h0,h1,fitA,fitB,remaining,vf,jf,Nat.zero_le (D a),Nat.zero_le (D b)]
end FullIngressClosure
