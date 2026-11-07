import FullIngressClosure.Workspace
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
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR","RouteR"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL","RouteL"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.span","rSpan"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.span","lSpan"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.execute","routeR"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.execute","routeL"),
      ("FullIngressClosure.Counters","FullIngressClosure","Unary","NatUnary"),
      ("FullIngressClosure.Counters","FullIngressClosure","Increment","Increment"),
      ("FullIngressClosure.Counters","FullIngressClosure","Decrement","Decrement"),
      ("FullIngressClosure.Counters","FullIngressClosure","increment","increment"),
      ("FullIngressClosure.Counters","FullIngressClosure","decrement_positive","decrementPositive"),
      ("FullIngressClosure.Counters","FullIngressClosure","decrement_zero","decrementZero"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_original","bankOriginal"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_unary","bankUnary"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_other","bankOther"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_grid","bankGrid"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_commute","bankCommute"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_idempotent","bankIdempotent"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_take","bankTake"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_add","bankAdd"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.rise","gridRise"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.cells","gridCells"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique transfer proof term {mod}/{key}: {found.map Prod.fst}"
private inductive Travel (k : Nat) : Nat → Nat → Fin (BodyIngress.machine k).stateCount →
    Fin (BodyIngress.machine k).stateCount → Prop
  | right {a b e out} : RouteR k a b e out → Travel k a b e out
  | left {a b e out} : RouteL k a b e out → Travel k a b e out
  | stay {a e out} : Safe k e → (BodyIngress.machine k).step e none=(out,none,.stay) → Travel k a a e out
private theorem travel {k lo P D T a b e out} (code : Travel k a b e out) (grid : Grid D T)
    (ha : a ≤ 12) (hb : b ≤ 12) (lower : lo ≤ D 0) (upper : D 12 ≤ P) :
    ∃ t,t ≤ 2*(P+16) ∧ PPath k lo P t (pNode e (D a) T) (pNode out (D b) T) := by
  cases code with
  | right code =>
    have ab:=rSpan code
    have path:=routeR (lo:=lo) (hi:=P) code D T ((gridMono grid 0 a (by omega) ha).trans' lower)
      ((gridMono grid b 12 hb le_rfl).trans upper)
      (by intro j _ jhi; exact gridRise grid j (by omega))
      (by intro i j _ ij jhi; exact gridMono grid i j ij (by omega))
      (by intro j _ jhi; exact gridBlank grid j (by omega))
      (by intro j i _ jhi hl hu; exact gridCells grid j i (by omega) hl hu)
    refine ⟨_,?_,path⟩
    have fit: D b ≤ P := (gridMono grid b 12 hb le_rfl).trans upper
    omega
  | left code =>
    have ba:=lSpan code
    have path:=routeL (lo:=lo) (hi:=P) code D T ((gridMono grid 0 b (by omega) hb).trans' lower)
      ((gridMono grid a 12 ha le_rfl).trans upper)
      (by intro j _ jhi; exact gridRise grid j (by omega))
      (by intro i j _ ij jhi; exact gridMono grid i j ij (by omega))
      (by intro j _ jhi; exact gridBlank grid j (by omega))
      (by intro j i _ jhi hl hu; exact gridCells grid j i (by omega) hl hu)
    refine ⟨_,?_,path⟩
    have fit: D a ≤ P := (gridMono grid a 12 ha le_rfl).trans upper
    omega
  | stay safe row =>
    have low:=lower.trans (gridMono grid 0 a (Nat.zero_le a) ha)
    have high:=(gridMono grid a 12 ha le_rfl).trans upper
    have path:=pKeep (k:=k) (lo:=lo) (hi:=P) e out (D a) (D a) T .stay
      ⟨safe.1,safe.2.1⟩ safe.2.2 ⟨low,high⟩ ⟨low,high⟩ (by rw [gridBlank grid a ha]; exact row) rfl
    exact ⟨1,by omega,path⟩
private theorem asUnary {D T j v w} (unary : BankUnary D T j v) (len : D (j+1)=D j+w+1) :
    NatUnary T (D j) w v := by
  intro i hl hu
  rw [unary i hl (by rwa [len])]
  congr 1
  exact decide_eq_decide.mpr (by omega)
private structure TransferCode (k a b : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  take : Fin (BodyIngress.machine k).stateCount
  atInc : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  dec : Decrement k entry take out
  outward : Travel k a b take atInc
  inc : Increment k atInc back
  inward : Travel k b a back entry
private theorem transfer {k lo P D a b entry out} (code : TransferCode k a b entry out)
    (ha : a < 12) (hb : b < 12) (ne : a ≠ b)
    (wa wb : Nat) (lenA : D (a+1)=D a+wa+1) (lenB : D (b+1)=D b+wb+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (v u : Nat) (va : v ≤ wa) (uv : u+v ≤ wb)
    (T : Nat → Option Bool) (grid : Grid D T)
    (source : BankUnary D T a v) (target : BankUnary D T b u) :
    ∃ t,t ≤ 32*(v+1)*(P+16) ∧ PPath k lo P t (pNode entry (D a) T)
      (pNode out (D a) (setBank (setBank T D a 0) D b (u+v))) := by
  induction v generalizing T u with
  | zero =>
    have path:=decrementZero (k:=k) (lo:=lo) (hi:=P) code.dec T (D a) wa
      (lower.trans (gridMono grid 0 a (by omega) (by omega)))
      (by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank grid a (by omega)) (by rw [← lenA]; exact gridBlank grid (a+1) (by omega)) (asUnary source lenA)
    have restored : setBank (setBank T D a 0) D b (u+0)=T := by
      rw [bankOriginal source,Nat.add_zero,bankOriginal target]
    rw [restored]
    exact ⟨3,by nlinarith,path⟩
  | succ v ih =>
    let C:=setBank T D a v
    let E:=setBank C D b (u+1)
    have take:=decrementPositive (k:=k) (lo:=lo) (hi:=P) code.dec T (D a) wa (v+1)
      (lower.trans (gridMono grid 0 a (by omega) (by omega)))
      (by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank grid a (by omega)) (by rw [← lenA]; exact gridBlank grid (a+1) (by omega))
      (asUnary source lenA) (by omega) va
    rw [show D a+(v+1)=D a+v+1 by omega] at take
    rw [bankTake grid ha lenA source (by omega)] at take
    have gridC : Grid D C:=bankGrid grid a v ha
    have cTarget : BankUnary D C b u:=bankOther grid b a u v hb ha ne.symm target
    obtain ⟨outTime,outPrice,outPath⟩:=travel code.outward gridC (by omega) (by omega) lower upper
    have add:=increment (k:=k) (lo:=lo) (hi:=P) code.inc C (D b) wb u
      (lower.trans (gridMono gridC 0 b (by omega) (by omega)))
      (by rw [← lenB]; exact (gridMono gridC (b+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank gridC b (by omega)) (asUnary cTarget lenB) (by omega)
    rw [bankAdd gridC hb lenB cTarget (by omega)] at add
    have gridE : Grid D E:=bankGrid gridC b (u+1) hb
    have eSource : BankUnary D E a v:=bankOther gridC a b v (u+1) ha hb ne (bankUnary T D a v)
    have eTarget : BankUnary D E b (u+1):=bankUnary C D b (u+1)
    obtain ⟨backTime,backPrice,backPath⟩:=travel code.inward gridE (by omega) (by omega) lower upper
    obtain ⟨restTime,restPrice,restPath⟩:=ih (u:=u+1) (by omega) (by omega) E gridE eSource eTarget
    have normalized : setBank (setBank E D a 0) D b (u+1+v)=setBank (setBank T D a 0) D b (u+(v+1)) := by
      have sumEq : u+1+v=u+(v+1) := by omega
      funext i
      dsimp only [E,C,setBank]
      rw [sumEq]
      by_cases ia : D a < i ∧ i < D (a+1)
      · by_cases ib : D b < i ∧ i < D (b+1)
        · simp only [if_pos ia,if_pos ib]
        · simp only [if_pos ia,if_neg ib]
      · by_cases ib : D b < i ∧ i < D (b+1)
        · simp only [if_neg ia,if_pos ib]
        · simp only [if_neg ia,if_neg ib]
    rw [normalized] at restPath
    have path:=pAppend take (pAppend outPath (pAppend add (pAppend backPath restPath)))
    refine ⟨_,?_,path⟩
    have aw: D a+wa+1 ≤ P := by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
    have bw: D b+wb+1 ≤ P := by rw [← lenB]; exact (gridMono grid (b+1) 12 (by omega) le_rfl).trans upper
    nlinarith only [restPrice,outPrice,backPrice,va,uv,aw,bw,Nat.zero_le (D a),Nat.zero_le (D b)]
private def image3 (T : Nat → Option Bool) (D : Nat → Nat) (a b c va vb vc : Nat) : Nat → Option Bool :=
  setBank (setBank (setBank T D a va) D b vb) D c vc
private theorem shadow3 (T : Nat → Option Bool) (D : Nat → Nat) (a b c x y z X Y Z : Nat) :
    image3 (image3 T D a b c x y z) D a b c X Y Z=image3 T D a b c X Y Z := by
  funext i
  dsimp only [image3,setBank]
  by_cases ic : D c < i ∧ i < D (c+1)
  · simp only [if_pos ic]
  · by_cases ib : D b < i ∧ i < D (b+1)
    · simp only [if_neg ic,if_pos ib]
    · by_cases ia : D a < i ∧ i < D (a+1)
      · simp only [if_neg ic,if_neg ib,if_pos ia]
      · simp only [if_neg ic,if_neg ib,if_neg ia]
private structure DuplicateCode (k a b c : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  take : Fin (BodyIngress.machine k).stateCount
  atB : Fin (BodyIngress.machine k).stateCount
  toC : Fin (BodyIngress.machine k).stateCount
  atC : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  dec : Decrement k entry take out
  outward : Travel k a b take atB
  incB : Increment k atB toC
  between : Travel k b c toC atC
  incC : Increment k atC back
  inward : Travel k c a back entry
private theorem duplicate {k lo P D a b c entry out} (code : DuplicateCode k a b c entry out)
    (ha : a < 12) (hb : b < 12) (hc : c < 12) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (wa wb wc : Nat) (lenA : D (a+1)=D a+wa+1) (lenB : D (b+1)=D b+wb+1) (lenC : D (c+1)=D c+wc+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (v u q : Nat) (va : v ≤ wa) (uv : u+v ≤ wb) (qv : q+v ≤ wc)
    (T : Nat → Option Bool) (grid : Grid D T)
    (source : BankUnary D T a v) (target : BankUnary D T b u) (scratch : BankUnary D T c q) :
    ∃ t,t ≤ 64*(v+1)*(P+16) ∧ PPath k lo P t (pNode entry (D a) T)
      (pNode out (D a) (image3 T D a b c 0 (u+v) (q+v))) := by
  induction v generalizing T u q with
  | zero =>
    have path:=decrementZero (k:=k) (lo:=lo) (hi:=P) code.dec T (D a) wa
      (lower.trans (gridMono grid 0 a (by omega) (by omega)))
      (by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank grid a (by omega)) (by rw [← lenA]; exact gridBlank grid (a+1) (by omega)) (asUnary source lenA)
    have restored : image3 T D a b c 0 (u+0) (q+0)=T := by
      dsimp only [image3]
      rw [Nat.add_zero,Nat.add_zero,bankOriginal source,bankOriginal target,bankOriginal scratch]
    rw [restored]
    exact ⟨3,by nlinarith,path⟩
  | succ v ih =>
    let A:=setBank T D a v
    let B:=setBank A D b (u+1)
    let C:=setBank B D c (q+1)
    have take:=decrementPositive (k:=k) (lo:=lo) (hi:=P) code.dec T (D a) wa (v+1)
      (lower.trans (gridMono grid 0 a (by omega) (by omega)))
      (by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank grid a (by omega)) (by rw [← lenA]; exact gridBlank grid (a+1) (by omega))
      (asUnary source lenA) (by omega) va
    rw [show D a+(v+1)=D a+v+1 by omega,bankTake grid ha lenA source (by omega)] at take
    have gridA : Grid D A:=bankGrid grid a v ha
    have aTarget : BankUnary D A b u:=bankOther grid b a u v hb ha ab.symm target
    have aScratch : BankUnary D A c q:=bankOther grid c a q v hc ha ac.symm scratch
    obtain ⟨t1,h1,p1⟩:=travel code.outward gridA (by omega) (by omega) lower upper
    have addB:=increment (k:=k) (lo:=lo) (hi:=P) code.incB A (D b) wb u
      (lower.trans (gridMono gridA 0 b (by omega) (by omega)))
      (by rw [← lenB]; exact (gridMono gridA (b+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank gridA b (by omega)) (asUnary aTarget lenB) (by omega)
    rw [bankAdd gridA hb lenB aTarget (by omega)] at addB
    have gridB : Grid D B:=bankGrid gridA b (u+1) hb
    have bScratch : BankUnary D B c q:=bankOther gridA c b q (u+1) hc hb bc.symm aScratch
    obtain ⟨t2,h2,p2⟩:=travel code.between gridB (by omega) (by omega) lower upper
    have addC:=increment (k:=k) (lo:=lo) (hi:=P) code.incC B (D c) wc q
      (lower.trans (gridMono gridB 0 c (by omega) (by omega)))
      (by rw [← lenC]; exact (gridMono gridB (c+1) 12 (by omega) le_rfl).trans upper)
      (gridBlank gridB c (by omega)) (asUnary bScratch lenC) (by omega)
    rw [bankAdd gridB hc lenC bScratch (by omega)] at addC
    have gridC : Grid D C:=bankGrid gridB c (q+1) hc
    have cSource : BankUnary D C a v:=bankOther gridB a c v (q+1) ha hc ac
      (bankOther gridA a b v (u+1) ha hb ab (bankUnary T D a v))
    have cTarget : BankUnary D C b (u+1):=bankOther gridB b c (u+1) (q+1) hb hc bc (bankUnary A D b (u+1))
    have cScratch : BankUnary D C c (q+1):=bankUnary B D c (q+1)
    obtain ⟨t3,h3,p3⟩:=travel code.inward gridC (by omega) (by omega) lower upper
    obtain ⟨restTime,restPrice,rest⟩:=ih (u:=u+1) (q:=q+1) (by omega) (by omega) (by omega) C gridC cSource cTarget cScratch
    have normalized : image3 C D a b c 0 (u+1+v) (q+1+v)=image3 T D a b c 0 (u+(v+1)) (q+(v+1)) := by
      change image3 (image3 T D a b c v (u+1) (q+1)) D a b c 0 (u+1+v) (q+1+v)=_
      rw [shadow3,show u+1+v=u+(v+1) by omega,show q+1+v=q+(v+1) by omega]
    rw [normalized] at rest
    have path:=pAppend take (pAppend p1 (pAppend addB (pAppend p2 (pAppend addC (pAppend p3 rest)))))
    refine ⟨_,?_,path⟩
    have aw : D a+wa+1 ≤ P := by rw [← lenA]; exact (gridMono grid (a+1) 12 (by omega) le_rfl).trans upper
    have bw : D b+wb+1 ≤ P := by rw [← lenB]; exact (gridMono grid (b+1) 12 (by omega) le_rfl).trans upper
    have cw : D c+wc+1 ≤ P := by rw [← lenC]; exact (gridMono grid (c+1) 12 (by omega) le_rfl).trans upper
    nlinarith only [restPrice,h1,h2,h3,va,uv,qv,aw,bw,cw,Nat.zero_le (D a),Nat.zero_le (D b),Nat.zero_le (D c)]
private structure CopyCode (k a b c : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  drained : Fin (BodyIngress.machine k).stateCount
  restoreEntry : Fin (BodyIngress.machine k).stateCount
  restoreOut : Fin (BodyIngress.machine k).stateCount
  drain : DuplicateCode k a b c entry drained
  toRestore : Travel k a c drained restoreEntry
  restore : TransferCode k c a restoreEntry restoreOut
  fromRestore : Travel k c a restoreOut out
private theorem copy_value {k lo P D a b c entry out} (code : CopyCode k a b c entry out)
    (ha : a < 12) (hb : b < 12) (hc : c < 12) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (wa wb wc : Nat) (lenA : D (a+1)=D a+wa+1) (lenB : D (b+1)=D b+wb+1) (lenC : D (c+1)=D c+wc+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P) (v : Nat) (va : v ≤ wa) (vb : v ≤ wb) (vc : v ≤ wc)
    (T : Nat → Option Bool) (grid : Grid D T)
    (source : BankUnary D T a v) (target : BankUnary D T b 0) (scratch : BankUnary D T c 0) :
    ∃ t,t ≤ 128*(v+1)*(P+16) ∧ PPath k lo P t (pNode entry (D a) T)
      (pNode out (D a) (setBank (setBank T D b v) D c 0)) := by
  let A:=setBank T D a 0
  let B:=setBank A D b v
  let U:=setBank B D c v
  have gridA : Grid D A:=bankGrid grid a 0 ha
  have gridB : Grid D B:=bankGrid gridA b v hb
  have gridU : Grid D U:=bankGrid gridB c v hc
  obtain ⟨t1,h1,drain⟩:=duplicate code.drain ha hb hc ab ac bc wa wb wc lenA lenB lenC lower upper v 0 0 va (by omega) (by omega) T grid source target scratch
  simp only [Nat.zero_add] at drain
  obtain ⟨t2,h2,before⟩:=travel code.toRestore gridU (by omega) (by omega) lower upper
  have cUnary : BankUnary D U c v:=bankUnary B D c v
  have aUnary : BankUnary D U a 0:=bankOther gridB a c 0 v ha hc ac
    (bankOther gridA a b 0 v ha hb ab (bankUnary T D a 0))
  obtain ⟨t3,h3,restore⟩:=transfer code.restore hc ha ac.symm wc wa lenC lenA lower upper v 0 vc (by omega) U gridU cUnary aUnary
  simp only [Nat.zero_add] at restore
  have eq1 : setBank U D c 0=setBank B D c 0:=bankIdempotent B D c v 0
  have eq2 : setBank (setBank B D c 0) D a v=setBank (setBank B D a v) D c 0:=
    bankCommute gridB c a 0 v hc ha ac.symm
  have eq3 : setBank B D a v=setBank (setBank A D a v) D b v:=
    bankCommute gridA b a v v hb ha ab.symm
  have eq4 : setBank A D a v=T := by
    change setBank (setBank T D a 0) D a v=T
    rw [bankIdempotent,bankOriginal source]
  have normalized : setBank (setBank U D c 0) D a v=setBank (setBank T D b v) D c 0 := by
    rw [eq1,eq2,eq3,eq4]
  rw [normalized] at restore
  have gridV:=bankGrid (bankGrid gridU c 0 hc) a v ha
  obtain ⟨t4,h4,after⟩:=travel code.fromRestore gridV (by omega) (by omega) lower upper
  rw [normalized] at after
  have path:=pAppend drain (pAppend before (pAppend restore after))
  refine ⟨_,?_,path⟩
  nlinarith only [h1,h2,h3,h4,Nat.zero_le v]

end FullIngressClosure
