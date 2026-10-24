import CarryWindow.Geometry
namespace CarryWindow
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let requests:=[("CarryWindow.Geometry","CarryWindow","C","C"),
    ("CarryWindow.Geometry","CarryWindow","D","D"),
    ("CarryWindow.Geometry","CarryWindow","A","A"),
    ("CarryWindow.Geometry","CarryWindow","Banks","Banks"),
    ("CarryWindow.Geometry","CarryWindow","value","value"),
    ("CarryWindow.Geometry","CarryWindow","atD","atD"),
    ("CarryWindow.Geometry","CarryWindow","atBank","atBank"),
    ("CarryWindow.Geometry","CarryWindow","occupied","occupied"),
    ("CarryWindow.Geometry","CarryWindow","set0","set0"),
    ("CarryWindow.Geometry","CarryWindow","take0","take0"),
    ("CarryWindow.Geometry","CarryWindow","take3","take3"),
    ("CarryWindow.Geometry","CarryWindow","clear0","clear0"),
    ("CarryWindow.Geometry","CarryWindow","hop","hop"),
    ("CarryWindow.Geometry","CarryWindow","keep","keep"),
    ("CarryWindow.Geometry","CarryWindow","put","put"),
    ("CarryWindow.Geometry","CarryWindow","dest","dest"),
    ("VirtualLeaf.Body","VirtualLeaf","Trace","Tr"),
    ("VirtualLeaf.Body","VirtualLeaf","Trace.run","trRun"),
    ("VirtualLeaf.Body","VirtualLeaf","Trace.bound","trBound"),
    ("VirtualLeaf.Body","VirtualLeaf","nil","trNil"),
    ("VirtualLeaf.Body","VirtualLeaf","single","trSingle"),
    ("VirtualLeaf.Body","VirtualLeaf","append","trAppend"),
    ("VirtualLeaf.Body","VirtualLeaf","sweepL","trSweepL"),
    ("VirtualLeaf.Body","VirtualLeaf","sweepR","trSweepR"),
    ("CarryWindow.Rows","CarryWindow","native_row","native_row"),
    ("CarryWindow.Machine","CarryWindow","native","native") ]
  for (mod,ns,key,localName) in requests do
    let names:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    unless names.length=1 do throwError "Ambiguous checked proof term {localName}: {names}"
    logInfo m!"private-term|{names.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) names.head! :: st.openDecls}
private theorem R {M : UniformTM} {N B lo hi : Nat} (fit : hi < tapeLength N B)
    (s d : Fin M.stateCount) (low width h' : Nat) (T : Nat → Option Bool) (mv : Move)
    (hb : lo ≤ low+1 ∧ low+width+1 ≤ hi) (ha : lo ≤ h' ∧ h' ≤ hi)
    (cells : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (scan : ∀ b, M.step s (some b)=(s,some b,.right))
    (last : M.step s (T (low+width+1))=(d,T (low+width+1),mv))
    (move : dest (low+width+1) mv=h') :
    Tr (N:=N) (B:=B) M lo hi (width+1)
      (C s (low+1) T (by omega)) (C d h' T (by omega)) := by
  have a:=trSweepR (M:=M) (N:=N) (B:=B) (lo:=lo) (hi:=hi) s (fun i => T i.val)
    (low+1) width fit hb.1 (by omega) (by
      intro i l h; obtain ⟨v,hv⟩:=cells i.val (by omega) (by omega)
      change M.step s (T i.val)=(s,T i.val,.right)
      rw [hv]; exact scan v)
  have b:=keep fit s d (low+1+width) h' T mv ⟨by omega,by omega⟩ ha
    (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using last)
    (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using move)
  exact trAppend a b
private theorem J {M : UniformTM} {N B lo hi : Nat} (fit : hi < tapeLength N B)
    (s d : Fin M.stateCount) (low width h' : Nat) (T : Nat → Option Bool) (mv : Move)
    (hb : lo ≤ low ∧ low+width ≤ hi) (ha : lo ≤ h' ∧ h' ≤ hi)
    (cells : ∀ i, low < i → i ≤ low+width → ∃ b, T i=some b)
    (scan : ∀ b, M.step s (some b)=(s,some b,.left))
    (last : M.step s (T low)=(d,T low,mv)) (move : dest low mv=h') :
    Tr (N:=N) (B:=B) M lo hi (width+1)
      (C s (low+width) T (by omega)) (C d h' T (by omega)) := by
  have a:=trSweepL (M:=M) (N:=N) (B:=B) (lo:=lo) (hi:=hi) s (fun i => T i.val)
    low width fit hb.1 hb.2 (by
      intro i l h; obtain ⟨v,hv⟩:=cells i.val l h
      change M.step s (T i.val)=(s,T i.val,.left)
      rw [hv]; exact scan v)
  have b:=keep fit s d low h' T mv ⟨hb.1,by omega⟩ ha last move
  exact trAppend a b
private theorem right3 {k N B T F r n} (fr : Banks T F r n) (W a v : Nat)
    (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (2*r+n+3)
      (C (extra k 2) (D F r n 0+1) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 5) (D F r n 3) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=R (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 2) (extra k 3) (D F r n 0) r (D F r n 1+1) (A T F r n W a v) .right
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i l h; exact occupied fr W a v 0 i (by decide) l (by dsimp only [D] at h ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [show D F r n 0+r+1=D F r n 1 by dsimp only [D]; omega,atD fr W a v 1 (by decide),native_row]; rfl)
    (by dsimp only [dest,D]; omega)
  have p1:=R (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 3) (extra k 4) (D F r n 1) n (D F r n 2+1) (A T F r n W a v) .right
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i l h; exact occupied fr W a v 1 i (by decide) l (by dsimp only [D] at h ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [show D F r n 1+n+1=D F r n 2 by dsimp only [D]; omega,atD fr W a v 2 (by decide),native_row]; rfl)
    (by dsimp only [dest,D]; omega)
  have p2:=R (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 4) (extra k 5) (D F r n 2) r (D F r n 3) (A T F r n W a v) .stay
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i l h; exact occupied fr W a v 2 i (by decide) l (by dsimp only [D] at h ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [show D F r n 2+r+1=D F r n 3 by dsimp only [D]; omega,atD fr W a v 3 (by decide),native_row]; rfl)
    (by dsimp only [dest,D]; omega)
  simpa only [show r+1+(n+1)+(r+1)=2*r+n+3 by omega] using trAppend (trAppend p0 p1) p2
private theorem left3 {k N B T F r n} (fr : Banks T F r n) (W a v : Nat)
    (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (2*r+n+3)
      (C (extra k 9) (D F r n 2+r) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 12) (D F r n 0+1) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 9) (extra k 10) (D F r n 2) r (D F r n 1+n) (A T F r n W a v) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i l h; exact occupied fr W a v 2 i (by decide) l (by dsimp only [D] at h ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W a v 2 (by decide),native_row]; rfl)
    (by dsimp only [dest,D]; omega)
  have p1:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 10) (extra k 11) (D F r n 1) n (D F r n 0+r) (A T F r n W a v) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i l h; exact occupied fr W a v 1 i (by decide) l (by dsimp only [D] at h ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W a v 1 (by decide),native_row]; rfl)
    (by dsimp only [dest,D]; omega)
  have p2:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 11) (extra k 12) (D F r n 0) r (D F r n 0+1) (A T F r n W a v) .right
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i l h; exact occupied fr W a v 0 i (by decide) l (by dsimp only [D] at h ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W a v 0 (by decide),native_row]; rfl)
    rfl
  simpa only [show r+1+(n+1)+(r+1)=2*r+n+3 by omega] using trAppend (trAppend p0 p1) p2
private theorem six (k : Nat) (b : Option Bool) (hb : b ≠ some true) :
    (machine k).step (extra k 6) b=(extra k 7,b,.left) := by
  rw [native_row]
  cases b with
  | none => rfl
  | some v => cases v with | false => rfl | true => exact False.elim (hb rfl)
private theorem tail3 {T F r n} (fr : Banks T F r n) (W a v : Nat) (vr : v ≤ r) :
    A T F r n W a v (D F r n 3+1+v) ≠ some true := by
  by_cases full : v=r
  · rw [show D F r n 3+1+v=D F r n 4 by dsimp only [D]; omega,atD fr W a v 4 (by decide)]
    decide
  · rw [atBank T F r n W a v 3 _ (by decide) (by decide)
      (by dsimp only [D]; omega) (by dsimp only [D]; omega)]
    simp only [value,show (3:Nat) ≠ 0 by decide,ite_false,ite_true,
      decide_eq_false (by omega : ¬D F r n 3+1+v ≤ D F r n 3+v)]
    decide
private theorem enter3 {k N B T F r n} (fr : Banks T F r n) (W a v : Nat)
    (vr : v ≤ r) (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (v+2)
      (C (extra k 5) (D F r n 3) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 7) (D F r n 3+v) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=keep (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 5) (extra k 6) (D F r n 3) (D F r n 3+1) (A T F r n W a v) .right
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by rw [atD fr W a v 3 (by decide),native_row]; rfl) rfl
  have p1:=trSweepR (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) (hi:=D F r n 6)
    (extra k 6) (fun i => A T F r n W a v i.val) (D F r n 3+1) v fit
    (by dsimp only [D]; omega) (by dsimp only [D]; omega) (by
      intro i lo hi
      change (machine k).step (extra k 6) (A T F r n W a v i.val)=(extra k 6,A T F r n W a v i.val,.right)
      have cell : A T F r n W a v i.val=some true := by
        rw [atBank T F r n W a v 3 _ (by decide) (by decide)
          (by dsimp only [D] at lo ⊢; omega) (by dsimp only [D] at hi ⊢; omega)]
        change some (decide (i.val ≤ D F r n 3+v))=some true
        rw [decide_eq_true (by omega : i.val ≤ D F r n 3+v)]
      rw [cell,native_row]; rfl)
  have p2:=keep (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 6) (extra k 7) (D F r n 3+1+v) (D F r n 3+v) (A T F r n W a v) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (six k _ (tail3 fr W a v vr)) (by dsimp only [dest,D]; omega)
  simpa only [show 1+v+1=v+2 by omega] using trAppend (trAppend p0 p1) p2
private theorem inc0 {k N B T F r n} (fr : Banks T F r n) (W a v : Nat)
    (ar : a < r) (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (2*a+2)
      (C (extra k 12) (D F r n 0+1) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 2) (D F r n 0+1) (A T F r n W (a+1) v) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=trSweepR (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) (hi:=D F r n 6)
    (extra k 12) (fun i => A T F r n W a v i.val) (D F r n 0+1) a fit
    (by omega) (by dsimp only [D]; omega) (by
      intro i lo hi
      change (machine k).step (extra k 12) (A T F r n W a v i.val)=(extra k 12,A T F r n W a v i.val,.right)
      have cell : A T F r n W a v i.val=some true := by
        rw [atBank T F r n W a v 0 _ (by decide) (by decide)
          (by dsimp only [D] at lo ⊢; omega) (by dsimp only [D] at hi ⊢; omega)]
        change some (decide (i.val ≤ D F r n 0+a))=some true
        rw [decide_eq_true (by omega : i.val ≤ D F r n 0+a)]
      rw [cell,native_row]; rfl)
  have cell : A T F r n W a v (D F r n 0+1+a)=some false := by
    rw [atBank T F r n W a v 0 _ (by decide) (by decide)
      (by dsimp only [D]; omega) (by dsimp only [D]; omega)]
    change some (decide (D F r n 0+1+a ≤ D F r n 0+a))=some false
    rw [decide_eq_false (by omega : ¬D F r n 0+1+a ≤ D F r n 0+a)]
  have p1:=hop (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 12) (extra k 13) (D F r n 0+1+a) (D F r n 0+a) (A T F r n W a v) (some true) .left
    ⟨by omega,by dsimp only [D]; omega⟩ ⟨by omega,by dsimp only [D]; omega⟩
    (by rw [cell,native_row]; rfl) (by dsimp only [dest,D]; omega)
  have tapeEq : put (A T F r n W a v) (D F r n 0+1+a) (some true)=A T F r n W (a+1) v := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using set0 T F r n W a v ar
  rw [tapeEq] at p1
  have p2:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 13) (extra k 2) (D F r n 0) a (D F r n 0+1) (A T F r n W (a+1) v) .right
    ⟨le_rfl,by dsimp only [D]; omega⟩ ⟨by omega,by dsimp only [D]; omega⟩
    (by intro i lo hi; exact occupied fr W (a+1) v 0 i (by decide) lo (by dsimp only [D] at hi ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W (a+1) v 0 (by decide),native_row]; rfl) rfl
  simpa only [show a+1+(a+1)=2*a+2 by omega] using trAppend (trAppend p0 p1) p2
private theorem round {k N B T F r n} (fr : Banks T F r n) (W a v : Nat)
    (cap : a+(v+1) ≤ r) (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (2*(v+1)+2*a+4*r+2*n+11)
      (C (extra k 5) (D F r n 3) (A T F r n W a (v+1)) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 5) (D F r n 3) (A T F r n W (a+1) v) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=enter3 (k:=k) fr W a (v+1) (by omega) fit
  have cell : A T F r n W a (v+1) (D F r n 3+(v+1))=some true := by
    rw [atBank T F r n W a (v+1) 3 _ (by decide) (by decide)
      (by dsimp only [D]; omega) (by dsimp only [D]; omega)]
    change some (decide (D F r n 3+(v+1) ≤ D F r n 3+(v+1)))=some true
    rw [decide_eq_true le_rfl]
  have p1:=hop (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 7) (extra k 8) (D F r n 3+(v+1)) (D F r n 3+v) (A T F r n W a (v+1)) (some false) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩ ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by rw [cell,native_row]; rfl) (by dsimp only [D,dest]; omega)
  have tapeEq : put (A T F r n W a (v+1)) (D F r n 3+(v+1)) (some false)=A T F r n W a v := by
    simpa only [Nat.add_assoc] using take3 T F r n W a v (by omega)
  rw [tapeEq] at p1
  have p2:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 8) (extra k 9) (D F r n 3) v (D F r n 2+r) (A T F r n W a v) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩ ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i lo hi; exact occupied fr W a v 3 i (by decide) lo (by dsimp only [D] at hi ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W a v 3 (by decide),native_row]; rfl) (by dsimp only [D,dest]; omega)
  have p3:=left3 (k:=k) fr W a v fit
  have p4:=inc0 (k:=k) fr W a v (by omega) fit
  have p5:=right3 (k:=k) fr W (a+1) v fit
  convert trAppend (trAppend (trAppend (trAppend (trAppend p0 p1) p2) p3) p4) p5 using 1
  all_goals omega
private theorem zeroEnd {k N B T F r n} (fr : Banks T F r n) (W a : Nat)
    (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (r+4)
      (C (extra k 5) (D F r n 3) (A T F r n W a 0) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 23) (D F r n 2) (A T F r n W a 0) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=enter3 (k:=k) fr W a 0 (by omega) fit
  simp only [Nat.add_zero] at p0
  have p1:=keep (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 7) (extra k 22) (D F r n 3) (D F r n 2+r) (A T F r n W a 0) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩ ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by rw [atD fr W a 0 3 (by decide),native_row]; rfl) (by dsimp only [D,dest]; omega)
  have p2:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 22) (extra k 23) (D F r n 2) r (D F r n 2) (A T F r n W a 0) .stay
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩ ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i lo hi; exact occupied fr W a 0 2 i (by decide) lo (by dsimp only [D] at hi ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W a 0 2 (by decide),native_row]; rfl) rfl
  convert trAppend (trAppend p0 p1) p2 using 1
  all_goals omega
private theorem loop {k N B T F r n} (fr : Banks T F r n) (W v a : Nat)
    (cap : a+v ≤ r) (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6)
      (v*(2*(a+v)+4*r+2*n+11)+r+4)
      (C (extra k 5) (D F r n 3) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 23) (D F r n 2) (A T F r n W (a+v) 0) (by dsimp only [D] at fit ⊢; omega)) := by
  induction v generalizing a with
  | zero => simpa using zeroEnd (k:=k) fr W a fit
  | succ v ih =>
    have one:=round (k:=k) fr W a v cap fit
    have rest:=ih (a+1) (by omega)
    have eq : a+1+v=a+(v+1) := by omega
    simp only [eq] at rest
    have price : (2*(v+1)+2*a+4*r+2*n+11)+(v*(2*(a+(v+1))+4*r+2*n+11)+r+4)=
      (v+1)*(2*(a+(v+1))+4*r+2*n+11)+r+4 := by ring
    simpa only [price] using trAppend one rest
private theorem setup {k N B T F r n} (fr : Banks T F r n) (W g : Nat)
    (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) (3*r+2*n+6)
      (C (embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))))
        (D F r n 2) (A T F r n W r g) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 5) (D F r n 3) (A T F r n W 0 g) (by dsimp only [D] at fit ⊢; omega)) := by
  let start:=embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))
  have p0:=keep (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit start
    (extra k 0) (D F r n 2) (D F r n 1+n) (A T F r n W r g) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩ ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by rw [atD fr W r g 2 (by decide)]; dsimp only [start]; rw [table_delta,if_pos ⟨rfl,rfl⟩])
    (by dsimp only [D,dest]; omega)
  have p1:=J (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 0) (extra k 1) (D F r n 1) n (D F r n 0+r) (A T F r n W r g) .left
    ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩ ⟨by dsimp only [D]; omega,by dsimp only [D]; omega⟩
    (by intro i lo hi; exact occupied fr W r g 1 i (by decide) lo (by dsimp only [D] at hi ⊢; omega))
    (by intro b; rw [native_row]; cases b <;> rfl)
    (by rw [atD fr W r g 1 (by decide),native_row]; rfl) (by dsimp only [D,dest]; omega)
  have p2:=clear0 (k:=k) T W g fit r le_rfl
  have p3:=keep (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit
    (extra k 1) (extra k 2) (D F r n 0) (D F r n 0+1) (A T F r n W 0 g) .right
    ⟨le_rfl,by dsimp only [D]; omega⟩ ⟨by omega,by dsimp only [D]; omega⟩
    (by rw [atD fr W 0 g 0 (by decide),native_row]; rfl) rfl
  have p4:=right3 (k:=k) fr W 0 g fit
  convert trAppend (trAppend (trAppend (trAppend p0 p1) p2) p3) p4 using 1
  all_goals (dsimp only [start,D] at *; omega)
private theorem carry {k N B T F r n} (fr : Banks T F r n) (W g : Nat)
    (gr : g ≤ r) (fit : D F r n 6 < tapeLength N B) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6)
      (g*(2*g+4*r+2*n+11)+4*r+2*n+10)
      (C (embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))))
        (D F r n 2) (A T F r n W r g) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 23) (D F r n 2) (A T F r n W g 0) (by dsimp only [D] at fit ⊢; omega)) := by
  have p0:=setup (k:=k) fr W g fit
  have p1:=loop (k:=k) fr W g 0 (by omega) fit
  simp only [Nat.zero_add] at p1
  convert trAppend p0 p1 using 1
  all_goals omega
run_cmd do
  for key in ["after"] ++ (List.range 26).map (fun j => "after"++toString j) do
    let names:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith (".Cursor."++key)
    unless names.length=1 do throwError "Ambiguous immutable Cursor chunk {key}: {names}"
    logInfo m!"private-term|{names.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous ("cursor_"++key)) names.head! :: st.openDecls}
private def shiftCode (k c : Nat) := if c/9=40 then c else c+837*k
private theorem affine0 (k : Nat) : cursor_after0 k 0=(cursor_after0 0 0).map (shiftCode k) := by rfl
private theorem affine1 (k : Nat) : cursor_after1 k 0=(cursor_after1 0 0).map (shiftCode k) := by rfl
private theorem affine2 (k : Nat) : cursor_after2 k 0=(cursor_after2 0 0).map (shiftCode k) := by rfl
private theorem affine3 (k : Nat) : cursor_after3 k 0=(cursor_after3 0 0).map (shiftCode k) := by rfl
private theorem affine4 (k : Nat) : cursor_after4 k 0=(cursor_after4 0 0).map (shiftCode k) := by rfl
private theorem affine5 (k : Nat) : cursor_after5 k 0=(cursor_after5 0 0).map (shiftCode k) := by rfl
private theorem affine6 (k : Nat) : cursor_after6 k 0=(cursor_after6 0 0).map (shiftCode k) := by rfl
private theorem affine7 (k : Nat) : cursor_after7 k 0=(cursor_after7 0 0).map (shiftCode k) := by rfl
private theorem affine8 (k : Nat) : cursor_after8 k 0=(cursor_after8 0 0).map (shiftCode k) := by rfl
private theorem affine9 (k : Nat) : cursor_after9 k 0=(cursor_after9 0 0).map (shiftCode k) := by rfl
private theorem affine10 (k : Nat) : cursor_after10 k 0=(cursor_after10 0 0).map (shiftCode k) := by rfl
private theorem affine11 (k : Nat) : cursor_after11 k 0=(cursor_after11 0 0).map (shiftCode k) := by rfl
private theorem affine12 (k : Nat) : cursor_after12 k 0=(cursor_after12 0 0).map (shiftCode k) := by rfl
private theorem affine13 (k : Nat) : cursor_after13 k 0=(cursor_after13 0 0).map (shiftCode k) := by rfl
private theorem affine14 (k : Nat) : cursor_after14 k 0=(cursor_after14 0 0).map (shiftCode k) := by rfl
private theorem affine15 (k : Nat) : cursor_after15 k 0=(cursor_after15 0 0).map (shiftCode k) := by rfl
private theorem affine16 (k : Nat) : cursor_after16 k 0=(cursor_after16 0 0).map (shiftCode k) := by rfl
private theorem affine17 (k : Nat) : cursor_after17 k 0=(cursor_after17 0 0).map (shiftCode k) := by rfl
private theorem affine18 (k : Nat) : cursor_after18 k 0=(cursor_after18 0 0).map (shiftCode k) := by rfl
private theorem affine19 (k : Nat) : cursor_after19 k 0=(cursor_after19 0 0).map (shiftCode k) := by rfl
private theorem affine20 (k : Nat) : cursor_after20 k 0=(cursor_after20 0 0).map (shiftCode k) := by rfl
private theorem affine21 (k : Nat) : cursor_after21 k 0=(cursor_after21 0 0).map (shiftCode k) := by rfl
private theorem affine22 (k : Nat) : cursor_after22 k 0=(cursor_after22 0 0).map (shiftCode k) := by rfl
private theorem affine23 (k : Nat) : cursor_after23 k 0=(cursor_after23 0 0).map (shiftCode k) := by rfl
private theorem affine24 (k : Nat) : cursor_after24 k 0=(cursor_after24 0 0).map (shiftCode k) := by rfl
private theorem affine25 (k : Nat) : cursor_after25 k 0=(cursor_after25 0 0).map (shiftCode k) := by rfl
private theorem affineAfter (k : Nat) : cursor_after k 0=(cursor_after 0 0).map (shiftCode k) := by
  dsimp only [cursor_after]
  rw [affine0 k, affine1 k, affine2 k, affine3 k, affine4 k, affine5 k, affine6 k, affine7 k, affine8 k, affine9 k, affine10 k, affine11 k, affine12 k, affine13 k, affine14 k, affine15 k, affine16 k, affine17 k, affine18 k, affine19 k, affine20 k, affine21 k, affine22 k, affine23 k, affine24 k, affine25 k]
  simp only [List.map_append]
private def checkCodes (p : Nat → Nat → Bool) : Nat → List Nat → Bool
  | _,[] => true
  | j,c::cs => p j c && checkCodes p (j+1) cs
private theorem check_get (p : Nat → Nat → Bool) (xs : List Nat) (j : Nat)
    (ok : checkCodes p j xs=true) (i c : Nat) (got : xs[i]?=some c) : p (j+i) c=true := by
  induction xs generalizing j i with
  | nil => simp only [List.getElem?_nil] at got; contradiction
  | cons x xs ih =>
    have parts : p j x=true ∧ checkCodes p (j+1) xs=true := by
      simpa only [checkCodes,Bool.and_eq_true] using ok
    cases i with
    | zero => simp only [List.getElem?_cons_zero] at got; cases got; simpa only [Nat.add_zero] using parts.1
    | succ i =>
      have h:=ih (j+1) parts.2 i (by simpa only [List.getElem?_cons_succ] using got)
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
private def deadBase (i : Nat) : Bool :=
  decide ((471 ≤ i ∧ i ≤ 478) ∨ (509 ≤ i ∧ i ≤ 512) ∨ (541 ≤ i ∧ i ≤ 544) ∨ (553 ≤ i ∧ i < 937 ∧ i ≠ 613))
private theorem codeBound : checkCodes (fun _ c => decide (c/9 < 937)) 0 (cursor_after 0 0)=true := by decide
private theorem deadCertificate : checkCodes (fun j c => !deadBase (330+j/3) || (c/9==40 || deadBase (c/9)))
    0 (cursor_after 0 0)=true := by decide
run_cmd do
  for (n,ci) in (← getEnv).constants.toList do
    if (n.toString.splitOn "accepted_full").length > 1 then
      logInfo m!"old-accepted-full-term|{n}|{ci.type}"
private def tag : Option Bool → Nat | none => 0 | some false => 1 | some true => 2
private def code0 (i : Nat) (b : Option Bool) := ((cursor_after 0 0)[3*(i-330)+tag b]?).getD 0
private theorem tag_lt (b : Option Bool) : tag b < 3 := by cases b with | none => decide | some v => cases v <;> decide
private theorem got0 (i : Nat) (b : Option Bool) (lo : 330 ≤ i) (hi : i < 937) :
    (cursor_after 0 0)[3*(i-330)+tag b]?=some (code0 i b) := by
  have len : (cursor_after 0 0).length=1821 := by rfl
  have small:=tag_lt b
  have bound : 3*(i-330)+tag b < (cursor_after 0 0).length := by rw [len]; omega
  have found:=List.getElem?_eq_getElem bound
  unfold code0
  rw [found]
  rfl
private theorem shift_dest (k c : Nat) : shiftCode k c/9=if c/9=40 then 40 else c/9+93*k := by
  unfold shiftCode
  split_ifs <;> omega
private theorem shift_symbol (k c : Nat) : shiftCode k c/3%3=c/3%3 := by
  unfold shiftCode
  split_ifs <;> omega
private theorem shift_move (k c : Nat) : shiftCode k c%3=c%3 := by
  unfold shiftCode
  split_ifs <;> omega
private def action (k c : Nat) : Fin (Cursor.stateCount k) × Option Bool × Move :=
  (Cursor.q k (c/9),(if c/3%3=0 then none else some (decide (c/3%3=2))),
    if c%3=0 then .left else if c%3=1 then .stay else .right)
private theorem actual_row (k i : Nat) (b : Option Bool) (lo : 330 ≤ i) (hi : i < 937) :
    (Cursor.machine k).step (Cursor.q k (i+93*k)) b=action k (shiftCode k (code0 i b)) := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "program_split" => have split:=OLD k
  fromDonor "VirtualReady.Kernel" "VirtualReady" "pref_len" => have len:=OLD k
  fromDonor "VirtualReady.Kernel" "VirtualReady" "decode_actual" =>
    apply OLD k (i+93*k) (shiftCode k (code0 i b)) b (by omega) (by unfold Cursor.stateCount; omega)
    rw [split,List.getElem?_toArray,List.getElem?_append,if_neg (by rw [len]; have small:=tag_lt b; change ¬3*(i+93*k-64)+tag b < _; omega)]
    rw [len]
    change (cursor_after k 0)[3*(i+93*k-64)+tag b-(798+279*k)]?=some (shiftCode k (code0 i b))
    rw [show 3*(i+93*k-64)+tag b-(798+279*k)=3*(i-330)+tag b by omega,
      affineAfter k,List.getElem?_map,got0 i b lo hi]
    rfl
private theorem base_bound (i : Nat) (b : Option Bool) (lo : 330 ≤ i) (hi : i < 937) : code0 i b/9 < 937 := by
  have h:=check_get (fun _ c => decide (c/9 < 937)) _ 0 codeBound _ _ (got0 i b lo hi)
  exact of_decide_eq_true h
private theorem base_dead (i : Nat) (b : Option Bool) (lo : 330 ≤ i) (hi : i < 937)
    (dead : deadBase i=true) : code0 i b/9=40 ∨ deadBase (code0 i b/9)=true := by
  have h:=check_get (fun j c => !deadBase (330+j/3) || (c/9==40 || deadBase (c/9)))
    _ 0 deadCertificate _ _ (got0 i b lo hi)
  have small:=tag_lt b
  have idx : 330+(0+(3*(i-330)+tag b))/3=i := by omega
  simpa only [idx,dead,Bool.not_true,Bool.false_or,Bool.or_eq_true,beq_iff_eq] using h
end CarryWindow
