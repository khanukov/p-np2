import VirtualReady.Kernel
namespace VirtualReady
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def paint (T : Nat → Option Bool) (lo hi : Nat) : Nat → Option Bool :=
  fun i => if lo ≤ i ∧ i < hi then some false else T i
private def stage (T : Nat → Option Bool) (F r n : Nat) : Nat → Nat → Option Bool
  | 0 => T
  | j+1 => paint (stage T F r n j) (D F r n j+1) (D F r n (j+1))
private abbrev Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Frame" => exact OLD T L n Q F r
private theorem Dmono (F r n a b : Nat) (ha : a ≤ b) (hb : b ≤ 6) : D F r n a ≤ D F r n b := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Dmono" => exact OLD F r n a b ha hb
private theorem paint_old (T : Nat → Option Bool) (lo hi i : Nat) (h : i < lo ∨ hi ≤ i) : paint T lo hi i=T i := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "paint_old" => exact OLD T lo hi i h
private theorem cleanup_run (k N B L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : F+5*r+n+7 < tapeLength N B) (hd : F+r+n+3 < tapeLength N B) (hh : L+n+1 < tapeLength N B) :
    (Cursor.machine k).run (F-(L+n+1)+19*r+7*n+48)
      ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,hd⟩,fun i => T i.val⟩=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨L+n+1,hh⟩,fun i => paint (stage T F r n 6) (L+1) (L+n+1) i.val⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "cleanup_run" => exact OLD k N B L n Q F r T fr fit hd hh
private structure Base (V : Nat → Option Bool) (S z n F : Nat) : Prop where
  arena : S+z+n+3+2^n < F
  sep : V (S+z+2)=none
  right : V (S+z+n+3)=none
  marks : ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+2^n → V i=some true
  gap : ∀ i, S+z+n+3+2^n < i → i < F → V i=none
  fence : V F=some false
private theorem actual_base {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (PairEncoding.pairLength a m)-(a+m+z+n+3)-1) :
    let R := PairEncoding.pairLength a m
    let B := FixedRawLengthFence.allocation R
    let S := a+m
    let F := FixedRawLengthFence.fencePos R
    let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
    let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    Base V S z n F ∧ ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none := by
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" =>
    obtain ⟨fr,_fit,fresh⟩ := OLD x w gamma cap rows
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.arena" => have arena := OLD fr
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.sep" => have sep := OLD fr
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.right" => have right := OLD fr
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.marks" => have marks := OLD fr
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.gap" => have gap := OLD fr
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.fence" => have fence := OLD fr
  exact ⟨⟨arena,sep,right,marks,gap,fence⟩,fresh⟩
private def computed (V : Nat → Option Bool) (L n F r : Nat) :=
  RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
private theorem computed_old (V : Nat → Option Bool) (L n F r i : Nat)
    (_room : L+n+1 < F) (before : i ≤ F) (outside : i ≤ L ∨ L+n+1 ≤ i) : computed V L n F r i=V i := by
  simp only [computed,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by have b:=Nat.min_le_right (bitLength n) r; omega),
    if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem computed_frame (V : Nat → Option Bool) (S z n F r : Nat) (fr : Base V S z n F)
    (fresh : ∀ i, F < i → i ≤ D F r n 6 → V i=none) :
    Frame (computed V (S+z+2) n F r) (S+z+2) n (2^n) F r := by
  let L := S+z+2
  have hv : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  have arena : L+n+1+2^n < F := by rw [hv]; exact fr.arena
  have room : L+n+1 < F := (Nat.le_add_right _ _).trans_lt arena
  have old := computed_old V L n F r
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Frame.mk" =>
    refine OLD (by positivity) arena ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    change computed V L n F r (D F r n j)=none
    have bound := Nat.min_le_right (bitLength n) r
    have ext : computed V L n F r (D F r n j)=V (D F r n j) := by
      interval_cases j <;> simp only [computed,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image,D]
      all_goals repeat' first | rfl | (exfalso; omega) | split
    rw [ext]
    exact fresh _ (by have h:=Dmono F r n 0 j (by omega) hj; change F+1 ≤ D F r n j at h; omega) (Dmono F r n j 6 hj le_rfl)
  · intro j hj i lo hi
    change D F r n j < i at lo
    change i < D F r n (j+1) at hi
    interval_cases j <;> simp only [D] at lo hi
    all_goals simp only [computed,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    all_goals repeat' first | (exact ⟨_,rfl⟩) | (exfalso; omega) | split
  · rw [old F room le_rfl (Or.inr (by omega))]; exact fr.fence
  · intro i lo hi
    have src : L+n+1+2^n < i := lo
    rw [old i room (Nat.le_of_lt hi) (Or.inr ((Nat.le_add_right _ _).trans (Nat.le_of_lt src)))]
    exact fr.gap i (by rw [← hv]; exact src) hi
  · intro i lo hi
    have lower : L+n+1 < i := lo
    have upper : i ≤ L+n+1+2^n := hi
    rw [old i room (upper.trans (Nat.le_of_lt arena)) (Or.inr (Nat.le_of_lt lower))]
    exact fr.marks i (by rw [← hv]; exact lower) (by rw [← hv]; exact upper)
  · rw [old L room (by omega) (Or.inl le_rfl)]; exact fr.sep
  · rw [old (L+n+1) room (by omega) (Or.inr le_rfl)]
    rw [show L+n+1=S+z+n+3 by dsimp only [L]; omega]
    exact fr.right
  · intro i lo hi
    simp only [computed,RuntimeBitLength.Target.fullImage]
    rw [if_pos ⟨lo,hi⟩]; exact ⟨_,rfl⟩
private abbrev bank (F r n i : Nat) : Prop :=
  F+1 < i ∧ i < F+r+2 ∨ F+r+2 < i ∧ i < F+r+n+3 ∨
  F+r+n+3 < i ∧ i < F+2*r+n+4 ∨ F+2*r+n+4 < i ∧ i < F+3*r+n+5 ∨
  F+3*r+n+5 < i ∧ i < F+4*r+n+6 ∨ F+4*r+n+6 < i ∧ i < F+5*r+n+7
private theorem stage_exact (T : Nat → Option Bool) (F r n i : Nat) :
    stage T F r n 6 i = if bank F r n i then some false else T i := by
  simp only [stage,D,paint,bank]
  split_ifs <;> first | rfl | omega
private theorem cleared_image (V : Nat → Option Bool) (L n F r : Nat) (room : L+n+1 < F)
    (assn : ∀ i, L < i → i < L+n+1 → V i=some false) :
    paint (stage (computed V L n F r) F r n 6) (L+1) (L+n+1)=Cursor.Target.scratch V F r n := by
  funext i
  by_cases assignment : L < i ∧ i < L+n+1
  · rw [paint,if_pos (by omega)]
    simp only [Cursor.Target.scratch]
    rw [if_neg (by omega),assn i assignment.1 assignment.2]
  · rw [paint_old _ _ _ _ (by omega),stage_exact]
    change (if bank F r n i then some false else computed V L n F r i)=
      if bank F r n i then some false else V i
    by_cases h : bank F r n i
    · rw [if_pos h,if_pos h]
    · rw [if_neg h,if_neg h]
      dsimp only [bank] at h
      simp only [computed,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
      have bound := Nat.min_le_right (bitLength n) r
      rw [if_neg assignment,if_neg (by omega),if_neg (by omega),
        if_neg assignment,if_neg (by omega),if_neg (by omega)]
open Pnp4.Frontier Pnp4.AlgorithmsToLowerBounds PairEncoding
private theorem phase_price (R n r F H t : Nat) (hn : n ≤ R) (hr : r ≤ R) (hf : F=3*R+2)
    (ht : t ≤ 67108864*(R+1)^4) : t+(F-H+19*r+7*n+48) ≤ 134217728*(R+1)^4 := by
  have d : F-H+19*r+7*n+48 ≤ 64*(R+1) := by omega
  have bound : R+1 ≤ (R+1)^4 := by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3),Nat.zero_le (R^4)]
  have times := Nat.mul_le_mul_left 64 bound
  omega
private theorem widen (R t : Nat) (ht : t ≤ 67108864*(R+1)^4) : t ≤ 134217728*(R+1)^4 :=
  ht.trans (Nat.mul_le_mul_right _ (by decide))
private theorem no_verdict (k : Nat) {N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) (t : Nat)
    (atEnd : ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 329) ∨
      ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) :
    ∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
      ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject := by
  have controls := AllArityCursor.control_values k
  have va : (IngressRepair.machine k).accept.val=327 := controls.2.2.1
  have vr : (IngressRepair.machine k).reject.val=328 := controls.2.2.2
  have seed : (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 329)).val=617 := by
    change 288+329%Cursor.stateCount k=617
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
  have ready : (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)).val=1224+93*k := by
    change 288+((64+265+82*k+1+11*k+604+2)%Cursor.stateCount k)=1224+93*k
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
    omega
  apply (IngressRepair.machine k).no_terminal_of_le c
  · intro h
    rcases atEnd with done | done
    · have eq:=congrArg Fin.val (done.symm.trans h); rw [seed,va] at eq; omega
    · have eq:=congrArg Fin.val (done.symm.trans h); rw [ready,va] at eq; omega
  · intro h
    rcases atEnd with done | done
    · have eq:=congrArg Fin.val (done.symm.trans h); rw [seed,vr] at eq; omega
    · have eq:=congrArg Fin.val (done.symm.trans h); rw [ready,vr] at eq; omega
/-- Actual repaired raw origin, all accepted arities, same dependent parse and
allocation: seed is preserved; bitLength overflow now EXECUTES to virtual MReady. -/
theorem accepted_virtual (k : Nat) : Target.AcceptedVirtual k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,z,hH,gamma,eof,physical⟩ := AllArityBitLength.accepted_seed k x w accepted
  let R := pairLength a m; let B := FixedRawLengthFence.allocation R; let S := a+m
  let n := pr.2.n; let L := S+z+2; let F := FixedRawLengthFence.fencePos R
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let p := min (9+2*z+2^n) S; let r := S-p
  let Y := computed V L n F r
  let c := initialConfig (IngressRepair.machine k) B (encodePair x w)
  have same := IngressRepair.accepted_transport k x w accepted
  have sr : S ≤ R := by dsimp only [S,R,pairLength]; omega
  have width : n ≤ S := by have small:=Nat.lt_two_pow_self (n:=n); change 2^n ≤ S at table; omega
  have Hval : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  refine ⟨pr,parsed,table,z,hH,gamma,?_,?_⟩
  · intro doneEOF
    obtain ⟨t,price,logical,falseRead,oldRun⟩ := eof doneEOF
    have run : (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩ := by rw [same]; exact oldRun
    exact ⟨t,widen R t price,logical,falseRead,run,no_verdict k c t (Or.inr (congrArg Config.state run))⟩
  · intro phys
    change p < S at phys
    obtain ⟨t,h,price,fit,oldRun,first329,overflow⟩ := physical phys
    change F+5*r+n+7 < tapeLength R B at fit
    change r < bitLength n → S < Cursor.Target.M k n z at overflow
    have head3 : F+2*r+n+4 < tapeLength R B := by clear * - fit; omega
    have head2 : F+r+n+3 < tapeLength R B := by clear * - fit; omega
    change (AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) B (encodePair x w))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
         ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,h⟩,
         fun i => (if bitLength n ≤ r then AllArityBitLength.Target.seedImage Y F r n else Y) i.val⟩ at oldRun
    refine ⟨fit,?_,?_⟩
    · intro fits
      change bitLength n ≤ r at fits
      have run : (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 329,⟨F+2*r+n+4,head3⟩,
            fun i => AllArityBitLength.Target.seedImage Y F r n i.val⟩ := by
        rw [same]
        simpa only [if_pos fits] using oldRun
      refine ⟨t,_,widen R t price,run,?_,no_verdict k c t (Or.inl (congrArg Config.state run))⟩
      intro u hu
      change ((IngressRepair.machine k).run u c).state≠_
      rw [same]
      exact first329 u hu
    · intro over
      change r < bitLength n at over
      have nofit : ¬bitLength n ≤ r := by omega
      have start : (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,head2⟩,fun i => Y i.val⟩ := by
        rw [same]
        simpa only [if_neg nofit] using oldRun
      obtain ⟨base,fresh⟩ := actual_base x w gamma (AcceptedBody.strict_capacity x w gamma width)
        (Stream.accepted_rows_fit k x w accepted parsed gamma)
      change Base V S z n F at base
      change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
      have frame : Frame Y L n (2^n) F r := computed_frame V S z n F r base (by
        intro i lo hi
        exact fresh ⟨i,by change i ≤ F+5*r+n+7 at hi; omega⟩ lo)
      have body := cleanup_run k R B L n (2^n) F r Y frame fit (by omega) (by rw [Hval]; exact hH)
      have originalFalse (i : Nat) (lo : L < i) (hi : i < L+n+1) : V i=some false := by
        dsimp only [V,Stream.Target.image]
        rw [if_pos ⟨lo,hi⟩,CappedWorkspace.overflow_bits]
        simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
        split_ifs <;> rfl
      have room : L+n+1 < F := by
        have bound : L+n+1+2^n < F := by rw [Hval]; exact base.arena
        exact (Nat.le_add_right _ _).trans_lt bound
      have image : paint (stage Y F r n 6) (L+1) (L+n+1)=Cursor.Target.image V k S n z F := by
        rw [cleared_image V L n F r room originalFalse]
        funext i
        simp only [Cursor.Target.image]
        rw [if_pos phys,if_neg (by have hM:=overflow over; change ¬(i=Cursor.Target.M k n z ∧ i < S); omega)]
      have run : (IngressRepair.machine k).run (t+(F-(L+n+1)+19*r+7*n+48)) c=
          IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => Cursor.Target.image V k S n z F i.val⟩ := by
        rw [UniformTM.run_add,start]
        change (IngressRepair.producer.seq (Cursor.machine k)).run _ _=_
        rw [UniformTM.seq_run_right,body,image]
        apply congrArg (IngressRepair.producer.seqEmbedRight (Cursor.machine k))
        refine Config.ext_parts rfl (Fin.ext Hval) rfl
      refine ⟨_,phase_price R n r F (L+n+1) t (width.trans sr) ((Nat.sub_le S p).trans sr) rfl price,overflow over,?_,run,
        no_verdict k c _ (Or.inr (congrArg Config.state run))⟩
      have beyond : ¬Cursor.Target.M k n z < a+m := by have hm:=overflow over; change a+m < Cursor.Target.M k n z at hm; omega
      change padRead (Fin.append x w) (Cursor.Target.M k n z)=false
      unfold padRead
      rw [dif_neg beyond]
end VirtualReady
