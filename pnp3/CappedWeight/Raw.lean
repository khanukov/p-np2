import CappedWeight.Kernel
import CappedWeight.RawTarget
namespace CappedWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private theorem clock (R n r t d : Nat) (hn : n ≤ R) (hr : r ≤ R)
    (ht : t ≤ 67108864*(R+1)^4)
    (hd : d ≤ 1024*(n+r+1)^2*(3*R+2+5*r+n+9)) : t+d ≤ 268435456*(R+1)^4 := by
  have c1 : n+r+1 ≤ 2*(R+1) := by omega
  have c2 : 3*R+2+5*r+n+9 ≤ 12*(R+1) := by omega
  have mul:=Nat.mul_le_mul (Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left c1 2)) c2
  nlinarith only [ht,hd,mul,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3),Nat.zero_le (R^4)]
private theorem overflow (k n z S r : Nat) (hk : 0<k) (hr : r<n)
    (physical : min (9+2*z+2^n) S<S) (rem : r=S-min (9+2*z+2^n) S) : S<Cursor.Target.M k n z := by
  have base : 9+2*z+2^n<S := by omega
  rw [Nat.min_eq_left (Nat.le_of_lt base)] at rem
  obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
  have np : 0<n := by omega
  have pp : 1≤n^j := Nat.pow_pos np
  have ge : n≤n^(j+1) := by rw [Nat.pow_succ]; nlinarith
  have total : S=9+2*z+2^n+r := by omega
  have mul:=Nat.mul_le_mul_left (bitLength n+4) (show n≤n^(j+1)+(j+1) by omega)
  dsimp only [Cursor.Target.M,Cursor.Target.W]
  nlinarith only [total,hr,mul,ge,Nat.zero_le (bitLength n),Nat.zero_le (n*bitLength n)]
private theorem right_run {k N B : Nat} (t : Nat) (c : Config (Cursor.machine k).stateCount N B) :
    (AllArityCursor.machine k).run t (SmallIngress.producer.seqEmbedRight (Cursor.machine k) c)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run t c) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).run t _=_
  rw [UniformTM.seq_run_right]
private theorem idem (T : Nat → Option Bool) (L n F r a b c d e : Nat) :
    Target.image (Target.image T L n F r a b c d e) L n F r a b c d e=Target.image T L n F r a b c d e := by
  funext i; dsimp only [Target.image]; split_ifs <;> rfl
private theorem full_old (X : Nat → Option Bool) (L n F r i : Nat)
    (a : i ≤ L ∨ L+n+1 ≤ i) (b : i ≤ F+r+2 ∨ F+r+n+3 ≤ i)
    (c : i ≤ F+r+n+3 ∨ F+2*r+n+4 ≤ i) : RuntimeBitLength.Target.fullImage X L n F r i=X i := by
  dsimp only [RuntimeBitLength.Target.fullImage]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by have h:=Nat.min_le_right (bitLength n) r; omega)]
private theorem prepared_seed (k N B L n Q F r : Nat) (V : Nat → Option Bool) (hk : 0 < k) (hr : 0 < r)
    (fits : bitLength n ≤ r) (paid : 0 < Q) (room : L+n+1+Q < F)
    (sep : V L=none) (right : V (L+n+1)=none)
    (marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → V i=some true)
    (gap : ∀ i, L+n+1+Q < i → i < F → V i=none) (fence : V F=some false)
    (fresh : ∀ i, F < i → i ≤ F+5*r+n+7 → V i=none) :
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Z:=AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage X L n F r) F r n
    Target.FirstProduct k N B L n F r Z := by
  dsimp only
  let C:=SuffixCap.Target.image V F r
  let X:=CappedWorkspace.Target.image C L n F r
  let Z:=AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage X L n F r) F r n
  have geo : L+n+1 < F := by omega
  have oldC (i : Nat) (hi : i ≤ F+1) : C i=V i := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_neg (by omega)]
  have cf : C F=some false := (oldC _ (by omega)).trans fence
  have cd0 : C (F+1)=none := (oldC _ le_rfl).trans (fresh _ (by omega) (by omega))
  have cb0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : C i=some true := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_pos (by omega)]
  have blank (i : Nat) (lo : F+r+2 ≤ i) (hi : i ≤ F+5*r+n+7) : C i=none := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_neg (by omega)]; exact fresh i (by omega) hi
  obtain ⟨xa,xf,xb0,xzero,xd,xold⟩:=AllArityWorkspace.six_bank_image C L n F r geo cf cd0 cb0 blank
  have zold (i : Nat) (a : i ≤ L ∨ L+n+1 ≤ i) (b : i ≤ F+r+2 ∨ F+r+n+3 ≤ i)
      (c : i ≤ F+r+n+3 ∨ F+2*r+n+4 ≤ i) (d : i≠F+2*r+n+5) : Z i=X i := by
    dsimp only [Z,AllArityBitLength.Target.seedImage]; rw [if_neg d]; exact full_old X L n F r i a b c
  have za (i : Nat) (lo : L < i) (hi : i < L+n+1) : Z i=some false := by
    dsimp only [Z,AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage]
    rw [if_neg (by omega),if_pos ⟨lo,hi⟩]
    simp only [not_lt_of_ge fits,false_and,decide_false]
  have z1 (i : Nat) (lo : F+r+2 < i) (hi : i < F+r+n+3) : Z i=some false := by
    dsimp only [Z,AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage]
    rw [if_neg (by omega),if_neg (by omega),if_pos ⟨lo,hi⟩]
    simp only [not_lt_of_ge fits,false_and,decide_false]
  have z2 (i : Nat) (lo : F+r+n+3 < i) (hi : i < F+2*r+n+4) : Z i=some (decide (i ≤ F+r+n+3+bitLength n)) := by
    dsimp only [Z,AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),Nat.min_eq_left fits]
    by_cases mark : i ≤ F+r+n+3+bitLength n
    · rw [if_pos ⟨lo,mark⟩,decide_eq_true mark]
    · rw [if_neg (by omega),decide_eq_false mark]; exact xzero i (by omega)
  have z3 (i : Nat) (lo : F+2*r+n+4 < i) (hi : i < F+3*r+n+5) : Z i=some (decide (i ≤ F+2*r+n+4+1)) := by
    by_cases mark : i=F+2*r+n+5
    · dsimp only [Z,AllArityBitLength.Target.seedImage]; rw [if_pos mark,decide_eq_true (by omega)]
    · rw [zold i (by omega) (by omega) (by omega) mark,decide_eq_false (by omega)]; exact xzero i (by omega)
  have z45 (i : Nat) (h : (F+3*r+n+5 < i ∧ i < F+4*r+n+6) ∨ (F+4*r+n+6 < i ∧ i < F+5*r+n+7)) : Z i=some false := by
    rw [zold i (by omega) (by omega) (by omega) (by omega)]; exact xzero i (by omega)
  have exterior (i : Nat) (hi : i ≤ L ∨ (L+n+1 ≤ i ∧ i ≤ F+1)) : Z i=V i := by
    exact (zold i (by omega) (by omega) (by omega) (by omega)).trans ((xold i (by omega)).trans (oldC i (by omega)))
  apply first_product k N B L n Q F r Z hk hr paid room
    ((exterior L (Or.inl le_rfl)).trans sep)
    ((exterior (L+n+1) (Or.inr ⟨le_rfl,by omega⟩)).trans right)
    (by intro i lo hi; exact (exterior i (Or.inr ⟨by omega,by omega⟩)).trans (marks i lo hi))
    (by intro i lo hi; exact (exterior i (Or.inr ⟨by omega,by omega⟩)).trans (gap i lo hi))
    ((exterior F (Or.inr ⟨by omega,by omega⟩)).trans fence)
  · intro i h; rw [zold i (by omega) (by omega) (by omega) (by omega)]; exact xd i h
  · intro i lo hi; rw [zold i (by omega) (by omega) (by omega) (by omega)]; exact xb0 i lo hi
  · exact z1
  · funext i; dsimp only [Target.image]; split_ifs with a b c d e
    · rw [za i a.1 a.2,decide_eq_false (by omega)]
    · exact (z2 i b.1 b.2).symm
    · exact (z3 i c.1 c.2).symm
    · rw [z45 i (Or.inl d),decide_eq_false (by omega)]
    · rw [z45 i (Or.inr e),decide_eq_false (by omega)]
    · rfl
/-- Accepted same-pr producer288 input, then the executed first power product.
The raw time is the predecessor's actual q329 witness plus the literal phase time. -/
theorem accepted_first_product (k : Nat) (hk : 0 < k) : Target.RawProduct k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,z,hH,gamma,eof,physical⟩:=AllArityBitLength.accepted_seed k x w accepted
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have pair : S ≤ R := by dsimp only [S,R,pairLength]; omega
  have width : n ≤ S := by have lt:=Nat.lt_two_pow_self (n:=n); change 2^n ≤ S at table; omega
  refine ⟨pr,parsed,table,z,hH,gamma,eof,?_⟩
  intro phys
  change p < S at phys
  obtain ⟨t,h,price,Pfit,reached,first,over⟩:=physical phys
  refine ⟨t,h,price,Pfit,reached,first,over,?_⟩
  intro fits fit
  have rp : 0 < r := by dsimp only [r]; omega
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" =>
    obtain ⟨cf,short,fresh⟩:=OLD x w gamma cap rows
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.arena" => have arena:=OLD cf
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.sep" => have sep:=OLD cf
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.right" => have right:=OLD cf
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.marks" => have marks:=OLD cf
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.gap" => have gap:=OLD cf
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.fence" => have fence:=OLD cf
  change S+z+n+3+2^n < F at arena
  change V L=none at sep
  change V (S+z+n+3)=none at right
  change ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+2^n → V i=some true at marks
  change ∀ i, S+z+n+3+2^n < i → i < F → V i=none at gap
  change V F=some false at fence
  change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
  have H : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  have prep : Target.FirstProduct k R B L n F r Z := prepared_seed k R B L n (2^n) F r V hk rp fits
    (by positivity) (by omega) sep (by rw [H]; exact right)
    (by intro i lo hi; exact marks i (by omega) (by omega))
    (by intro i lo hi; exact gap i (by omega) hi) fence
    (by intro i lo hi; exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
  obtain ⟨d,phasePrice,done,before⟩:=prep fit
  have headD3 : F+2*r+n+4 < tapeLength R B :=
    lt_of_le_of_lt (by omega : F+2*r+n+4 ≤ F+5*r+n+7) fit
  have reached' : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 329,⟨F+2*r+n+4,headD3⟩,fun i => Z i.val⟩ := by
    simpa only [if_pos fits] using reached
  refine ⟨d,phasePrice,?_,?_,?_,?_⟩
  · rw [UniformTM.run_add,reached',right_run,done]
  · apply clock R n r t d (width.trans pair) ((Nat.sub_le S p).trans pair) price
    simpa only [FixedRawLengthFence.fencePos] using phasePrice
  · intro u hu
    have bd:=before u hu
    rw [UniformTM.run_add,reached',right_run]
    change 288+_ < 699
    exact Nat.add_lt_add_left bd 288
  · intro shortage; exact overflow k n z S r hk shortage phys rfl
end CappedWeight
