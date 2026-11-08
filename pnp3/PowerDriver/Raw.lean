import PowerDriver.Kernel
import PowerDriver.Seed
namespace PowerDriver
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private abbrev Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop := by
  fromDonor "PowerDriver.Kernel" "PowerDriver" "Frame" => exact OLD T L n Q F r
private theorem right_run {k N B : Nat} (t : Nat) (c : Config (Cursor.machine k).stateCount N B) :
    (AllArityCursor.machine k).run t (SmallIngress.producer.seqEmbedRight (Cursor.machine k) c)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run t c) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).run t _=_
  rw [UniformTM.seq_run_right]
private theorem clock (R n r k t d : Nat) (hn : n ≤ R) (hr : r ≤ R)
    (ht : t ≤ 67108864*(R+1)^4)
    (hd : d ≤ 1024*(k+1)*(n+r+1)^2*(3*R+2+5*r+n+9)) : t+d ≤ 1073741824*(k+1)*(R+1)^4 := by
  have c1 : n+r+1 ≤ 2*(R+1) := by omega
  have c2 : 3*R+2+5*r+n+9 ≤ 12*(R+1) := by omega
  have mul:=Nat.mul_le_mul (Nat.mul_le_mul_left (1024*(k+1)) (Nat.pow_le_pow_left c1 2)) c2
  have slack:=Nat.mul_le_mul_left (67108864*(R+1)^4) (show 1 ≤ k+1 by omega)
  nlinarith only [ht,hd,mul,slack,Nat.zero_le R,Nat.zero_le k,Nat.zero_le (R^2),Nat.zero_le (R^3),Nat.zero_le (R^4),Nat.zero_le (k*R^2),Nat.zero_le (k*R^3),Nat.zero_le (k*R^4)]
private theorem overflow (k n z S r j a e : Nat) (hj : j<k) (ha : a<n^j) (he : e<n) (cap : r=a*n+e)
    (physical : min (9+2*z+2^n) S<S) (rem : r=S-min (9+2*z+2^n) S) : S<Cursor.Target.M k n z := by
  have np : 0<n := by omega
  have pp : 1 ≤ n^(k-(j+1)) := Nat.pow_pos np
  have ge : n^(j+1) ≤ n^k := by
    rw [show k=j+1+(k-(j+1)) by omega,Nat.pow_add n (j+1) (k-(j+1))]
    nlinarith only [pp,Nat.zero_le (n^(j+1))]
  have small : r<n^(j+1) := by rw [Nat.pow_succ]; nlinarith only [ha,he,cap,Nat.zero_le n]
  have base : 9+2*z+2^n<S := by omega
  rw [Nat.min_eq_left (Nat.le_of_lt base)] at rem
  have total : S=9+2*z+2^n+r := by omega
  have mul:=Nat.mul_le_mul_left (bitLength n+4) (show n^k ≤ n^k+k by omega)
  dsimp only [Cursor.Target.M,Cursor.Target.W]
  nlinarith only [total,small,ge,mul,Nat.zero_le (bitLength n),Nat.zero_le ((bitLength n)*n^k)]
private theorem full_old (X : Nat → Option Bool) (L n F r i : Nat)
    (a : i ≤ L ∨ L+n+1 ≤ i) (b : i ≤ F+r+2 ∨ F+r+n+3 ≤ i)
    (c : i ≤ F+r+n+3 ∨ F+2*r+n+4 ≤ i) : RuntimeBitLength.Target.fullImage X L n F r i=X i := by
  dsimp only [RuntimeBitLength.Target.fullImage]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by have h:=Nat.min_le_right (bitLength n) r; omega)]
private theorem prepared_seed (L n Q F r : Nat) (V : Nat → Option Bool) (hr : 0 < r)
    (fits : bitLength n ≤ r) (paid : 0 < Q) (room : L+n+1+Q < F)
    (sep : V L=none) (right : V (L+n+1)=none)
    (marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → V i=some true)
    (gap : ∀ i, L+n+1+Q < i → i < F → V i=none) (fence : V F=some false)
    (fresh : ∀ i, F < i → i ≤ F+5*r+n+7 → V i=none) :
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Z:=AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage X L n F r) F r n
    Frame Z L n Q F r := by
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
  fromDonor "PowerDriver.Kernel" "PowerDriver" "makeFrame" =>
    apply OLD L n Q F r Z paid room
      ((exterior L (Or.inl le_rfl)).trans sep)
      ((exterior (L+n+1) (Or.inr ⟨le_rfl,by omega⟩)).trans right)
      (by intro i lo hi; exact (exterior i (Or.inr ⟨by omega,by omega⟩)).trans (marks i lo hi))
      (by intro i lo hi; exact (exterior i (Or.inr ⟨by omega,by omega⟩)).trans (gap i lo hi))
      ((exterior F (Or.inr ⟨by omega,by omega⟩)).trans fence)
  · intro i h; rw [zold i (by omega) (by omega) (by omega) (by omega)]; exact xd i h
  · intro i lo hi; rw [zold i (by omega) (by omega) (by omega) (by omega)]; exact xb0 i lo hi
  · exact z1
  · funext i; dsimp only [CappedWeight.Target.image]; split_ifs with a b c d e
    · rw [za i a.1 a.2,decide_eq_false (by omega)]
    · exact (z2 i b.1 b.2).symm
    · exact (z3 i c.1 c.2).symm
    · rw [z45 i (Or.inl d),decide_eq_false (by omega)]
    · rw [z45 i (Or.inr e),decide_eq_false (by omega)]
    · rfl
theorem accepted_power (k : Nat) : Target.RawPower k := by
  intro a m x w accepted
  fromDonor "PowerDriver.Seed" "PowerDriver" "seed_ceiling" =>
    obtain ⟨pr,parsed,table,z,hH,gamma,eof,physical⟩:=OLD k x w accepted
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
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro virtual
    obtain ⟨t,price,logical,_false,done⟩:=eof virtual
    exact ⟨t,clock R n r k t 0 (width.trans pair) ((Nat.sub_le S p).trans pair) price (by positivity),logical,done⟩
  · intro phys
    change p<S at phys
    obtain ⟨t,h,price,fit,reached,prior,over⟩:=physical phys
    have rp : 0<r := by dsimp only [r]; omega
    by_cases fits : bitLength pr.2.n ≤ a+m-min (9+2*z+2^pr.2.n) (a+m)
    · have cap:=AcceptedBody.strict_capacity x w gamma width
      have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" => obtain ⟨cf,short,fresh⟩:=OLD x w gamma cap rows
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
      have fr : Frame Z L n (2^n) F r := prepared_seed L n (2^n) F r V rp fits
        (by positivity) (by omega) sep (by rw [H]; exact right)
        (by intro i lo hi; exact marks i (by omega) (by omega))
        (by intro i lo hi; exact gap i (by omega) hi) fence
        (by intro i lo hi; exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
      fromDonor "PowerDriver.Kernel" "PowerDriver" "driver" => obtain ⟨d,phase,branch⟩:=OLD (k:=k) Z fr rp
      have headD3 : F+2*r+n+4 < tapeLength R B := lt_of_le_of_lt (by omega : F+2*r+n+4 ≤ F+5*r+n+7) fit
      have seed : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 329,⟨F+2*r+n+4,headD3⟩,fun i => Z i.val⟩ := by simpa only [if_pos fits] using reached
      refine ⟨fit,t+d,clock R n r k t d (width.trans pair) ((Nat.sub_le S p).trans pair) price (by simpa only [FixedRawLengthFence.fencePos] using phase),Or.inr ⟨fits,?_⟩⟩
      rcases branch with ⟨ok,path⟩|⟨j,a0,e,hj,ha,he,eq,path⟩
      all_goals
        fromDonor "PowerDriver.Kernel" "PowerDriver" "Path.execute" => have ex:=OLD path fit
        fromDonor "PowerDriver.Kernel" "PowerDriver" "Path.first" => have fs:=OLD path fit
      · refine Or.inl ⟨ok,?_,?_⟩
        · rw [UniformTM.run_add,seed,right_run]; exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) ex
        · intro u hu
          by_cases early : u<t
          · exact (prior u early).trans_le (by omega)
          · rw [show u=t+(u-t) by omega,UniformTM.run_add,seed,right_run]
            change 288+_ < 288+329+82*k
            exact (Nat.add_lt_add_left (fs (u-t) (by omega)) 288).trans_le (by omega)
      · refine Or.inr ⟨j,a0,e,hj,ha,he,eq,overflow k n z S r j a0 e hj ha he eq phys rfl,?_,?_⟩
        · rw [UniformTM.run_add,seed,right_run]; exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) ex
        · intro u hu
          by_cases early : u<t
          · exact (prior u early).trans_le (by omega)
          · rw [show u=t+(u-t) by omega,UniformTM.run_add,seed,right_run]
            change 288+_ < 288+329+82*k
            exact (Nat.add_lt_add_left (fs (u-t) (by omega)) 288).trans_le (by omega)
    · refine ⟨fit,t,clock R n r k t 0 (width.trans pair) ((Nat.sub_le S p).trans pair) price (by positivity),Or.inl ⟨by omega,over (by omega),?_⟩⟩
      simpa only [if_neg fits] using reached
end PowerDriver
