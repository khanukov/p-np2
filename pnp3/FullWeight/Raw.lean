import FullWeight.Loops
namespace FullWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private abbrev Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop := by
  fromDonor "FullWeight.Kernel" "FullWeight" "Frame" => exact OLD T L n Q F r
private theorem right_run {k N B : Nat} (t : Nat) (c : Config (Cursor.machine k).stateCount N B) :
    (AllArityCursor.machine k).run t (SmallIngress.producer.seqEmbedRight (Cursor.machine k) c)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run t c) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).run t _=_
  rw [UniformTM.seq_run_right]
private theorem clock (R n r k t d v : Nat) (hn : n  ≤  R) (hr : r  ≤  R)
    (ht : t  ≤  67108864*(R+1)^4)
    (hd : d  ≤  1024*(k+1)*(n+r+1)^2*(3*R+2+5*r+n+9))
    (hv : v  ≤  1048576*(k+1)*(r+1)^2*(3*R+2+5*r+n+9)) : t+d+v  ≤  268435456*(k+1)*(R+1)^4 := by
  have c1 : n+r+1  ≤  2*(R+1) := by omega
  have c2 : 3*R+2+5*r+n+9  ≤  12*(R+1) := by omega
  have p:=Nat.mul_le_mul (Nat.mul_le_mul_left (1024*(k+1)) (Nat.pow_le_pow_left c1 2)) c2
  have w:=Nat.mul_le_mul (Nat.mul_le_mul_left (1048576*(k+1)) (Nat.pow_le_pow_left (show r+1  ≤  R+1 by omega) 2)) c2
  have pp : d  ≤  49152*(k+1)*(R+1)^3 := by nlinarith only [hd,p]
  have ww : v  ≤  12582912*(k+1)*(R+1)^3 := by nlinarith only [hv,w]
  have inc : (R+1)^3  ≤  (R+1)^4 := by
    calc (R+1)^3  ≤  (R+1)^3*(R+1) := Nat.le_mul_of_pos_right _ (by omega)
         _ = (R+1)^4 := by ring
  have lift:=Nat.mul_le_mul_left (12632064*(k+1)) inc
  have seed:=Nat.mul_le_mul_left (67108864*(R+1)^4) (show 1  ≤  k+1 by omega)
  nlinarith only [ht,pp,ww,lift,seed,Nat.zero_le ((k+1)*(R+1)^4)]
private theorem cap_weight (k n r v2 v3 v4 v5 d : Nat) (cap : CappedWeight.Target.Cap k n r v2 v3 v4 v5 d) : r < Cursor.Target.W k n := by
  have positive : 0 < n^k+k := by
    by_cases zero : k=0
    · subst k;change 0 < 1;omega
    · omega
  dsimp only [Cursor.Target.W]
  rcases cap with ⟨j,a,e,hj,ha,he,eq,_⟩|⟨j,hj,eq,_⟩|⟨j,hj,eq,_⟩|⟨a,e,ha,he,eq,_⟩
  · have np : 0 < n := by omega
    have pp : 1  ≤  n^(k-(j+1)) := Nat.pow_pos np
    have ge : n^(j+1)  ≤  n^k := by
      rw [show k=j+1+(k-(j+1)) by omega,Nat.pow_add n (j+1) (k-(j+1))]
      nlinarith only [pp,Nat.zero_le (n^(j+1))]
    have small : r < n^(j+1) := by rw [Nat.pow_succ];nlinarith only [ha,he,eq,Nat.zero_le n]
    nlinarith only [small,ge,Nat.zero_le k,Nat.zero_le (bitLength n),Nat.zero_le ((bitLength n)*(n^k+k))]
  · nlinarith only [hj,eq,Nat.zero_le (bitLength n),Nat.zero_le ((bitLength n)*(n^k+k)),Nat.zero_le (n^k)]
  · nlinarith only [hj,eq,positive,Nat.zero_le (bitLength n)]
  · nlinarith only [ha,he,eq,Nat.zero_le (n^k+k)]
private theorem address (k n z S r : Nat) (small : r < Cursor.Target.W k n)
    (phys : min (9+2*z+2^n) S < S) (rem : r=S-min (9+2*z+2^n) S) : S < Cursor.Target.M k n z := by
  have base : 9+2*z+2^n < S := by omega
  rw [Nat.min_eq_left (Nat.le_of_lt base)] at rem
  dsimp only [Cursor.Target.M]
  omega
private theorem exclude (k i : Nat) (s : Fin (AllArityCursor.machine k).stateCount)
    (hi : i  ≤  798+93*k) (hs : s.val < 288+i) : s ≠ SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k i) := by
  have eq : (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k i)).val=288+i := by
    change 288+i%Cursor.stateCount k=288+i
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
  intro h
  rw [h,eq] at hs
  omega
theorem accepted_full (k : Nat) : CappedWeight.Target.FullRaw k := by
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
  have pair : S  ≤  R := by dsimp only [S,R,pairLength]; omega
  have width : n  ≤  S := by have lt:=Nat.lt_two_pow_self (n:=n); change 2^n  ≤  S at table; omega
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro virtual
    obtain ⟨t,price,logical,_false,done⟩:=eof virtual
    exact ⟨t,clock R n r k t 0 0 (width.trans pair) ((Nat.sub_le S p).trans pair) price (by positivity) (by positivity),logical,done⟩
  · intro phys
    change p < S at phys
    obtain ⟨t,h,price,fit,reached,prior,over⟩:=physical phys
    have rp : 0 < r := by dsimp only [r]; omega
    by_cases fits : bitLength pr.2.n  ≤  a+m-min (9+2*z+2^pr.2.n) (a+m)
    · have cap:=AcceptedBody.strict_capacity x w gamma width
      have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" => obtain ⟨cf,short,fresh⟩:=OLD x w gamma cap rows
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.arena" => have arena:=OLD cf
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.sep" => have sep:=OLD cf
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.right" => have right:=OLD cf
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.marks" => have marks:=OLD cf
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.gap" => have gap:=OLD cf
      fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.fence" => have fence:=OLD cf
      change S+z+n+3+2^n  <  F at arena
      change V L=none at sep
      change V (S+z+n+3)=none at right
      change ∀ i, S+z+n+3  <  i → i  ≤  S+z+n+3+2^n → V i=some true at marks
      change ∀ i, S+z+n+3+2^n  <  i → i  <  F → V i=none at gap
      change V F=some false at fence
      change ∀ i : Fin (tapeLength R B), F  <  i.val → V i.val=none at fresh
      have H : L+n+1=S+z+n+3 := by dsimp only [L]; omega
      have fr : Frame Z L n (2^n) F r := by
        fromDonor "PowerDriver.Raw" "PowerDriver" "prepared_seed" =>
          exact OLD L n (2^n) F r V rp fits
            (by positivity) (by omega) sep (by rw [H]; exact right)
            (by intro i lo hi; exact marks i (by omega) (by omega))
            (by intro i lo hi; exact gap i (by omega) hi) fence
            (by intro i lo hi; exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
      fromDonor "PowerDriver.Kernel" "PowerDriver" "driver" => obtain ⟨d,phase,branch⟩:=OLD (k:=k) Z fr rp
      have headD3 : F+2*r+n+4  <  tapeLength R B := lt_of_le_of_lt (by omega : F+2*r+n+4  ≤  F+5*r+n+7) fit
      have seed : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 329,⟨F+2*r+n+4,headD3⟩,fun i => Z i.val⟩ := by simpa only [if_pos fits] using reached
      rcases branch with ⟨ok,path⟩|⟨j,a0,e,hj,ha,he,eq,path⟩
      all_goals
        fromDonor "PowerDriver.Kernel" "PowerDriver" "Path.execute" => have ex:=OLD path fit
        fromDonor "PowerDriver.Kernel" "PowerDriver" "Path.first" => have fs:=OLD path fit
        have before : ∀ u, u < t+d → ((AllArityCursor.machine k).run u c).state.val < 288+329+82*k := by
          intro u hu
          by_cases early : u < t
          · exact (prior u early).trans_le (by omega)
          · rw [show u=t+(u-t) by omega,UniformTM.run_add,seed,right_run]
            change 288+_  <  288+329+82*k
            exact (Nat.add_lt_add_left (fs (u-t) (by omega)) 288).trans_le (by omega)
      · have powerRun : (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (329+82*k),⟨F+2*r+n+4,headD3⟩,fun i => CappedWeight.Target.image Z L n F r (bitLength n) (n^k) 0 0 0 i.val⟩ := by
          rw [UniformTM.run_add,seed,right_run]
          exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) ex
        fromDonor "FullWeight.Loops" "FullWeight" "tail" => obtain ⟨v,pv,tailBranch⟩:=OLD (k:=k) Z fr (bitLength n) (n^k) fits ok
        have total : t+d+v  ≤  268435456*(k+1)*(R+1)^4 := clock R n r k t d v (width.trans pair)
          ((Nat.sub_le S p).trans pair) price
          (by simpa only [FixedRawLengthFence.fencePos] using phase)
          (by simpa only [FixedRawLengthFence.fencePos] using pv)
        refine ⟨fit,t+d+v,total,Or.inr ⟨fits,?_⟩⟩
        rcases tailBranch with ⟨final,tailPath⟩|⟨v2,v3,v4,v5,caps,tailPath⟩
        all_goals
          fromDonor "FullWeight.Kernel" "FullWeight" "Path.execute" => have tailEx:=OLD tailPath fit
          fromDonor "FullWeight.Kernel" "FullWeight" "Path.first" => have tailFirst:=OLD tailPath fit
          have priorTail : ∀ u, u < t+d+v → ((AllArityCursor.machine k).run u c).state.val < 288+430+93*k := by
            intro u hu
            by_cases early : u < t+d
            · exact (before u early).trans_le (by omega)
            · rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,powerRun,right_run]
              change 288+_  <  288+430+93*k
              exact (Nat.add_lt_add_left (tailFirst (u-(t+d)) (by omega)) 288).trans_le (by omega)
        · refine Or.inl ⟨final,?_,?_⟩
          · rw [UniformTM.run_add,powerRun,right_run]
            exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) tailEx
          · intro u hu
            exact exclude k (430+93*k) _ (by omega) ((priorTail u hu).trans_le (by omega))
        · have cap : CappedWeight.Target.Cap k n r v2 v3 v4 v5 0 := by
            refine Or.inr ?_
            rcases caps with ⟨j,hj,eq,h2,h3,h4,h5⟩|⟨j,hj,eq,h2,h3,h4,h5⟩|⟨a0,e,ha,he,eq,h2,h3,h4,h5⟩
            · exact Or.inl ⟨j,hj,eq,h2,h3,h4,h5,rfl⟩
            · exact Or.inr (Or.inl ⟨j,hj,eq,h2,h3,h4,h5,rfl⟩)
            · exact Or.inr (Or.inr ⟨a0,e,ha,he,eq,h2,h3,h4,h5,rfl⟩)
          refine Or.inr ⟨v2,v3,v4,v5,0,cap,address k n z S r (cap_weight k n r v2 v3 v4 v5 0 cap) phys rfl,?_,?_⟩
          · rw [UniformTM.run_add,powerRun,right_run]
            exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) tailEx
          · intro u hu
            exact exclude k (798+93*k) _ (by omega) ((priorTail u hu).trans_le (by omega))
      · have cap : CappedWeight.Target.Cap k n r (bitLength n) (n^j-a0-1) r 0 (e+1) :=
          Or.inl ⟨j,a0,e,hj,ha,he,eq,rfl,rfl,rfl,rfl,rfl⟩
        refine ⟨fit,t+d,clock R n r k t d 0 (width.trans pair) ((Nat.sub_le S p).trans pair) price
          (by simpa only [FixedRawLengthFence.fencePos] using phase) (by positivity),Or.inr ⟨fits,Or.inr
            ⟨bitLength n,n^j-a0-1,r,0,e+1,cap,address k n z S r (cap_weight k n r _ _ _ _ _ cap) phys rfl,?_,?_⟩⟩⟩
        · rw [UniformTM.run_add,seed,right_run]
          exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) ex
        · intro u hu
          exact exclude k (798+93*k) _ (by omega) ((before u hu).trans_le (by omega))
    · refine ⟨fit,t,clock R n r k t 0 0 (width.trans pair) ((Nat.sub_le S p).trans pair) price (by positivity) (by positivity),Or.inl ⟨by omega,over (by omega),?_⟩⟩
      simpa only [if_neg fits] using reached
end FullWeight
