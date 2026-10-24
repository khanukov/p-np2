import PostWeight.Length
namespace PostWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def seed (V : Nat → Option Bool) (L n F r : Nat) :=
  AllArityBitLength.Target.seedImage
    (RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) F r n
private theorem wpos (k n : Nat) : 0 < Cursor.Target.W k n := by
  unfold Cursor.Target.W
  cases k with
  | zero => simp
  | succ k => positivity
private theorem ell_le (v : Nat) : bitLength v ≤ v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases zero : v=0
    · subst v; simp [bitLength]
    · fromDonor "PostWeight.Length" "PostWeight" "lengthStep" => have eq:=OLD v (by omega)
      have small:=ih (v/2) (by omega)
      omega
private theorem seed_blank (V : Nat → Option Bool) (L n F r : Nat) (room : L+n+1 < F) (rp : 0 < r)
    (fresh : ∀ i, F < i → i ≤ F+5*r+n+7 → V i=none) (j : Nat) (hj : j ≤ 6) :
    seed V L n F r (D F r n j)=none := by
  have bound:=Nat.min_le_right (bitLength n) r
  interval_cases j
  all_goals simp only [seed,AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage,
    CappedWorkspace.Target.image,SuffixCap.Target.image,D]
  all_goals repeat' rw [if_neg (by omega)]
  all_goals exact fresh _ (by omega) (by omega)
private theorem seed_occupied (V : Nat → Option Bool) (L n F r i : Nat)
    (bank : (F+1 < i ∧ i < F+r+2) ∨ (F+r+2 < i ∧ i < F+r+n+3)) :
    ∃ b, seed V L n F r i=some b := by
  dsimp only [seed,AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage,
    CappedWorkspace.Target.image,SuffixCap.Target.image]
  repeat' first | (exact ⟨_,rfl⟩) | (exfalso; omega) | split
private abbrev Banks (T : Nat → Option Bool) (L n F r : Nat) : Prop := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Banks" => exact OLD T L n F r
private theorem join_clock (P W t d : Nat) (ht : t ≤ 2048*(W+1)*(P+1)^2) (hd : d ≤ P+1) :
    t+d ≤ 4096*(W+1)*(P+1)^2 := by
  have mul:=Nat.mul_le_mul_right ((P+1)^2) (show 1 ≤ W+1 by omega)
  nlinarith only [ht,hd,mul,Nat.zero_le (P*P),Nat.zero_le P]
private theorem kernel_run (k N B L n F r : Nat) (T : Nat → Option Bool)
    (room : L+n+1 < F)
    (blank : ∀ j, j ≤ 6 → T (D F r n j)=none)
    (b0 : ∀ i, F+1 < i → i < F+r+2 → ∃ b, T i=some b)
    (b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → ∃ b, T i=some b)
    (g W : Nat) (wr : W ≤ r) (fit : F+5*r+n+7 < tapeLength N B) :
    ∃ (t : Nat) (h : F+1 < tapeLength N B),
      t ≤ 4096*(W+1)*(F+5*r+n+8)^2 ∧
      (Cursor.machine k).run t
        (⟨Cursor.q k (430+93*k),⟨F+r+n+3,by omega⟩,fun i => CappedWeight.Target.image T L n F r 0 g W 0 0 i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k (613+93*k),⟨F+1,h⟩,fun i => CappedWeight.Target.image T L n F r (bitLength W) 0 0 W 0 i.val⟩ := by
  have frame : Banks T L n F r := by
    fromDonor "PostWeight.Kernel" "PostWeight" "Banks.mk" => exact OLD room blank
  fromDonor "PostWeight.Length" "PostWeight" "postLength" =>
    obtain ⟨t,ht,path⟩:=OLD (k:=k) frame (P:=F+5*r+n+7) (by rfl) g W wr ((ell_le W).trans wr)
  fromDonor "PostWeight.Length" "PostWeight" "seekStart" => have tail:=OLD (k:=k) frame (P:=F+5*r+n+7) (by rfl) (bitLength W) W b0 b1
  fromDonor "PostWeight.Kernel" "PostWeight" "Path.append" => have joined:=OLD path tail
  fromDonor "PostWeight.Kernel" "PostWeight" "Path.execute" => have run:=OLD (N:=N) (B:=B) joined fit
  refine ⟨t+(3*r+n+8),by omega,?_,run⟩
  exact join_clock (F+5*r+n+7) W t (3*r+n+8) ht (by omega)
private theorem price (R n r W t : Nat) (hn : n ≤ R) (hr : r ≤ R) (hw : W ≤ r)
    (ht : t ≤ 4096*(W+1)*(3*R+2+5*r+n+8)^2) : t ≤ 524288*(R+1)^3 := by
  have a : W+1 ≤ R+1 := by omega
  have b : 3*R+2+5*r+n+8 ≤ 10*(R+1) := by omega
  have mul:=Nat.mul_le_mul (Nat.mul_le_mul_left 4096 a) (Nat.pow_le_pow_left b 2)
  nlinarith only [ht,mul,Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]
private theorem no_verdict {k N B t : Nat} (c : Config (Cursor.machine k).stateCount N B)
    (last : ((Cursor.machine k).run t c).state=Cursor.q k (613+93*k)) :
    ∀ u, u ≤ t → ((Cursor.machine k).run u c).state≠(Cursor.machine k).accept ∧
      ((Cursor.machine k).run u c).state≠(Cursor.machine k).reject := by
  apply (Cursor.machine k).no_terminal_of_le c
  all_goals intro bad
  all_goals rw [last] at bad
  all_goals have values:=congrArg Fin.val bad
  all_goals first |
    change (613+93*k)%Cursor.stateCount k=39%Cursor.stateCount k at values |
    change (613+93*k)%Cursor.stateCount k=40%Cursor.stateCount k at values
  all_goals rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega),Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at values
  all_goals omega
/-- Connected exact W-produced start to the completed bitLength(W) boundary.
This is a prepared continuation; it does not assume or establish raw-to-W. -/
theorem prepared_length (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    (pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)))
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    p<S → bitLength n≤r → Cursor.Target.W k n≤r →
    ∀ fit : F+5*r+n+7 < tapeLength R B,
    ∃ (t : Nat) (h : F+1 < tapeLength R B),
      t≤524288*(R+1)^3 ∧
      (Cursor.machine k).run t
        (⟨Cursor.q k (430+93*k),⟨F+r+n+3,by omega⟩,fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩ : Config (Cursor.machine k).stateCount R B)=
        ⟨Cursor.q k (613+93*k),⟨F+1,h⟩,fun i => CappedWeight.Target.image Z L n F r (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ ∧
      ∀ u, u ≤ t →
        let c : Config (Cursor.machine k).stateCount R B :=
          ⟨Cursor.q k (430+93*k),⟨F+r+n+3,by omega⟩,fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩
        ((Cursor.machine k).run u c).state≠(Cursor.machine k).accept ∧
        ((Cursor.machine k).run u c).state≠(Cursor.machine k).reject := by
  intro S R B n L F p r U V X Y Z phys fits wr fit
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
    have h:=accepted
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
    split at h
    · rename_i shape; cases shape; simpa only [AcceptedBody.concat_eq_append] using h
    · contradiction
  have table:=AcceptedBody.table_support k (Fin.append x w) parsed semantic
  have width : n ≤ S := by have lt:=Nat.lt_two_pow_self (n:=n); change 2^n ≤ S at table; omega
  have nr : n ≤ R := by dsimp [R,pairLength]; omega
  have rr : r ≤ R := by have h:=Nat.sub_le S p; dsimp [R,pairLength]; omega
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" => obtain ⟨fr,_,fresh⟩:=OLD x w gamma cap rows
  fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.arena" => have arena:=OLD fr
  change S+z+n+3+2^n < F at arena
  change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
  have room : L+n+1 < F := by
    have lower : S+z+n+3 < F := (Nat.le_add_right _ _).trans_lt arena
    have eq : L+n+1=S+z+n+3 := by dsimp only [L]; omega
    rw [eq]; exact lower
  have rp : 0 < r := lt_of_lt_of_le (wpos k n) wr
  have freshNat (i : Nat) (lo : F < i) (hi : i ≤ F+5*r+n+7) : V i=none :=
    fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo
  have blank (j : Nat) (hj : j ≤ 6) : Z (D F r n j)=none := seed_blank V L n F r room rp freshNat j hj
  obtain ⟨t,h,ht,run⟩:=kernel_run k R B L n F r Z room blank
    (by intro i lo hi; exact seed_occupied V L n F r i (Or.inl ⟨lo,hi⟩))
    (by intro i lo hi; exact seed_occupied V L n F r i (Or.inr ⟨lo,hi⟩)) (n^k+k) (Cursor.Target.W k n) wr fit
  exact ⟨t,h,price R n r (Cursor.Target.W k n) t nr rr wr ht,run,no_verdict _ (congrArg Config.state run)⟩
end PostWeight
