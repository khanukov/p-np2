import RawPrelude.Target
namespace RawPrelude
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
set_option maxRecDepth 10000
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private abbrev Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Frame" => exact OLD T L n Q F r
private def paint (T : Nat → Option Bool) (lo hi : Nat) : Nat → Option Bool :=
  fun i => if lo ≤ i ∧ i < hi then some false else T i
private def stage (T : Nat → Option Bool) (F r n : Nat) : Nat → Nat → Option Bool
  | 0 => T
  | j+1 => paint (stage T F r n j) (D F r n j+1) (D F r n (j+1))
private abbrev bank (F r n i : Nat) : Prop :=
  F+1 < i ∧ i < F+r+2 ∨ F+r+2 < i ∧ i < F+r+n+3 ∨
  F+r+n+3 < i ∧ i < F+2*r+n+4 ∨ F+2*r+n+4 < i ∧ i < F+3*r+n+5 ∨
  F+3*r+n+5 < i ∧ i < F+4*r+n+6 ∨ F+4*r+n+6 < i ∧ i < F+5*r+n+7
private def overlay (T : Nat → Option Bool) (L n F r a b c d e : Nat) :=
  CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r a b c d e
private theorem overlay_old (T : Nat → Option Bool) (L n F r a b c d e i : Nat)
    (rp : 0 < r) (outside : ¬bank F r n i) (assn : ¬(L < i ∧ i < L+n+1)) :
    overlay T L n F r a b c d e i=T i := by
  dsimp only [overlay,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
  dsimp only [bank] at outside
  rw [if_neg assn,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem overlay_frame (T : Nat → Option Bool) (L n Q F r a b c d e : Nat)
    (fr : Frame T L n Q F r) (rp : 0 < r) : Frame (overlay T L n F r a b c d e) L n Q F r := by
  rcases fr with ⟨paid,room,blank,cells,fence,gap,marks,sep,right,assn⟩
  have old (i : Nat) (hi : i ≤ F) (out : i ≤ L ∨ L+n+1 ≤ i) :
      overlay T L n F r a b c d e i=T i :=
    overlay_old T L n F r a b c d e i rp (by dsimp only [bank]; omega) (by omega)
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Frame.mk" =>
    refine OLD paid room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    change overlay T L n F r a b c d e (D F r n j)=none
    rw [overlay_old T L n F r a b c d e _ rp]
    · exact blank j hj
    · interval_cases j <;> dsimp only [bank,D] <;> omega
    · interval_cases j <;> dsimp only [D] <;> omega
  · intro j hj i lo hi
    have occupied := cells j hj i lo hi
    dsimp only [overlay,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    repeat' first | (exact ⟨_,rfl⟩) | (split <;> try assumption)
  · rw [old F le_rfl (Or.inr (by omega))]; exact fence
  · intro i lo hi; rw [old i (by omega) (Or.inr (by omega))]; exact gap i lo hi
  · intro i lo hi; rw [old i (by omega) (Or.inr (by omega))]; exact marks i lo hi
  · rw [old L (by omega) (Or.inl le_rfl)]; exact sep
  · rw [old (L+n+1) (by omega) (Or.inr le_rfl)]; exact right
  · intro i lo hi
    dsimp only [overlay,CappedWeight.Target.image]
    rw [if_pos ⟨lo,hi⟩]; exact ⟨_,rfl⟩
private theorem cleared_overlay (T : Nat → Option Bool) (L n F r a b c d e : Nat) (rp : 0 < r) :
    paint (stage (overlay T L n F r a b c d e) F r n 6) (L+1) (L+n+1)=
      paint (stage T F r n 6) (L+1) (L+n+1) := by
  funext i
  by_cases assn : L < i ∧ i < L+n+1
  · dsimp only [paint]; rw [if_pos (by omega),if_pos (by omega)]
  · have noassn : ¬(L+1 ≤ i ∧ i < L+n+1) := by omega
    change (if L+1 ≤ i ∧ i < L+n+1 then some false else stage _ F r n 6 i)=
      if L+1 ≤ i ∧ i < L+n+1 then some false else stage T F r n 6 i
    rw [if_neg noassn,if_neg noassn]
    fromDonor "VirtualReady.Raw" "VirtualReady" "stage_exact" =>
      rw [show stage (overlay T L n F r a b c d e) F r n 6 i=
        if bank F r n i then some false else overlay T L n F r a b c d e i from OLD _ F r n i,
        show stage T F r n 6 i=if bank F r n i then some false else T i from OLD T F r n i]
    by_cases h : bank F r n i
    · rw [if_pos h,if_pos h]
    · rw [if_neg h,if_neg h]; exact overlay_old T L n F r a b c d e i rp h assn
private theorem cleanup_D0 (k N B L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : F+5*r+n+7 < tapeLength N B) (hh : L+n+1 < tapeLength N B) :
    (Cursor.machine k).run (F-(L+n+1)+18*r+6*n+44)
      ⟨Cursor.q k (798+93*k),⟨F+1,by omega⟩,fun i => T i.val⟩=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨L+n+1,hh⟩,
        fun i => paint (stage T F r n 6) (L+1) (L+n+1) i.val⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "cleanup_path" => have path:=OLD k (F+5*r+n+7) L n Q F r T fr le_rfl
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Path.execute" => have run:=OLD (N:=N) (B:=B) path fit
  have ready : Cursor.q k (889+93*k+47)=Cursor.mReady k ⟨2,by decide⟩ := by
    apply Fin.ext
    change (889+93*k+47)%Cursor.stateCount k=(64+265+82*k+1+11*k+604+2)%Cursor.stateCount k
    congr 1; omega
  have direct : (Cursor.machine k).run (F-(L+n+1)+18*r+6*n+44)
      ⟨Cursor.q k (798+93*k),⟨F+1,by omega⟩,fun i => T i.val⟩=
      ⟨Cursor.q k (889+93*k+47),⟨L+n+1,hh⟩,
        fun i => paint (stage T F r n 6) (L+1) (L+n+1) i.val⟩ := run
  rw [ready] at direct
  exact direct
end RawPrelude
