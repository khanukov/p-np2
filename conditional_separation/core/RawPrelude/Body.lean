import RawPrelude.Kernel
import Complexity.PrivateInterfaceLookupResolvedCarry
namespace RawPrelude
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := ["Frame","paint","stage","overlay","overlay_frame","cleared_overlay","cleanup_D0"]
  let validated ← ofExcept (PartAPrivateCarry.batch (← getEnv) (rows.map fun s => (`RawPrelude.Kernel, PartAPrivateCarry.key ("RawPrelude."++s))))
  for (s,target) in rows.zip validated do

    let ns := [target]
    logInfo m!"private-term|{ns.head!}"
    modifyScope fun st => {st with openDecls := .explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
private def computed (V : Nat → Option Bool) (L n F r : Nat) :=
  RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
private theorem cleared (V : Nat → Option Bool) (k S z n F r : Nat)
    (room : S+z+n+3 < F)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → V i=some false)
    (phys : min (9+2*z+2^n) S < S) (rem : r=S-min (9+2*z+2^n) S)
    (logical : S < Cursor.Target.M k n z) :
    paint (stage (computed V (S+z+2) n F r) F r n 6) (S+z+2+1) (S+z+2+n+1)=
      Cursor.Target.image V k S n z F := by
  fromDonor "VirtualReady.Raw" "VirtualReady" "cleared_image" =>
    rw [show paint (stage (computed V (S+z+2) n F r) F r n 6) (S+z+2+1) (S+z+2+n+1)=
      Cursor.Target.scratch V F r n from OLD V (S+z+2) n F r (by omega) (by intro i lo hi; exact assn i lo (by omega))]
  funext i
  dsimp only [Cursor.Target.image]
  rw [if_pos phys,if_neg (by omega),← rem]
private theorem clear_D2 (k N B S z n Q F r : Nat) (V : Nat → Option Bool)
    (fr : Frame (computed V (S+z+2) n F r) (S+z+2) n Q F r)
    (room : S+z+n+3 < F)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → V i=some false)
    (phys : min (9+2*z+2^n) S < S) (rem : r=S-min (9+2*z+2^n) S)
    (logical : S < Cursor.Target.M k n z)
    (fit : F+5*r+n+7 < tapeLength N B) (hh : S+z+n+3 < tapeLength N B) :
    (Cursor.machine k).run (F-(S+z+2+n+1)+19*r+7*n+48)
      ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,by omega⟩,
        fun i => computed V (S+z+2) n F r i.val⟩=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hh⟩,
        fun i => Cursor.Target.image V k S n z F i.val⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "cleanup_run" =>
    have run:=OLD k N B (S+z+2) n Q F r (computed V (S+z+2) n F r) fr fit (by omega) (by omega)
  have direct : (Cursor.machine k).run (F-(S+z+2+n+1)+19*r+7*n+48)
      ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,by omega⟩,
        fun i => computed V (S+z+2) n F r i.val⟩=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+2+n+1,(by omega : S+z+2+n+1 < tapeLength N B)⟩,
        fun i => paint (stage (computed V (S+z+2) n F r) F r n 6) (S+z+2+1) (S+z+2+n+1) i.val⟩ := run
  rw [cleared V k S z n F r room assn phys rem logical] at direct
  exact direct.trans (Config.ext_parts rfl (Fin.ext (by change S+z+2+n+1=S+z+n+3; omega)) rfl)
private theorem clear_D0 (k N B S z n Q F r a b c d e : Nat) (V : Nat → Option Bool)
    (fr : Frame (computed V (S+z+2) n F r) (S+z+2) n Q F r)
    (room : S+z+n+3 < F)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → V i=some false)
    (phys : min (9+2*z+2^n) S < S) (rem : r=S-min (9+2*z+2^n) S)
    (logical : S < Cursor.Target.M k n z)
    (fit : F+5*r+n+7 < tapeLength N B) (hh : S+z+n+3 < tapeLength N B) :
    (Cursor.machine k).run (F-(S+z+2+n+1)+18*r+6*n+44)
      ⟨Cursor.q k (798+93*k),⟨F+1,by omega⟩,
        fun i => overlay (computed V (S+z+2) n F r) (S+z+2) n F r a b c d e i.val⟩=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hh⟩,
        fun i => Cursor.Target.image V k S n z F i.val⟩ := by
  have rp : 0 < r := by omega
  have frame:=overlay_frame _ (S+z+2) n Q F r a b c d e fr rp
  have run:=cleanup_D0 k N B (S+z+2) n Q F r _ frame fit (by omega)
  rw [cleared_overlay _ (S+z+2) n F r a b c d e rp,
    cleared V k S z n F r room assn phys rem logical] at run
  exact run.trans (Config.ext_parts rfl (Fin.ext (by change S+z+2+n+1=S+z+n+3; omega)) rfl)
private theorem clock (R k t d : Nat) (ht : t ≤ 268435456*(k+1)*(R+1)^4)
    (hd : d ≤ 524288*(R+1)^3) : t+d ≤ 2147483648*(k+1)*(R+1)^5 := by
  have a : (R+1)^4 ≤ (R+1)^5 := by
    calc (R+1)^4 ≤ (R+1)^4*(R+1) := Nat.le_mul_of_pos_right _ (by omega)
         _ = (R+1)^5 := by ring
  have b : (R+1)^3 ≤ (R+1)^5 := by
    calc (R+1)^3 ≤ (R+1)^3*(R+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
         _ = (R+1)^5 := by ring
  have ht' := Nat.mul_le_mul_left (268435456*(k+1)) a
  have hd' := Nat.mul_le_mul_left 524288 b
  have hk := Nat.mul_le_mul_left (524288*(R+1)^5) (show 1 ≤ k+1 by omega)
  nlinarith only [ht,hd,ht',hd',hk,Nat.zero_le ((k+1)*(R+1)^5)]
private theorem cleanup_price (R n r F H : Nat) (hn : n ≤ R) (hr : r ≤ R) (hf : F=3*R+2) :
    F-H+19*r+7*n+48 ≤ 524288*(R+1)^3 := by
  have d : F-H+19*r+7*n+48 ≤ 64*(R+1) := by omega
  have p : R+1 ≤ (R+1)^3 := by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
  have mul:=Nat.mul_le_mul_left 64 p
  omega
private theorem right_run {k N B : Nat} (t : Nat) (c : Config (Cursor.machine k).stateCount N B) :
    (AllArityCursor.machine k).run t (SmallIngress.producer.seqEmbedRight (Cursor.machine k) c)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run t c) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).run t _=_
  rw [UniformTM.seq_run_right]
private theorem no_verdict (k : Nat) {N B : Nat} (c : Config (AllArityCursor.machine k).stateCount N B) (t : Nat)
    (atEnd : ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (613+93*k)) ∨
      ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) :
    ∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
      ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject := by
  have controls:=AllArityCursor.control_values k
  have va : (AllArityCursor.machine k).accept.val=327 := controls.2.2.1
  have vr : (AllArityCursor.machine k).reject.val=328 := controls.2.2.2
  have normal : (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (613+93*k))).val=901+93*k := by
    change 288+(613+93*k)%Cursor.stateCount k=901+93*k
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; omega
  have ready : (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)).val=1224+93*k := by
    change 288+((64+265+82*k+1+11*k+604+2)%Cursor.stateCount k)=1224+93*k
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; omega
  apply (AllArityCursor.machine k).no_terminal_of_le c
  all_goals intro h
  all_goals rcases atEnd with done | done
  all_goals have eq:=congrArg Fin.val (done.symm.trans h)
  all_goals first | rw [normal,va] at eq | rw [normal,vr] at eq | rw [ready,va] at eq | rw [ready,vr] at eq
  all_goals omega
end RawPrelude
