import VirtualFinalClosure.LengthFrame
namespace VirtualFinalClosure.LengthBanks
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("actual_cells","actualCells"),("Cells.arena","arenaCell")] do
    let found:=env.constants.toList.filter fun (name,_)=>
      name.toString.startsWith "_private.AllArityWorkspace.Runtime." &&
      name.toString.endsWith (".AllArityWorkspace."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual length bank1/frame source {key}"
private theorem bank1_occupied (V : Nat → Option Bool) (L n F r : Nat)
    (room : L+n+1 < F) :
    ∀ i,F+r+2 < i → i < F+r+n+3 → ∃ b,
      RuntimeBitLength.Target.fullImage
        (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r i=some b := by
  intro i lo hi
  dsimp only [RuntimeBitLength.Target.fullImage]
  rw [if_neg (by omega),if_pos ⟨lo,hi⟩]
  exact ⟨_,rfl⟩
private theorem d2_blank (V : Nat → Option Bool) (L n F r : Nat)
    (room : L+n+1 < F) (blank : V (F+r+n+3)=none) :
    RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r (F+r+n+3)=none := by
  dsimp only [RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  exact blank
/-- Literal blank extension, fixed BEFORE the continuation. It cannot conceal
post-run corruption by selecting an arbitrary exterior after execution. -/
private def masked (T : Nat → Option Bool) (bound : Nat) : Nat → Option Bool :=
  fun i=>if i < bound then T i else none
private def masked_type : (Nat → Option Bool) → Nat → Nat → Option Bool := masked
private theorem masked_low (T : Nat → Option Bool) (bound i : Nat) (hi : i < bound) :
    masked T bound i=T i := by dsimp only [masked];rw [if_pos hi]
private theorem actual_bank1 {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let S:=a+m;let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    F+5*r+n+7 < tapeLength R B ∧ Y (F+r+n+3)=none ∧
      (∀ i,F+r+2 < i → i < F+r+n+3 → ∃ b,Y i=some b) := by
  intro S R B L F r U V Y
  obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R B at fit
  obtain ⟨fr,_short,fresh⟩:=actualCells x w gamma cap rows
  change ∀ i : Fin (tapeLength R B),F < i.val → V i.val=none at fresh
  have arena:=arenaCell fr
  have room : L+n+1 < F:=by
    change S+z+n+3+2^n < F at arena
    dsimp only [L]
    have paid:=Nat.two_pow_pos n
    omega
  have blank : V (F+r+n+3)=none:=fresh ⟨F+r+n+3,lt_of_le_of_lt (by omega) fit⟩ (by change F < F+r+n+3;omega)
  exact ⟨fit,d2_blank V L n F r room blank,bank1_occupied V L n F r room⟩
#print axioms bank1_occupied
#print axioms d2_blank
#print axioms masked_type
#print axioms masked_low
#print axioms actual_bank1
end VirtualFinalClosure.LengthBanks
