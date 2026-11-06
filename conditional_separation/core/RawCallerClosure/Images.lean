import RawCallerClosure.Arithmetic
import TotalIngressClosure.NormalFrame
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName,kind) in [
    (`FullIngressClosure.Frame,`FullIngressClosure,"ready_low","readyLow","theorem"),
    (`FullIngressClosure.Frame,`FullIngressClosure,"ready_tail","readyTail","theorem"),
    (`FullIngressClosure.Frame,`FullIngressClosure,"actual_source","actualSource","theorem"),
    (`AllArityBitLength.Raw,`AllArityBitLength,"actual_cells","actualCells","theorem")] do
    let found:=e.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith ("."++ns.toString++"."++leaf)
    let [(n,ci)]:=found | throwError "Nonunique immutable image term {owner}/{leaf}"
    let actual:=match ci with |.thmInfo _=>"theorem"|_=>"other"
    unless actual==kind do throwError "Wrong image term kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong image owner"
    logInfo m!"ordinary-image|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private def table {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (z n : Nat) : Nat → Option Bool :=
  Stream.Target.image (Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n))
    (a+m) z n (9+2*z) (2^n) (2^n) false
private def ready (V : Nat → Option Bool) (L n F r g W : Nat) : Nat → Option Bool :=
  CarryWindow.Target.image (CappedWeight.Target.image (AllArityBitLength.Target.seedImage
    (RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) F r n)
    L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W
private theorem ready_low (V : Nat → Option Bool) (L n F r g W i : Nat)
    (room:L+n+1 < F) (hi:i ≤ F) (outside:i ≤ L ∨ L+n+1 ≤ i) : ready V L n F r g W i=V i :=
  readyLow V L n F r g W i room hi outside
private theorem ready_tail (V : Nat → Option Bool) (L n F r g W i : Nat)
    (room:L+n+1 < F) (hi:F+5*r+n+7 < i) : ready V L n F r g W i=V i :=
  readyTail V L n F r g W i room hi
private theorem zero_width {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1)) (zero:z=0) : n=0 := by
  obtain ⟨q,qg,_length,_lower,upper,_borrow,_digits,_high⟩:=decremented_register_digits x w header
  have eq:q=z:=Option.some.inj (qg.symm.trans gamma)
  subst q
  subst z
  norm_num at upper
  omega
private theorem low_source {a m n z B : Nat} (x : Bitstring a) (w : Bitstring m)
    (g W r : Nat) (room:a+m+z+n+3 < FixedRawLengthFence.fencePos (pairLength a m))
    (i : Nat) (before:i < a+m) :
    ready (table B x w z n) (a+m+z+2) n (FixedRawLengthFence.fencePos (pairLength a m)) r g W i=
      SmallIngress.prepared B x w z n ⟨i,by unfold tapeLength pairLength;omega⟩ := by
  rw [ready_low (table B x w z n) (a+m+z+2) n (FixedRawLengthFence.fencePos (pairLength a m)) r g W i (by omega) (by omega) (Or.inl (by omega))]
  dsimp only [table,Stream.Target.image]
  rw [if_neg (by omega),if_neg (by omega)]
  simp only [Bool.false_eq_true,false_and,if_false]
  dsimp only [Body.extend]
  rw [dif_pos (by unfold tapeLength pairLength;omega)]
  dsimp only [Body.installedTape]
  rw [if_neg (by omega)]
private theorem source_all {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (g W r : Nat)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap:n < FixedRawLengthFence.capacity a m z)
    (room:a+m+z+n+3 < FixedRawLengthFence.fencePos (pairLength a m))
    (i : Nat) (above:9+2*z ≤ i) (before:i < a+m) :
    ready (table (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n
      (FixedRawLengthFence.fencePos (pairLength a m)) r g W i=some ((Fin.append x w) ⟨i,before⟩) := by
  rw [ready_low (table (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n (FixedRawLengthFence.fencePos (pairLength a m)) r g W i (by omega) (by omega) (Or.inl (by omega))]
  exact actualSource x w gamma (FixedRawLengthFence.resource_bounds _).1 (Nat.le_of_lt cap) i above before
private theorem gamma_holes {a m n z : Nat} (x : Bitstring a) (w : Bitstring m) (g W r : Nat)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (physical:9+2*z < a+m)
    (room:a+m+z+n+3 < FixedRawLengthFence.fencePos (pairLength a m)) :
    let I:=ready (table (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n
      (FixedRawLengthFence.fencePos (pairLength a m)) r g W
    I (9+2*z-2)=none ∧ I (9+2*z-1)=some true := by
  intro I
  have walk:FixedGammaTargetPayloadExhaustion.termWalk (a+m) z=z := by
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
    exact Nat.min_eq_left (by omega)
  have low (i : Nat) (hi:i < a+m) : I i=SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n
      ⟨i,by unfold tapeLength pairLength;omega⟩:=low_source x w g W r room i hi
  constructor
  · rw [low _ (by omega)]
    by_cases hz:z=0
    · have hn:=zero_width x w gamma header hz
      subst z
      subst n
      dsimp only [SmallIngress.prepared]
      rw [if_pos (by decide)]
    · dsimp only [SmallIngress.prepared]
      rw [if_neg (by omega)]
      dsimp only [FixedRawLengthFence.countdownTape]
      rw [if_neg (by unfold FixedRawLengthFence.fencePos pairLength;omega)]
      dsimp only [FixedGammaTargetUnaryCountdown.loopTape]
      rw [if_pos (by omega)]
      dsimp only [FixedGammaTargetPayloadExhaustion.finishTape]
      rw [walk,if_pos (by omega)]
  · rw [low _ (by omega)]
    dsimp only [SmallIngress.prepared]
    rw [if_neg (by omega)]
    dsimp only [FixedRawLengthFence.countdownTape]
    rw [if_neg (by unfold FixedRawLengthFence.fencePos pairLength;omega)]
    dsimp only [FixedGammaTargetUnaryCountdown.loopTape]
    rw [if_pos (by omega)]
    dsimp only [FixedGammaTargetPayloadExhaustion.finishTape]
    rw [walk,if_neg (by omega),if_pos (by omega)]
private theorem tail_all {a m n z : Nat} (x : Bitstring a) (w : Bitstring m) (g W r : Nat)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap:n < FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n < FixedRawLengthFence.fencePos (pairLength a m))
    (i : Nat) (above:FixedRawLengthFence.fencePos (pairLength a m)+5*r+n+7 < i) :
    ready (table (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n
      (FixedRawLengthFence.fencePos (pairLength a m)) r g W i=none := by
  have room:a+m+z+2+n+1 < FixedRawLengthFence.fencePos (pairLength a m) := by
    calc
      a+m+z+2+n+1=a+m+z+n+3 := by omega
      _ ≤ a+m+z+n+3+2^n := Nat.le_add_right _ _
      _ < FixedRawLengthFence.fencePos (pairLength a m) := arena
  rw [ready_tail (table (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n (FixedRawLengthFence.fencePos (pairLength a m)) r g W i room above]
  obtain ⟨_cells,_fit,fresh⟩:=actualCells x w gamma cap (by omega)
  by_cases inside:i < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))
  · exact fresh ⟨i,inside⟩ (show FixedRawLengthFence.fencePos (pairLength a m) < i by omega)
  · dsimp only [table,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    simp only [Bool.false_eq_true,false_and,if_false]
    dsimp only [Body.extend]
    rw [dif_neg inside]
end RawCallerClosure
