import VirtualFinalClosure.MaskSeed
import AllArityWorkspace.Runtime
namespace VirtualFinalClosure.MaskedLength
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",(0:Nat)),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.arena","arenaCell",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong physical high-blank length term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique physical high-blank length term {mod}/{key}"
private theorem full (V : Nat → Option Bool) (L n F r bound : Nat)
    (room : L+n+1 < F) (fit : F+5*r+n+7 < bound)
    (tail : ∀ i,bound ≤ i → V i=none) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    masked Y bound=Y:=by
  intro Y
  funext i
  by_cases inside : i < bound
  · exact maskedLow Y bound i inside
  · have outside : bound ≤ i:=by omega
    have zero : Y i=none:=by
      dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      exact tail i outside
    dsimp only [masked]
    rw [if_neg inside,zero]
/-- The SAME initial finite tape has actual blank high cells. Hence its
unbounded explicit length image equals its old-budget mask on the larger run;
this is a cell theorem, never a different execution/deadline transport. -/
private theorem actual {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    masked Y (tapeLength R C)=Y:=by
  intro S R C L F r U V Y
  obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨_tail,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R C at fit
  have arena : S+z+n+3+2^n < F:=arenaCell cells
  have room : L+n+1 < F:=by dsimp only [L];have h:=Nat.two_pow_pos n;omega
  apply full V L n F r (tapeLength R C) room fit
  intro i hi
  dsimp only [V,Stream.Target.image]
  rw [if_neg (by dsimp only [L] at room;omega),if_neg (by omega)]
  simp only [Bool.false_eq_true,false_and,ite_false]
  change Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n) i=none
  dsimp only [Body.extend]
  rw [dif_neg (by change ¬i < tapeLength R C;omega)]
#print axioms full
#print axioms actual
end VirtualFinalClosure.MaskedLength
