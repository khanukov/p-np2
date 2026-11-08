import VirtualFinalClosure.GrownFinalImage
namespace VirtualFinalClosure.NormalImage
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.GrownFinalImage","VirtualFinalClosure.GrownFinalImage","high_blank","highBlank"),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact normal raw high-tail interface {mod}/{key}"
private theorem fields_high (V : Nat → Option Bool) (L n F r g W i : Nat)
    (room : L+n+1 < F) (high : F+5*r+n+7 < i) :
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W i=V i:=by
  intro X Y Z
  have limit:=Nat.min_le_right (bitLength n) r
  dsimp only [CarryWindow.Target.image,CappedWeight.Target.image,Z,AllArityBitLength.Target.seedImage,
    Y,RuntimeBitLength.Target.fullImage,X,CappedWorkspace.Target.image,SuffixCap.Target.image]
  repeat' rw [if_neg (by omega)]
private theorem prepared_high (I : Nat → Option Bool) (S M F r n g W i : Nat)
    (source : S < i) (high : SerializedBody.delimiter F r n 12 < i) :
    SerializedBody.prepared I S M F r n g W i=I i:=by
  dsimp only [SerializedBody.prepared]
  rw [if_neg (by omega)]
  dsimp only [SerializedBody.image]
  rw [if_pos (Or.inr high)]
/-- The exact original normal ABI has genuinely blank high cells above its
quadratic tape. This is a pointwise formula theorem used with the existing
move-room execution transport; it does not assume elapsed≤that allocation. -/
private theorem high_blank {a m n z : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let S:=a+m;let R:=pairLength a m;let B0:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
    let W:=Cursor.Target.W k n;let M:=Cursor.Target.M k n z;let g:=n^k+k
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) Q Q false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W
    SerializedBody.delimiter F r n 12 < tapeLength R B0 →
      ∀ i,tapeLength R B0 ≤ i → SerializedBody.prepared I S M F r n g W i=none:=by
  intro S R B0 L F Q p r W M g U V X Y Z I fit i hi
  obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨arena,_src,_end,_reg,_sep,_assn,_last,_marks,_gap,_fence⟩:=cells
  change S+z+n+3+Q < F at arena
  have room : L+n+1 < F:=by
    have low:=Nat.le_add_right (S+z+n+3) Q
    have below:=low.trans_lt arena
    have same : L+n+1=S+z+n+3:=by dsimp only [L];omega
    rwa [same]
  have large : F+13*r+2*n+16 < i:=by
    change F+13*r+2*n+16 < tapeLength R B0 at fit
    exact fit.trans_le hi
  have high : F+5*r+n+7 < i:=by omega
  have source : S < i:=by dsimp only [L] at room;omega
  rw [prepared_high I S M F r n g W i source (by exact large)]
  exact (fields_high V L n F r g W i room high).trans (highBlank x w gamma cap rows i (by omega))
private theorem extended_tape {states N C B : Nat} (h : C ≤ B) (q : Fin states)
    (head : Fin (tapeLength N C)) (T : Nat → Option Bool)
    (blank : ∀ i,tapeLength N C ≤ i → T i=none) :
    IngressAllocation.extendConfig h (⟨q,head,fun i=>T i.val⟩ : Config states N C)=
      ⟨q,⟨head.val,by have bound:=head.isLt;dsimp only [tapeLength] at bound ⊢;omega⟩,
        fun i=>T i.val⟩:=by
  apply Config.ext_parts
  · rfl
  · rfl
  · funext i
    change (if small : i.val < tapeLength N C then T (⟨i.val,small⟩ : Fin (tapeLength N C)).val else none)=T i.val
    by_cases low : i.val < tapeLength N C
    · rw [dif_pos low]
    · rw [dif_neg low];exact (blank i.val (by omega)).symm
#print axioms fields_high
#print axioms prepared_high
#print axioms high_blank
#print axioms extended_tape
end VirtualFinalClosure.NormalImage
