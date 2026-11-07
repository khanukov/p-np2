import RawCallerClosure.Frame
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf,kind) in [(`RawCallerClosure.Images,"ready","definition"),
      (`RawCallerClosure.Images,"table","definition"),(`RawCallerClosure.Images,"tail_all","theorem")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "RawCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact image lift"
    let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
    unless actual==kind do throwError "Wrong lift kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong lift owner"
    logInfo m!"ordinary-lift|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem after_workspace (F r n i : Nat)
    (h:SerializedBody.delimiter F r n 12 < i) : F+5*r+n+7 < i := by
  change F+13*r+2*n+16 < i at h
  omega
private theorem prepared_high {a m n z : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap:n < FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n < FixedRawLengthFence.fencePos (pairLength a m))
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos (pairLength a m))
      (a+m-min (9+2*z+2^n) (a+m)) n 12 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))) :
    let S:=a+m;let R:=pairLength a m;let F:=FixedRawLengthFence.fencePos R
    let r:=S-min (9+2*z+2^n) S
    let I:=ready (table (FixedRawLengthFence.allocation R) x w z n) (S+z+2) n F r (n^k+k) (Cursor.Target.W k n)
    ∀ i,tapeLength R (FixedRawLengthFence.allocation R) ≤ i →
      SerializedBody.prepared I S (Cursor.Target.M k n z) F r n (n^k+k) (Cursor.Target.W k n) i=none := by
  intro S R F r I i hi
  have outside:SerializedBody.delimiter F r n 12 < i:=lt_of_lt_of_le fit hi
  dsimp only [SerializedBody.prepared]
  split_ifs
  · rfl
  · dsimp only [SerializedBody.image]
    rw [if_pos (Or.inr outside)]
    exact tail_all x w (n^k+k) (Cursor.Target.W k n) r gamma cap arena i (after_workspace F r n i outside)
private theorem extend_image {states N C B : Nat} (budget:C≤B) (q : Fin states)
    (H : Nat) (small:H < tapeLength N C) (large:H < tapeLength N B) (T : Nat → Option Bool)
    (high:∀ i,tapeLength N C ≤ i → T i=none) :
    IngressAllocation.extendConfig budget (⟨q,⟨H,small⟩,fun i=>T i.val⟩:Config states N C)=
      (⟨q,⟨H,large⟩,fun i=>T i.val⟩:Config states N B) := by
  apply Config.ext_parts
  · rfl
  · exact Fin.ext rfl
  · funext i
    change (if hi:i.val<tapeLength N C then T i.val else none)=T i.val
    by_cases hi:i.val<tapeLength N C
    · rw [dif_pos hi]
    · rw [dif_neg hi,high i.val (by omega)]
end RawCallerClosure
