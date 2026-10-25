import VirtualFinalClosure.MaskSeed
import VirtualFinalClosure.LengthGrowFrame
import VirtualFinalClosure.PowerSeedFrame
namespace VirtualFinalClosure.InitialWeightFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("PowerDriver.Kernel","PowerDriver","Frame","PowerFrame",(2:Nat)),
      ("PowerDriver.Raw","PowerDriver","prepared_seed","preparedSeed",(1:Nat)),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","actualFrame",(1:Nat)),
      ("VirtualFinalClosure.LengthGrowFrame","VirtualFinalClosure.LengthGrowFrame","banks","banks",(1:Nat)),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",(1:Nat)),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",(0:Nat)),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",(1:Nat)),
      ("VirtualFinalClosure.MaskSeed","VirtualFinalClosure.MaskSeed","full","maskFull",(1:Nat)),
      ("TotalIngressClosure.SeedTotal","TotalIngressClosure","seed_empty","seedEmpty",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.arena","cell_arena",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.sep","cell_sep",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.right","cell_right",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.marks","cell_marks",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.gap","cell_gap",(1:Nat)),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.fence","cell_fence",(1:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual initial W operand frame {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual initial W operand frame {mod}/{key}"
/-- Initial q308's FULL masked tape supplies the real seed/W frame.
Every cell is derived from the same raw gamma/installed source, no rho premise. -/
private theorem actual {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (fits : bitLength n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let S:=a+m;let L:=S+z+2;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let F:=3*R+2;let r:=S-min (9+2*z+2^n) S;let P:=F+5*r+n+7
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    Frame T S L (L+n+1) (2^n) F ∧ 0 < r ∧ P < tapeLength R C ∧
      (∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none) ∧
      (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) → ∃ b,T i=some b) ∧
      T (F+2*r+n+5)=some false ∧ PowerFrame (AllArityBitLength.Target.seedImage T F r n) L n (2^n) F r := by
  intro S L R C F r P U V Y T
  obtain ⟨fr,arena,pos,_source,_b0,_d1,_sourceCells⟩:=actualFrame x w gamma cap rows physical
  obtain ⟨cells,_short,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨_tail,oldFit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change P < tapeLength R C at oldFit
  change ∀ i : Fin (tapeLength R C),F < i.val → V i.val=none at fresh
  have hH : L+n+1=S+z+n+3:=by dsimp only [L];omega
  change L+n+1+2^n+1 < F at arena
  have room : L+n+1 < F:=lt_of_le_of_lt (Nat.le_add_right (L+n+1) (2^n+1)) (by simpa only [Nat.add_assoc] using arena)
  have same (i : Nat) (hi : i ≤ P) : T i=Y i:=maskedLow Y (tapeLength R C) i (lt_of_le_of_lt hi oldFit)
  have maskedFrame:=protect fr (by intro i _lo hi;exact same i (by dsimp only [P];omega))
  have clean (i : Nat) (lo : F < i) (hi : i ≤ P) : V i=none:=fresh ⟨i,lt_of_le_of_lt hi oldFit⟩ lo
  obtain ⟨blank,occupied⟩:=banks V L n F r room clean
  let Vm:=masked V (tapeLength R C)
  have vmSame (i : Nat) (hi : i ≤ P) : Vm i=V i:=maskedLow V (tapeLength R C) i (lt_of_le_of_lt hi oldFit)
  have prepared:=preparedSeed L n (2^n) F r Vm pos fits (Nat.two_pow_pos n) (by omega)
    ((vmSame L (by dsimp only [P];omega)).trans (cell_sep cells))
    ((vmSame (L+n+1) (by dsimp only [P];omega)).trans (by rw [hH];exact cell_right cells))
    (by intro i lo hi;exact (vmSame i (by dsimp only [P];omega)).trans (cell_marks cells i (by omega) (by omega)))
    (by intro i lo hi;exact (vmSame i (by dsimp only [P];omega)).trans (cell_gap cells i (by omega) hi))
    ((vmSame F (by dsimp only [P];omega)).trans (cell_fence cells))
    (by intro i lo hi;exact (vmSame i hi).trans (clean i lo hi))
  have fullEq:=maskFull V L n F r (tapeLength R C) room oldFit
  refine ⟨maskedFrame,pos,oldFit,?_,?_,?_,?_⟩
  · intro j hj
    rw [same _ (by interval_cases j <;> dsimp only [SerializedBody.delimiter,P] <;> omega)]
    exact blank j hj
  · intro j hj i lo hi
    rw [same i (by interval_cases j <;> dsimp only [SerializedBody.delimiter,P] at hi ⊢ <;> omega)]
    exact occupied j hj i lo hi
  · rw [same _ (by dsimp only [P];omega)]
    exact seedEmpty L n F r (SuffixCap.Target.image V F r) room pos
  · change PowerFrame (AllArityBitLength.Target.seedImage
      (masked (RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) (tapeLength R C)) F r n) L n (2^n) F r
    rw [fullEq]
    exact prepared
#print axioms actual
end VirtualFinalClosure.InitialWeightFrame
