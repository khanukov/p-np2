import NormalFinalClosure.Target
import Pnp4.Frontier.ContractExpansion.ContentParseFieldRecovery
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds
/-- Original query/certificate guard and source concatenation, with no retargeting
of the internal witness window to the external certificate. -/
theorem rho_append (k a m : Nat) (x : Bitstring a) (w : Bitstring m) (length:m=a+1) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=
      contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) := by
  have canonical:m=Pnp3.ComplexityInterfaces.certificateLength a 1 := by
    simpa [Pnp3.ComplexityInterfaces.certificateLength] using length
  clear length
  subst m
  rw [PartAEndpoint.thresholdContentWitnessRelation,PartAEndpoint.contentWitnessRelation_at_certificateLength]
  apply congrArg (contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)))
  funext i
  by_cases h:i.val < a
  · simp [PartAEndpoint.concatV1ToPrefixBitVec,Fin.append,Fin.addCases,h]
    apply congrArg x
    apply Fin.ext
    rfl
  · simp [PartAEndpoint.concatV1ToPrefixBitVec,Fin.append,Fin.addCases,h]
    apply congrArg w
    apply Fin.ext
    rfl
theorem rho_append_mirror (k a m : Nat) (x : Bitstring a) (w : Bitstring m) (length:m=a+1) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=
      contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) :=
  rho_append k a m x w length
#print axioms rho_append
#print axioms rho_append_mirror
private theorem computes_rows {S n A : Nat} (source : Fin S → Bool) (c : Pnp3.Models.Circuit n) :
    ComputesTruthTable treeCircuitClass c (fun j=>padRead source (A+j.val)) ↔
      ∀ j,j < 2^n → padRead source (A+j)=Pnp3.Models.Circuit.eval c (Pnp3.Core.vecOfNat n j) := by
  constructor
  · intro h j hj
    have eq:=h (Pnp3.Core.vecOfNat n j)
    change Pnp3.Models.Circuit.eval c (Pnp3.Core.vecOfNat n j)=
      padRead source (A+(Pnp3.Models.bitVecToNat (Pnp3.Core.vecOfNat n j))%(2^n)) at eq
    rw [Pnp3.Models.bitVecToNat_vecOfNat hj,Nat.mod_eq_of_lt hj] at eq
    exact eq.symm
  · intro h beta
    have ltIndex:(Pnp3.Models.assignmentIndex beta).val < 2^n:=(Pnp3.Models.assignmentIndex beta).isLt
    have eq:=h _ ltIndex
    rw [Pnp3.Models.vecOfNat_assignmentIndex_val] at eq
    exact eq.symm
/-- Exact logical bridge for the already physical all-row result. The arbitrary
ignored decoder tail remains quantified; no zero-padding of that tail is imposed. -/
theorem codec_rows (threshold : Nat → Nat) {S : Nat} (source : Fin S → Bool) (A n : Nat)
    (w : Fin ((treeCircuitWitnessCodec threshold).witnessBits n) → Bool) :
    (treeCircuitWitnessCodec threshold).verifies n (fun j=>padRead source (A+j.val)) w ↔
      ∃ (c : Pnp3.Models.Circuit n) (tail : List Bool),
        decodeCircuitFull n (bitLength n) (List.ofFn w)=some (c,tail) ∧
        c.size ≤ threshold n ∧
        ∀ j,j < 2^n → padRead source (A+j)=Pnp3.Models.Circuit.eval c (Pnp3.Core.vecOfNat n j) := by
  constructor
  · rintro ⟨c,decoded,size,table⟩
    change Option.map Prod.fst (decodeCircuitFull n (bitLength n) (List.ofFn w))=some c at decoded
    cases hc:decodeCircuitFull n (bitLength n) (List.ofFn w) with
    | none=>simp only [hc,Option.map_none] at decoded;cases decoded
    | some pair=>
      rcases pair with ⟨c',tail⟩
      simp only [hc,Option.map_some] at decoded
      have same:c'=c:=Option.some.inj decoded
      subst c'
      exact ⟨c,tail,rfl,size,(computes_rows source c).mp table⟩
  · rintro ⟨c,tail,decoded,size,table⟩
    refine ⟨c,?_,size,(computes_rows source c).mpr table⟩
    change Option.map Prod.fst (decodeCircuitFull n (bitLength n) (List.ofFn w))=some c
    rw [decoded]
    rfl
/-- Independent complete proposition mirror, including the original decoder,
canonical assignment orientation and unconstrained remaining tail. -/
theorem codec_rows_mirror (threshold : Nat → Nat) {S : Nat} (source : Fin S → Bool) (A n : Nat)
    (w : Fin ((treeCircuitWitnessCodec threshold).witnessBits n) → Bool) :
    (treeCircuitWitnessCodec threshold).verifies n (fun j=>padRead source (A+j.val)) w ↔
      ∃ (c : Pnp3.Models.Circuit n) (tail : List Bool),
        decodeCircuitFull n (bitLength n) (List.ofFn w)=some (c,tail) ∧
        c.size ≤ threshold n ∧
        ∀ j,j < 2^n → padRead source (A+j)=Pnp3.Models.Circuit.eval c (Pnp3.Core.vecOfNat n j) :=
  codec_rows threshold source A n w
#print axioms codec_rows
#print axioms codec_rows_mirror
/-- Original content acceptance forces the exact decoder/size/ALL canonical-row
facts used by the sealed physical caller. No valid AST premise is added. -/
theorem accepted_content_rows (k n z : Nat) {S : Nat} (source : Fin S → Bool)
    (header:contentHeader? source=some (n,2*z+1))
    (accepted:contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) source=true) :
    ∃ (c : Pnp3.Models.Circuit n) (tail : List Bool),
      decodeCircuitFull n (bitLength n) (SerializedBody.window source (Cursor.Target.M k n z) (Cursor.Target.W k n))=some (c,tail) ∧
      c.size≤n^k+k ∧ ∀ j,j < 2^n → padRead source (9+2*z+j)=Pnp3.Models.Circuit.eval c (Pnp3.Core.vecOfNat n j) := by
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  obtain ⟨pr,input,_prefix,verify⟩:=(contentSemanticAccepts_eq_true_iff codec source).mp accepted
  unfold contentInput? at input
  rw [header] at input
  cases hp:parseTreeMCSPPrefixInput (thresholdPoly k) codec (padWord source (treeMCSPPrefixM codec n)) with
  | none=>simp only [hp,Option.map_none] at input;cases input
  | some parsed=>
    simp only [hp,Option.map_some] at input
    have same:=Option.some.inj input
    subst pr
    rcases parsed with ⟨tag,q,table,i,bound,prefBits,padBits,pad⟩
    obtain ⟨cg,narrow,tableSlice⟩:=parseTreeMCSPPrefixInput_x_slice codec
      (padWord source (treeMCSPPrefixM codec n)) _ hp
    have canonical:=decodeGamma?_padWord_narrow source codec header
    have pairs:(q,cg)=(n,2*z+1):=Option.some.inj (narrow.symm.trans canonical)
    have qEq:q=n:=congrArg Prod.fst pairs
    subst q
    have cgEq:cg=2*z+1:=congrArg Prod.snd pairs
    subst cg
    have tableEq:table=(fun j=>padRead source (9+2*z+j.val)) := by
      unfold sliceBits? at tableSlice
      split at tableSlice
      · have eq:=Option.some.inj tableSlice
        funext j
        have val:=congrFun eq j
        change padRead source (tagLen+(2*z+1)+j.val)=table j at val
        rw [show tagLen+(2*z+1)+j.val=9+2*z+j.val by unfold tagLen;omega] at val
        exact val.symm
      · cases tableSlice
    change codec.verifies n table (contentWitness codec source n) at verify
    rw [tableEq] at verify
    obtain ⟨c,tail,decoded,size,rows⟩:=(codec_rows (thresholdPoly k) source (9+2*z) n
      (contentWitness codec source n)).mp verify
    have consumed:=contentHeader?_consumed_eq_gammaLen source header
    have address:treeMCSPPrefixM codec n=Cursor.Target.M k n z := by
      dsimp only [treeMCSPPrefixM,idxWidth]
      rw [←consumed]
      change tagLen+(2*z+1)+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n=Cursor.Target.M k n z
      unfold tagLen Cursor.Target.M
      omega
    have bits:List.ofFn (contentWitness codec source n)=
        SerializedBody.window source (Cursor.Target.M k n z) (Cursor.Target.W k n) := by
      change List.ofFn (fun j : Fin (Cursor.Target.W k n)=>padRead source (treeMCSPPrefixM codec n+j.val))=
        List.ofFn (fun j : Fin (Cursor.Target.W k n)=>padRead source (Cursor.Target.M k n z+j.val))
      rw [address]
    rw [bits] at decoded
    exact ⟨c,tail,decoded,size,rows⟩
/-- Independently complete acceptance-to-original-decoder/table proposition. -/
theorem accepted_content_rows_mirror (k n z : Nat) {S : Nat} (source : Fin S → Bool)
    (header:contentHeader? source=some (n,2*z+1))
    (accepted:contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) source=true) :
    ∃ (c : Pnp3.Models.Circuit n) (tail : List Bool),
      decodeCircuitFull n (bitLength n) (SerializedBody.window source (Cursor.Target.M k n z) (Cursor.Target.W k n))=some (c,tail) ∧
      c.size≤n^k+k ∧ ∀ j,j < 2^n → padRead source (9+2*z+j)=Pnp3.Models.Circuit.eval c (Pnp3.Core.vecOfNat n j) :=
  accepted_content_rows k n z source header accepted
#print axioms accepted_content_rows
#print axioms accepted_content_rows_mirror
end NormalFinalClosure
