import VirtualLeaf.Transport
namespace VirtualLeaf
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds Pnp3.Internal.PsubsetPpoly.TM.Encoding
set_option maxRecDepth 10000
private theorem encode_zero (width : Nat) :
    encodeFin width ⟨0,by positivity⟩=List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [encodeFin,Nat.zero_mod,Nat.zero_div,ih,List.replicate_succ]; rfl
/-- Authoritative original codec/decoder: strict finite window and exact ignored tail. -/
theorem decode_leaf (k n : Nat) (beta : Fin n → Bool) :
    bitLength n+4≤Cursor.Target.W k n ∧
    (n=0 → (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=none) ∧
    ∀ positive : 0<n,
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
      decodeCircuitFull n (bitLength n) (List.replicate (Cursor.Target.W k n) false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩,
          List.replicate (Cursor.Target.W k n-(3+bitLength n)) false) ∧
      Pnp3.Models.Circuit.size (Pnp3.Models.Circuit.input ⟨0,positive⟩)=1 ∧
      Pnp3.Models.Circuit.eval (Pnp3.Models.Circuit.input ⟨0,positive⟩) beta=beta ⟨0,positive⟩ := by
  have pos : 1≤n^k+k := by cases k with | zero => simp | succ k => omega
  have cover : bitLength n+4≤Cursor.Target.W k n := by dsimp only [Cursor.Target.W]; nlinarith only [pos]
  refine ⟨cover,?_,?_⟩
  · intro zero; subst n; exact treeCircuitWitnessCodec_decode_blank_zero k
  · intro positive
    refine ⟨treeCircuitWitnessCodec_decode_blank_pos k positive,?_,rfl,rfl⟩
    let width:=bitLength n
    let hwidth:=Nat.le_of_lt (nat_lt_two_pow_bitLength n)
    have enc : encodeCircuit width hwidth (Pnp3.Models.Circuit.input ⟨0,positive⟩)=
        List.replicate (3+width) false := by
      dsimp only [encodeCircuit,toTree,encodeCircuitTree]
      rw [encode_zero, List.replicate_add]; rfl
    have bits : List.replicate (Cursor.Target.W k n) false=
        encodeCircuit width hwidth (Pnp3.Models.Circuit.input ⟨0,positive⟩) ++
          List.replicate (Cursor.Target.W k n-(3+width)) false := by
      rw [enc,←List.replicate_add]; congr 1; omega
    rw [bits,decodeCircuitFull_encodeCircuit]
private theorem offset {k a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n=Cursor.Target.M k pr.2.n z := by
  obtain ⟨consumed,header,target⟩:=contentInput?_target_eq_contentHeader _ _ parsed
  rw [←target] at header
  have width:=(countdown_width_eq_gammaZeros x w header gamma).1
  have len:=gammaLen_eq_two_mul_gammaZeros_add_one pr.2.n
  rw [←width] at len
  dsimp only [treeMCSPPrefixM,Cursor.Target.M,idxWidth,tagLen]
  change 8+gammaLen pr.2.n+2^pr.2.n+bitLength (Cursor.Target.W k pr.2.n)+Cursor.Target.W k pr.2.n=_
  omega
private theorem virtual_source {k a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (beyond : a+m≤Cursor.Target.M k pr.2.n z) :
    0<pr.2.n ∧ ∀ j : Fin (Cursor.Target.W k pr.2.n),
      padRead (Fin.append x w) (Cursor.Target.M k pr.2.n z+j.val)=false := by
  have zeros (j : Nat) : padRead (Fin.append x w) (Cursor.Target.M k pr.2.n z+j)=false := padRead_ge _ (by omega)
  refine ⟨?_,fun j => zeros j.val⟩
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
    have h:=accepted
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
    split at h
    · rename_i shape; cases shape; simpa only [AcceptedBody.concat_eq_append] using h
    · contradiction
  obtain ⟨pr',hpr,_prefix,relation⟩:=(contentSemanticAccepts_eq_true_iff _ _).1 semantic
  have same : pr'=pr := Option.some.inj (hpr.symm.trans parsed)
  cases same
  have blank : contentWitness (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) pr.2.n=(fun _ => false) := by
    funext j; dsimp only [contentWitness]; rw [offset x w parsed z gamma]; exact zeros j.val
  change (treeCircuitWitnessCodec (thresholdPoly k)).verifies _ _ _ at relation
  obtain ⟨c,decoded,_size,_computes⟩:=relation
  by_contra neg
  have eq : pr.2.n=0 := by omega
  have empty : (treeCircuitWitnessCodec (thresholdPoly k)).decode pr.2.n (fun _ => false)=none := by
    rw [eq]; exact treeCircuitWitnessCodec_decode_blank_zero k
  rw [blank,empty] at decoded
  cases decoded
end VirtualLeaf
