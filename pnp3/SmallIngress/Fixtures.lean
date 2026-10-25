import Stream.Kernel
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionNonVacuity
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds
#eval do
  let codec := treeCircuitWitnessCodec (thresholdPoly 0)
  for n in [0,1,2,3] do
    for b in [false,true] do
      let x := zeroPrefixQueryValue codec n (fun _ => b)
      let code := [false,false,true,b]
      let w : Bitstring (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1) :=
        fun i => code[i.val]?.getD false
      let showBits := fun bits : List Bool => String.mk (bits.map (fun (v : Bool) => if v then '1' else '0'))
      IO.println s!"canonical|{n}|{b}|{showBits (List.ofFn x)}|{showBits (List.ofFn w)}|{PartAEndpoint.thresholdContentWitnessRelation 0 _ _ x w}"
      let mismatch := zeroPrefixQueryValue codec n (fun _ => !b)
      IO.println s!"mismatch|{n}|{b}|{PartAEndpoint.thresholdContentWitnessRelation 0 _ _ mismatch w}"

namespace SmallIngress.Fixtures
set_option maxHeartbeats 2000000
/-- Symbolic canonical witnesses; this is not a kernel reduction of the literal trace words. -/
theorem canonical_nonvacuity (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n.val) 1),
      PartAEndpoint.thresholdContentWitnessRelation k _ _ x w=true := by
  have size : 1 ≤ thresholdPoly k n.val := by
    unfold thresholdPoly
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k; simp
    · omega
  have pred : treeMCSPPredicate n.val (thresholdPoly k n.val)
      (fun _ : Fin (Pnp3.Models.Partial.tableLen n.val) => b) :=
    ⟨Pnp3.Models.Circuit.const b,
      by simpa [treeCircuitClass,Pnp3.Models.Circuit.size] using size,by intro _; rfl⟩
  obtain ⟨w,hw⟩ := contentAccepts_zeroPrefixQuery_of_predicate
    (treeCircuitWitnessCodec (thresholdPoly k)) n.val (fun _ => b) pred
  refine ⟨w,?_⟩
  unfold PartAEndpoint.thresholdContentWitnessRelation
  rw [PartAEndpoint.contentWitnessRelation_at_certificateLength_concatBitstring]
  exact (contentSemanticAccepts_eq_true_iff _ _).2 hw
theorem check_canonical_nonvacuity (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n.val) 1),
      PartAEndpoint.thresholdContentWitnessRelation k _ _ x w=true := @canonical_nonvacuity k n b
end SmallIngress.Fixtures
#print axioms SmallIngress.Fixtures.canonical_nonvacuity
#print axioms SmallIngress.Fixtures.check_canonical_nonvacuity
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "SmallIngress.Fixtures." then logInfo m!"surface|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
