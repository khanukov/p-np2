import ConnectedRead.Closure
import Tests.PartACanonicalSupport

/-! Infrastructure: literal G1/G2 interfaces. All original binders, guards,
whole Config, clocks and conclusions are retained. Original proofs are reused;
these declarations are not independently authored correctness proofs. -/
namespace PartACanonical.G2
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option autoImplicit false

#check (GammaSupport.Exact : Prop)
#check (ConnectedRead.Exact : Nat → Prop)
#check (InputRead.Target.PartA : (Nat → UniformTM) → (Nat → Nat) → Prop)
#check (PartACanonical.privateNameFromString : String → Lean.Name)
#check (PartACanonical.elaboratePrivateABI : Lean.Elab.Term.TermElab)

theorem gammaSupport_canonical_mirror (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (accepted : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true)
    (hn : 3 ≤ pr.2.n) : tagLen + gammaLen pr.2.n ≤ N := by
  exact GammaSupport.canonical k z parsed accepted hn

theorem gammaSupport_exact_mirror :
∀ (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr →
    contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = true →
    3 ≤ pr.2.n → ∀ g,
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some g →
    9+2*g ≤ a+m := by
  exact GammaSupport.exact

theorem connectedRead_exact_mirror (k : Nat) :
∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w = true →
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ (z T : Nat)
        (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m)
          (FixedRawLengthFence.allocation (pairLength a m))) (mode : Fin 3),
        2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        9+2*z ≤ a+m ∧
        T+pr.2.n+2+InputRead.readClock pr.2.n z (a+m-(9+2*z)) ≤ 144*(pairLength a m+1)^2 ∧
        (mode.val=2 ↔ 9+2*z=a+m) ∧
        (∀ hi : 9+2*z < a+m, InputRead.result mode=Fin.append x w ⟨9+2*z,hi⟩) ∧
        InputRead.rawMachine.run (T+pr.2.n+2+InputRead.readClock pr.2.n z (a+m-(9+2*z)))
          (initialConfig InputRead.rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
          FixedRawLengthFence.prefixed.seqEmbedRight InputRead.machine
            ⟨InputRead.ready mode,⟨a+m+2+z+pr.2.n+1,hR⟩,
              fun i => if i.val=9+2*z then none else
                Body.installedTape (FixedRawLengthFence.countdownTape
                  (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n)
                  (a+m+2+z) pr.2.n i⟩) := by
  exact ConnectedRead.exact k

/-- Definitional body of InputRead.Target.PartA only. This is neither an inhabitant
of that interface nor a theorem relating its distinct constant to Body.Target.PartA;
the byte-identical interface definitions do not by themselves supply either proof. -/
theorem inputRead_partA_body_contract
    (M : Nat → UniformTM) (e : Nat → Nat) :
    InputRead.Target.PartA M e ↔
      (∀ k, VerifiesRelation (M k) (e k)
        (Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation k)) := by
  rfl

#print axioms GammaSupport.canonical
#print axioms GammaSupport.exact
#print axioms ConnectedRead.exact
#print axioms gammaSupport_canonical_mirror
#print axioms gammaSupport_exact_mirror
#print axioms connectedRead_exact_mirror
#print axioms InputRead.Target.PartA
#print axioms inputRead_partA_body_contract
#print axioms PartACanonical.privateNameFromString
#print axioms PartACanonical.elaboratePrivateABI
end PartACanonical.G2
