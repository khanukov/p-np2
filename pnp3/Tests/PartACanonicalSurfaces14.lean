import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for Stream.raw_accepted.
noncomputable def PartACanonical.Types.p0818 :
(∀ (_v0 : (@Nat)),
(@Stream.RawTarget.AcceptedOrbit _v0)) := by
  exact @Stream.raw_accepted

-- Complete literal proposition for Stream.raw_accepted; original proof reused.
theorem PartACanonical.Surface.m0484 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(@Exists.{(0 + 1)} (@AcceptedBody.Parsed _v0) (fun (_v6 : (@AcceptedBody.Parsed _v0)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v6)) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Partial.tableLen
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 :
  Nat) (@instOfNatNat (3 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))) _v6)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v8)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2048 : Nat) (@instOfNatNat (2048 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v11 : (∀ (_v11 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v8 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v8) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))));
(@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 _v9) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v11 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v12) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v8)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v10) (fun (_v15 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v8
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v15))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v9 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) _v12) (fun (_v13 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v8
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v13))))))))))))))))))))))))))))) := by
  exact @Stream.raw_accepted

-- Independent literal expected type for Stream.raw_body.
noncomputable def PartACanonical.Types.p0819 :
(∀ (_v0 : (@Nat)),
(@Stream.BodyTarget.Orbit _v0)) := by
  exact @Stream.raw_body

-- Complete literal proposition for Stream.raw_body; original proof reused.
theorem PartACanonical.Surface.m0485 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ {_v5 : (@AcceptedBody.Parsed _v0)},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v5))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.true))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v5)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v9)) (∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v5))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v9))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2048 : Nat) (@instOfNatNat (2048 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (let _v14 : (∀ (_v14 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5))));
(let _v15 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v16 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))));
(@And (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5))) _v16))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v19 _v12) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v19 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v14 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v20))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v20))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v13) (fun (_v20 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v21))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v21))) _v5)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v20))))))))))) (@ite.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) _v16) (@Nat.decLe (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) _v16) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)))) _v17) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v18)))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v15 _v17) (fun (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v16 _v16 (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v18))))))))))))))))))))))))))))))))) := by
  exact @Stream.raw_body

-- Independent literal expected type for Stream.raw_budget_cells.
noncomputable def PartACanonical.Types.p0820 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v2))),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v0 _v1 _v2))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@And (∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v8))),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v8) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v4 _v5 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3 _v8) (@Option.none.{0} (@Bool)))))) (@Exists.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))) (fun (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))))) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v4 _v5 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1)) _v8)) (@Option.some.{0} (@Bool) (@Bool.false))))))))))))))) := by
  exact @Stream.raw_budget_cells

-- Complete literal proposition for Stream.raw_budget_cells; original proof reused.
theorem PartACanonical.Surface.m0486 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v2))),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v0 _v1 _v2))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@And (∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v8))),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v8) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v4 _v5 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3 _v8) (@Option.none.{0} (@Bool)))))) (@Exists.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))) (fun (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))))) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v4 _v5 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1)) _v8)) (@Option.some.{0} (@Bool) (@Bool.false))))))))))))))) := by
  exact @Stream.raw_budget_cells

-- Independent literal expected type for Stream.rows.
noncomputable def PartACanonical.Types.p0821 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))) := by
  exact @Stream.rows

-- Independent literal expected type for Stream.rows.eq_1.
noncomputable def PartACanonical.Types.p0822 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_1

-- Complete literal proposition for Stream.rows.eq_1; original proof reused.
theorem PartACanonical.Surface.m0487 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_1

-- Independent literal expected type for Stream.rows.eq_10.
noncomputable def PartACanonical.Types.p0823 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))))) := by
  exact @Stream.rows.eq_10

-- Complete literal proposition for Stream.rows.eq_10; original proof reused.
theorem PartACanonical.Surface.m0488 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))))) := by
  exact @Stream.rows.eq_10

-- Independent literal expected type for Stream.rows.eq_11.
noncomputable def PartACanonical.Types.p0824 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 _v1) (@Prod.mk.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v1
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))))) := by
  exact @Stream.rows.eq_11

-- Complete literal proposition for Stream.rows.eq_11; original proof reused.
theorem PartACanonical.Surface.m0489 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 _v1) (@Prod.mk.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v1
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))))) := by
  exact @Stream.rows.eq_11

-- Independent literal expected type for Stream.rows.eq_12.
noncomputable def PartACanonical.Types.p0825 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 _v1) (@Prod.mk.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v1
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))))) := by
  exact @Stream.rows.eq_12

-- Complete literal proposition for Stream.rows.eq_12; original proof reused.
theorem PartACanonical.Surface.m0490 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 _v1) (@Prod.mk.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v1
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))))) := by
  exact @Stream.rows.eq_12

-- Independent literal expected type for Stream.rows.eq_13.
noncomputable def PartACanonical.Types.p0826 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(∀ (_v2 : (∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))),
(@False))),
(∀ (_v3 : (∀ (_v3 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))),
(@False))),
(∀ (_v4 : (∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v5 : (∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (19 : Nat) (@instOfNatNat (19 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v6 : (∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (27 : Nat) (@instOfNatNat (27 : Nat))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v7 : (∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (37 : Nat) (@instOfNatNat (37 : Nat))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v8 : (∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (38 : Nat) (@instOfNatNat (38 : Nat))))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v9 : (∀ (_v9 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (28 : Nat) (@instOfNatNat (28 : Nat))))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v10 : (∀ (_v10 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.some.{0} (@Bool) (@Bool.false)))),
(@False)))),
(∀ (_v11 : (∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v12 : (∀ (_v12 : (@Bool)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.some.{0} (@Bool) _v12))),
(@False))))),
(∀ (_v13 : (∀ (_v13 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 _v1) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (53 : Nat) (@instOfNatNat (53 : Nat))))) (@instDecidableAnd (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (53 : Nat) (@instOfNatNat (53 : Nat)))) (@Nat.decLe (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)) (@Nat.decLt
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (53 : Nat)
  (@instOfNatNat (53 : Nat))))) (let _v14 : (@Nat) := (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat)
  (@Nat.instDiv)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat
  (41 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))));
(let _v15 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v14));
(@Stream.rows.match_1.{(0 + 1)} (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Option.{0} (@Bool))) =>
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 :
  Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v1 (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q _v15) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.right))))
  (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (fun
  (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v14)))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Option.{0} (@Bool))) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (40 : Nat) (@instOfNatNat (40 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v17
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))))))) (let _v14 : (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) :=
  (@InputRead.rows (@InputRead.q (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)) _v1);
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@Fin.val (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41
  : Nat))) (@Prod.fst.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v14))) (@Prod.snd.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 :
  Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  _v14))))))))))))))))))) := by
  exact @Stream.rows.eq_13

-- Complete literal proposition for Stream.rows.eq_13; original proof reused.
theorem PartACanonical.Surface.m0491 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(∀ (_v2 : (∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))),
(@False))),
(∀ (_v3 : (∀ (_v3 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))),
(@False))),
(∀ (_v4 : (∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v5 : (∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (19 : Nat) (@instOfNatNat (19 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v6 : (∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (27 : Nat) (@instOfNatNat (27 : Nat))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v7 : (∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (37 : Nat) (@instOfNatNat (37 : Nat))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v8 : (∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (38 : Nat) (@instOfNatNat (38 : Nat))))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v9 : (∀ (_v9 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (28 : Nat) (@instOfNatNat (28 : Nat))))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v10 : (∀ (_v10 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.some.{0} (@Bool) (@Bool.false)))),
(@False)))),
(∀ (_v11 : (∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(∀ (_v12 : (∀ (_v12 : (@Bool)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.some.{0} (@Bool) _v12))),
(@False))))),
(∀ (_v13 : (∀ (_v13 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v1 (@Option.none.{0} (@Bool)))),
(@False)))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 _v1) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (53 : Nat) (@instOfNatNat (53 : Nat))))) (@instDecidableAnd (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))
  _v0)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (53 : Nat) (@instOfNatNat (53 : Nat)))) (@Nat.decLe (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)) (@Nat.decLt
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (53 : Nat)
  (@instOfNatNat (53 : Nat))))) (let _v14 : (@Nat) := (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat)
  (@Nat.instDiv)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat
  (41 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))));
(let _v15 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v14));
(@Stream.rows.match_1.{(0 + 1)} (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Option.{0} (@Bool))) =>
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 :
  Nat) (@instOfNatNat (64 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v1 (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q _v15) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.right))))
  (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (fun (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (fun
  (_v16 : (@Unit)) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v14)))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Option.{0} (@Bool))) =>
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (40 : Nat) (@instOfNatNat (40 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v17
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))))))) (let _v14 : (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) :=
  (@InputRead.rows (@InputRead.q (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)) _v1);
(@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@Fin.val (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41
  : Nat))) (@Prod.fst.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v14))) (@Prod.snd.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 :
  Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  _v14))))))))))))))))))) := by
  exact @Stream.rows.eq_13

-- Independent literal expected type for Stream.rows.eq_2.
noncomputable def PartACanonical.Types.p0827 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (19 : Nat) (@instOfNatNat (19 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (45 : Nat) (@instOfNatNat (45 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_2

-- Complete literal proposition for Stream.rows.eq_2; original proof reused.
theorem PartACanonical.Surface.m0492 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (19 : Nat) (@instOfNatNat (19 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (45 : Nat) (@instOfNatNat (45 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_2

-- Independent literal expected type for Stream.rows.eq_3.
noncomputable def PartACanonical.Types.p0828 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (27 : Nat) (@instOfNatNat (27 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (49 : Nat) (@instOfNatNat (49 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_3

-- Complete literal proposition for Stream.rows.eq_3; original proof reused.
theorem PartACanonical.Surface.m0493 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (27 : Nat) (@instOfNatNat (27 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (49 : Nat) (@instOfNatNat (49 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_3

-- Independent literal expected type for Stream.rows.eq_4.
noncomputable def PartACanonical.Types.p0829 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (37 : Nat) (@instOfNatNat (37 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.false))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_4

-- Complete literal proposition for Stream.rows.eq_4; original proof reused.
theorem PartACanonical.Surface.m0494 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (37 : Nat) (@instOfNatNat (37 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.false))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_4

-- Independent literal expected type for Stream.rows.eq_5.
noncomputable def PartACanonical.Types.p0830 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (38 : Nat) (@instOfNatNat (38 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_5

-- Complete literal proposition for Stream.rows.eq_5; original proof reused.
theorem PartACanonical.Surface.m0495 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (38 : Nat) (@instOfNatNat (38 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))) := by
  exact @Stream.rows.eq_5

-- Independent literal expected type for Stream.rows.eq_6.
noncomputable def PartACanonical.Types.p0831 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (28 : Nat) (@instOfNatNat (28 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))))) := by
  exact @Stream.rows.eq_6

-- Complete literal proposition for Stream.rows.eq_6; original proof reused.
theorem PartACanonical.Surface.m0496 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (28 : Nat) (@instOfNatNat (28 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))))) := by
  exact @Stream.rows.eq_6

-- Independent literal expected type for Stream.rows.eq_7.
noncomputable def PartACanonical.Types.p0832 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.some.{0} (@Bool) (@Bool.false)))
  (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.false))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))))) := by
  exact @Stream.rows.eq_7

-- Complete literal proposition for Stream.rows.eq_7; original proof reused.
theorem PartACanonical.Surface.m0497 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.some.{0} (@Bool) (@Bool.false)))
  (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) (@Bool.false))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))))) := by
  exact @Stream.rows.eq_7

-- Independent literal expected type for Stream.rows.eq_8.
noncomputable def PartACanonical.Types.p0833 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))))) := by
  exact @Stream.rows.eq_8

-- Complete literal proposition for Stream.rows.eq_8; original proof reused.
theorem PartACanonical.Surface.m0498 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (54 : Nat) (@instOfNatNat (54 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.none.{0} (@Bool))) (@Prod.mk.{0,
  0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))))) := by
  exact @Stream.rows.eq_8

-- Independent literal expected type for Stream.rows.eq_9.
noncomputable def PartACanonical.Types.p0834 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Bool)),
(∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.some.{0} (@Bool) _v1))
  (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1)
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))))) := by
  exact @Stream.rows.eq_9

-- Complete literal proposition for Stream.rows.eq_9; original proof reused.
theorem PartACanonical.Surface.m0499 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Bool)),
(∀ (_v2 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (56 : Nat) (@instOfNatNat (56 : Nat))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Stream.rows _v0 (@Option.some.{0} (@Bool) _v1))
  (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1)
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))))) := by
  exact @Stream.rows.eq_9

-- Independent literal expected type for Stream.unpaid.
noncomputable def PartACanonical.Types.p0835 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) := by
  exact @Stream.unpaid

-- Independent literal expected type for SuffixCap.Target.Raw.
noncomputable def PartACanonical.Types.p0836 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SuffixCap.Target.Raw

-- Independent literal expected type for SuffixCap.Target.deadline.
noncomputable def PartACanonical.Types.p0837 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @SuffixCap.Target.deadline

-- Independent literal expected type for SuffixCap.Target.image.
noncomputable def PartACanonical.Types.p0838 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @SuffixCap.Target.image

-- Independent literal expected type for SuffixCap.Target.image.eq_1.
noncomputable def PartACanonical.Types.p0839 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SuffixCap.Target.image _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v1 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))
  (@instDecidableAnd (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat)
  _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@Nat.decLt _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@_v0
  _v3))))))) := by
  exact @SuffixCap.Target.image.eq_1

-- Complete literal proposition for SuffixCap.Target.image.eq_1; original proof reused.
theorem PartACanonical.Surface.m0500 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SuffixCap.Target.image _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v1 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))
  (@instDecidableAnd (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat)
  _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@Nat.decLt _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@_v0
  _v3))))))) := by
  exact @SuffixCap.Target.image.eq_1

-- Independent literal expected type for SuffixCap.count_rows.
noncomputable def PartACanonical.Types.p0840 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Bool)),
(@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0, 0} (@Fin
  (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v2)
  (@Pnp3.Complexity.Uniform.V1.Move.right))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1
  (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat)
  (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Prod.mk.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0, 0}
  (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0}
  (@Bool) _v2) (@Pnp3.Complexity.Uniform.V1.Move.right))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0,
  0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q
  _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 +
  1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat
  (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.some.{0} (@Bool) _v2) (@Pnp3.Complexity.Uniform.V1.Move.left))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0,
  0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q
  _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 +
  1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat
  (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.some.{0} (@Bool) _v2) (@Pnp3.Complexity.Uniform.V1.Move.left))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1)
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat)
  (@instOfNatNat (14 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.rReady _v0) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (∀ (_v2 :
  (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0,
  0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q
  _v0 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v2 (@Bool.true)) (@instDecidableEqBool _v2 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))))))))))))))))))))))))))))))) := by
  exact @SuffixCap.count_rows

-- Complete literal proposition for SuffixCap.count_rows; original proof reused.
theorem PartACanonical.Surface.m0501 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Bool)),
(@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0, 0} (@Fin
  (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v2)
  (@Pnp3.Complexity.Uniform.V1.Move.right))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1
  (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat)
  (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Prod.mk.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0, 0}
  (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0}
  (@Bool) _v2) (@Pnp3.Complexity.Uniform.V1.Move.right))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0,
  0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q
  _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 +
  1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat
  (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.some.{0} (@Bool) _v2) (@Pnp3.Complexity.Uniform.V1.Move.left))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left)))) (@And (∀ (_v2 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0,
  0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q
  _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 +
  1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat
  (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.some.{0} (@Bool) _v2) (@Pnp3.Complexity.Uniform.V1.Move.left))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true))
  (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14
  : Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1)
  (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat)
  (@instOfNatNat (14 : Nat))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.rReady _v0) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (∀ (_v2 :
  (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Prod.mk.{0,
  0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q
  _v0 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v2 (@Bool.true)) (@instDecidableEqBool _v2 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right)))))))))))))))))))))))))))))))))) := by
  exact @SuffixCap.count_rows

-- Independent literal expected type for SuffixCap.counted.
noncomputable def PartACanonical.Types.p0841 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7) _v8)),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v14) (@Option.some.{0} (@Bool) _v17)))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v16) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v18)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v21 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v18) (@Option.some.{0} (@Bool) _v21)))))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v20)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v20) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v8)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v21) (@Option.none.{0} (@Bool))))))),
(∀ (_v22 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v8) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4 _v3)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v23) (@Option.none.{0} (@Bool))))))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4 _v3)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v8 _v3)) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v25 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@SuffixCap.counted._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v11 _v12 _v13 _v24 _v25)))) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v25))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.rReady _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v4 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v25 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@SuffixCap.counted._proof_2 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v12 _v13 _v24 _v25)))) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@SuffixCap.Target.image _v9 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4
  _v3) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v25))))) (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4
  _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v3)) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v25 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (58 : Nat) (@instOfNatNat (58 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v27 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@SuffixCap.counted._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v11 _v12 _v13 _v24 _v27)))) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v27)))))) (@Cursor.rReady
  _v0)))))))))))))))))))))))))))))) := by
  exact @SuffixCap.counted

-- Complete literal proposition for SuffixCap.counted; original proof reused.
theorem PartACanonical.Surface.m0502 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7) _v8)),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v14) (@Option.some.{0} (@Bool) _v17)))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v16) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v18)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v21 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v18) (@Option.some.{0} (@Bool) _v21)))))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v20)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v20) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v8)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v21) (@Option.none.{0} (@Bool))))))),
(∀ (_v22 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v8) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4 _v3)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v23) (@Option.none.{0} (@Bool))))))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4 _v3)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v8 _v3)) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v25 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@SuffixCap.counted._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v11 _v12 _v13 _v24 _v25)))) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v25))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.rReady _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v4 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v25 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@SuffixCap.counted._proof_2 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v12 _v13 _v24 _v25)))) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@SuffixCap.Target.image _v9 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4
  _v3) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v25))))) (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v4
  _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v3)) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v25 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (58 : Nat) (@instOfNatNat (58 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v27 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@SuffixCap.counted._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v11 _v12 _v13 _v24 _v27)))) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v27)))))) (@Cursor.rReady
  _v0)))))))))))))))))))))))))))))) := by
  exact @SuffixCap.counted

-- Independent literal expected type for SuffixCap.entry_rows.
noncomputable def PartACanonical.Types.p0842 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Bool)),
(@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))) (@Option.some.{0}
  (@Bool) _v1)) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1)
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Option.some.{0} (@Bool) _v1)) (@Prod.mk.{0, 0} (@Fin
  (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right))))))) := by
  exact @SuffixCap.entry_rows

-- Complete literal proposition for SuffixCap.entry_rows; original proof reused.
theorem PartACanonical.Surface.m0503 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Bool)),
(@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))) (@Option.some.{0}
  (@Bool) _v1)) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1)
  (@Pnp3.Complexity.Uniform.V1.Move.stay)))) (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Option.some.{0} (@Bool) _v1)) (@Prod.mk.{0, 0} (@Fin
  (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v1 (@Bool.true)) (@instDecidableEqBool _v1 (@Bool.true))
  (@OfNat.ofNat.{0} (@Nat) (83 : Nat) (@instOfNatNat (83 : Nat))) (@OfNat.ofNat.{0} (@Nat) (68 : Nat) (@instOfNatNat (68 :
  Nat))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.right))))))) := by
  exact @SuffixCap.entry_rows

-- Independent literal expected type for SuffixCap.raw_accepted_counted.
noncomputable def PartACanonical.Types.p0843 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ {_v6 : (@AcceptedBody.Parsed _v0)},
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v6))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v9)) (∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2)))) (fun (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@SuffixCap.Target.deadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.rReady _v0))))) (let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))));
(let _v14 : (∀ (_v14 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@Bool.false));
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v11 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.rReady _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v12) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@SuffixCap.Target.image _v14 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v15))))))))))))))))))))))))))))) := by
  exact @SuffixCap.raw_accepted_counted

-- Complete literal proposition for SuffixCap.raw_accepted_counted; original proof reused.
theorem PartACanonical.Surface.m0504 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ {_v6 : (@AcceptedBody.Parsed _v0)},
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v6))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v9)) (∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2)))) (fun (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@SuffixCap.Target.deadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.rReady _v0))))) (let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))));
(let _v14 : (∀ (_v14 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@Bool.false));
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v11 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.rReady _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v12) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@SuffixCap.Target.image _v14 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v15))))))))))))))))))))))))))))) := by
  exact @SuffixCap.raw_accepted_counted

-- Independent literal expected type for SuffixCap.raw_counted.
noncomputable def PartACanonical.Types.p0844 :
(∀ (_v0 : (@Nat)),
(@SuffixCap.Target.Raw _v0)) := by
  exact @SuffixCap.raw_counted

-- Complete literal proposition for SuffixCap.raw_counted; original proof reused.
theorem PartACanonical.Surface.m0505 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ {_v5 : (@AcceptedBody.Parsed _v0)},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v5))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.true))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v5)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v9)) (∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v5))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v9))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v5))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2)))) (fun (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@SuffixCap.Target.deadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v14)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.rReady _v0))))) (let _v16 : (∀ (_v16 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5))));
(let _v17 : (∀ (_v17 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) (@Bool.false));
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v18 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.rReady _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v15) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@SuffixCap.Target.image _v17 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v18)))))))))))))))))))))))))))))))) := by
  exact @SuffixCap.raw_counted

-- Independent literal expected type for TotalIngressClosure.Audit.check_raw.
noncomputable def PartACanonical.Types.p0845 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v4 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4 _v2);
(let _v9 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v10)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v11 _v7))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v10)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v5)))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5))
  (@And (∀ (_v13 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v13)))))) (∀ (_v13 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v13))))))))) (@Or (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v10
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v11 : (@Nat)) =>
(fun (_v12 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v11
  _v12))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v11 : (@Nat)) =>
(fun (_v12 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v12))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v11 : (@Nat)) =>
(fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v11 _v12))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v3)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v3))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v11 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v3)) (@Or
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v3)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 _v7))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v11) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v11)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v12) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v12)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v1) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v11 _v13) (@Sigma.mk.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v12 _v14)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) (fun (_v16 :
  (@Nat)) =>
(fun (_v17 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v16)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v11 _v12 _v13 _v14)
  _v1 _v15)) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v16)) (@And (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v17) _v7) (@TotalIngressClosure.config _v0 _v1
  _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v17 _v9)))) (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v4
  _v3) (fun (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v3)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v6) _v1 _v4 _v3 _v17 _v8 _v9) (@And (@IngressAllocation.Footprint _v6 _v1 _v4 _v2 _v16 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@IngressAllocation.MoveRoom _v6 _v1 _v4 _v2 _v16) (@And (@IngressAllocation.Trace _v6 _v1 _v4 _v3 _v17
  _v2 _v16) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v10 _v7) (@TotalIngressClosure.config _v0 _v1 _v3
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v4
  _v3 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4
  _v16 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v11 _v12 _v13 _v14) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v18 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 _v12) _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0}
  (@Nat) _v19)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v21 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12);
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v19) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v24 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v18);
(let _v25 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v24) _v21);
(let _v26 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 _v25);
(let _v27 : (@Nat) := (@Cursor.Target.W _v0 _v18);
(let _v28 : (@Nat) := (@Cursor.Target.M _v0 _v18 _v19);
(let _v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v20);
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v4
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v4 (@SmallIngress.prepared _v11
  _v12 _v4 _v13 _v14 _v19 _v18) _v22 _v18));
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v30 _v21 _v19 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v19)) _v24 _v24 (@Bool.false));
(let _v32 : (∀ (_v32 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v31 _v23 _v26) _v22 _v18 _v23 _v26);
(let _v33 : (∀ (_v33 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v32 _v22 _v18 _v23 _v26);
(let _v34 : (∀ (_v34 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v33 _v23 _v26 _v18);
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v34 _v22 _v18 _v23 _v26
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) _v27 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v23 _v26 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v27)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v27);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v11 _v12 _v19))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v29) _v24) _v23) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v25 _v21) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v26) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v27 _v26) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v23 _v26
  _v18 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))
  (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v35 _v36) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool)
  _v13 _v14 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) _v36
  _v38))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)
  _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12)
  (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) _v28))) _v29 (fun (_v36 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@SerializedBody.prepared _v35 _v21 _v28 _v23 _v26 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v18 _v0) _v0) _v27 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v36))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18) (fun
  (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v21 _v28) (@And (∀ (_v37 : (@Fin _v27)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@Fin.val _v27 _v37))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v18)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18 (fun (_v37 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v18) (@Pnp3.Models.Circuit.input _v18 (@Fin.mk _v18
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v36)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v25 _v21)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v29 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@_v31 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v37))) _v29 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v26
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v26) (@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v40 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@CappedWeight.Target.Cap _v0 _v18 _v26 _v37 _v38 _v39 _v40 _v41))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v29 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@Cursor.Target.image _v31 _v0 _v21 _v18 _v19 _v23 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v37)))
  _v29 (@Option.some.{0} (@Bool)
  (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @TotalIngressClosure.Audit.check_raw

-- Complete literal proposition for TotalIngressClosure.Audit.check_raw; original proof reused.
theorem PartACanonical.Surface.m0506 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v4 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4 _v2);
(let _v9 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v10)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v11 _v7))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v10)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v5)))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5))
  (@And (∀ (_v13 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v13)))))) (∀ (_v13 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v13))))))))) (@Or (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v10
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v11 : (@Nat)) =>
(fun (_v12 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v11
  _v12))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v11 : (@Nat)) =>
(fun (_v12 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v12))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v11 : (@Nat)) =>
(fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v11 _v12))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v3)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v3))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v11 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v3)) (@Or
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v3)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v3))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 _v7))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v11) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v11)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v12) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v12)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v1) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v11 _v13) (@Sigma.mk.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v12 _v14)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) (fun (_v16 :
  (@Nat)) =>
(fun (_v17 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v16)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v11 _v12 _v13 _v14)
  _v1 _v15)) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v16)) (@And (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v17) _v7) (@TotalIngressClosure.config _v0 _v1
  _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v17 _v9)))) (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v4
  _v3) (fun (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v3)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v6) _v1 _v4 _v3 _v17 _v8 _v9) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v16)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4
  _v2)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 :
  Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v16)),
(let _v20 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4
  _v2));
(∀ (_v21 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v6
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20)))))
  (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v16)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1
  _v4 _v3 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6
  _v1 _v4 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6
  _v1 _v3 _v2))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v7) (@TotalIngressClosure.config _v0 _v1 _v3 (@IngressAllocation.extendConfig
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v4 _v3 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4
  _v16 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v11 _v12 _v13 _v14) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v18 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 _v12) _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0}
  (@Nat) _v19)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v21 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12);
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v19) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v24 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v18);
(let _v25 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v24) _v21);
(let _v26 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 _v25);
(let _v27 : (@Nat) := (@Cursor.Target.W _v0 _v18);
(let _v28 : (@Nat) := (@Cursor.Target.M _v0 _v18 _v19);
(let _v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v20);
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v4
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v4 (@SmallIngress.prepared _v11
  _v12 _v4 _v13 _v14 _v19 _v18) _v22 _v18));
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v30 _v21 _v19 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v19)) _v24 _v24 (@Bool.false));
(let _v32 : (∀ (_v32 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v31 _v23 _v26) _v22 _v18 _v23 _v26);
(let _v33 : (∀ (_v33 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v32 _v22 _v18 _v23 _v26);
(let _v34 : (∀ (_v34 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v33 _v23 _v26 _v18);
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v34 _v22 _v18 _v23 _v26
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) _v27 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v23 _v26 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v27)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v27);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v11 _v12 _v19))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v29) _v24) _v23) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v25 _v21) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v26) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v27 _v26) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v23 _v26
  _v18 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))
  (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v35 _v36) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool)
  _v13 _v14 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) _v36
  _v38))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)
  _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12)
  (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) _v28))) _v29 (fun (_v36 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@SerializedBody.prepared _v35 _v21 _v28 _v23 _v26 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v18 _v0) _v0) _v27 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v36))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18) (fun
  (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v21 _v28) (@And (∀ (_v37 : (@Fin _v27)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@Fin.val _v27 _v37))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v18)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18 (fun (_v37 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v18) (@Pnp3.Models.Circuit.input _v18 (@Fin.mk _v18
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v36)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v25 _v21)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v29 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@_v31 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v37))) _v29 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v26
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v26) (@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v40 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v44 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v42)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v44 _v18) (@And (@Eq.{(0 + 1)} (@Nat) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v43 _v18) _v44)) (@And (@Eq.{(0 + 1)} (@Nat) _v37 (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@Eq.{(0 +
  1)} (@Nat) _v38 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v42) _v43) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v39 _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v40 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v42) _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v37
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@Eq.{(0 + 1)} (@Nat) _v38 _v26) (@And (@Eq.{(0 + 1)} (@Nat)
  _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v40 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v41 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v42) _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v37 _v26) (@And (@Eq.{(0 +
  1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v40 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v41 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v18 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0)) _v43)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v38 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) _v43) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v39 _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v40 _v43) (@Eq.{(0 + 1)} (@Nat) _v41
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v29 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@Cursor.Target.image _v31 _v0 _v21 _v18 _v19 _v23 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v37)))
  _v29 (@Option.some.{0} (@Bool)
  (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @TotalIngressClosure.Audit.check_raw

-- Independent literal expected type for TotalIngressClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0846 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @TotalIngressClosure.Target.Raw

-- Independent literal expected type for TotalIngressClosure.allocation.
noncomputable def PartACanonical.Types.p0847 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @TotalIngressClosure.allocation

-- Independent literal expected type for TotalIngressClosure.config.
noncomputable def PartACanonical.Types.p0848 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine
  _v0)) _v1 _v2))))) := by
  exact @TotalIngressClosure.config

-- Independent literal expected type for TotalIngressClosure.deadline.
noncomputable def PartACanonical.Types.p0849 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @TotalIngressClosure.deadline

-- Independent literal expected type for TotalIngressClosure.machine.
noncomputable def PartACanonical.Types.p0850 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @TotalIngressClosure.machine

-- Independent literal expected type for TotalIngressClosure.old.
noncomputable def PartACanonical.Types.p0851 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0))))) := by
  exact @TotalIngressClosure.old

-- Independent literal expected type for TotalIngressClosure.raw.
noncomputable def PartACanonical.Types.p0852 :
(∀ (_v0 : (@Nat)),
(@TotalIngressClosure.Target.Raw _v0)) := by
  exact @TotalIngressClosure.raw

-- Complete literal proposition for TotalIngressClosure.raw; original proof reused.
theorem PartACanonical.Surface.m0507 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v4 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4 _v2);
(let _v9 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v10)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v11 _v7))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v10)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v5)))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5))
  (@And (∀ (_v13 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v13)))))) (∀ (_v13 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v11 _v7)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v13))))))))) (@Or (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v10
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@TotalIngressClosure.Target.Raw._proof_1 _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 _v7))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v11) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v11)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v12) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v12)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v1) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v11 _v13) (@Sigma.mk.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v12 _v14)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) (fun (_v16 :
  (@Nat)) =>
(fun (_v17 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v16)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v11 _v12 _v13 _v14)
  _v1 _v15)) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v16)) (@And (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v17) _v7) (@TotalIngressClosure.config _v0 _v1
  _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v17 _v9)))) (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v4
  _v3) (fun (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v3)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v6) _v1 _v4 _v3 _v17 _v8 _v9) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v16)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4
  _v2)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 :
  Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v16)),
(let _v20 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v4
  _v2));
(∀ (_v21 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v6
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20)))))
  (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 _v20)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v16)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1
  _v4 _v3 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6
  _v1 _v4 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v18 (@Pnp3.Complexity.Uniform.V1.initialConfig _v6
  _v1 _v3 _v2))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v7) (@TotalIngressClosure.config _v0 _v1 _v3 (@IngressAllocation.extendConfig
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v4 _v3 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4
  _v16 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v11 _v12 _v13 _v14) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v18 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 _v12) _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0}
  (@Nat) _v19)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v21 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12);
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v19) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v24 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v18);
(let _v25 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v24) _v21);
(let _v26 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 _v25);
(let _v27 : (@Nat) := (@Cursor.Target.W _v0 _v18);
(let _v28 : (@Nat) := (@Cursor.Target.M _v0 _v18 _v19);
(let _v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v19) _v18) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v20);
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v4
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v4 (@SmallIngress.prepared _v11
  _v12 _v4 _v13 _v14 _v19 _v18) _v22 _v18));
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v30 _v21 _v19 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v19)) _v24 _v24 (@Bool.false));
(let _v32 : (∀ (_v32 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v31 _v23 _v26) _v22 _v18 _v23 _v26);
(let _v33 : (∀ (_v33 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v32 _v22 _v18 _v23 _v26);
(let _v34 : (∀ (_v34 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v33 _v23 _v26 _v18);
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v34 _v22 _v18 _v23 _v26
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) _v27 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v23 _v26 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v27)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v27);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v11 _v12 _v19))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v29) _v24) _v23) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v25 _v21) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v26) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v27 _v26) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v23 _v26
  _v18 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))
  (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v35 _v36) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool)
  _v13 _v14 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) _v36
  _v38))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)
  _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12)
  (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) _v28))) _v29 (fun (_v36 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@SerializedBody.prepared _v35 _v21 _v28 _v23 _v26 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v18 _v0) _v0) _v27 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v36))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18) (fun
  (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v21 _v28) (@And (∀ (_v37 : (@Fin _v27)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@Fin.val _v27 _v37))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v18)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18 (fun (_v37 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v18) (@Pnp3.Models.Circuit.input _v18 (@Fin.mk _v18
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v36)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v25 _v21)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v29 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@_v31 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v37))) _v29 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v26
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v26) (@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v40 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v44 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v42)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v44 _v18) (@And (@Eq.{(0 + 1)} (@Nat) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v43 _v18) _v44)) (@And (@Eq.{(0 + 1)} (@Nat) _v37 (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@Eq.{(0 +
  1)} (@Nat) _v38 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v42) _v43) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v39 _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v40 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v42) _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v37
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18)) (@And (@Eq.{(0 + 1)} (@Nat) _v38 _v26) (@And (@Eq.{(0 + 1)} (@Nat)
  _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v40 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v41 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v18) _v42) _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v37 _v26) (@And (@Eq.{(0 +
  1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v40 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v41 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v18 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0)) _v43)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v18) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v38 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v18 _v0) _v0) _v43) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v39 _v26) (@And (@Eq.{(0 + 1)} (@Nat) _v40 _v43) (@Eq.{(0 + 1)} (@Nat) _v41
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v4 _v16 _v8) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v4 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v29 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@Cursor.Target.image _v31 _v0 _v21 _v18 _v19 _v23 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) _v37)))
  _v29 (@Option.some.{0} (@Bool)
  (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @TotalIngressClosure.raw

-- Independent literal expected type for Turing.Tape.mk₁.eq_1.
noncomputable def PartACanonical.Types.p0853.{u_1} :
(∀ {_v0 : (Sort (u_1 + 1))},
(∀ [_v1 : (@Inhabited.{(u_1 + 1)} _v0)],
(∀ (_v2 : (@List.{u_1} _v0)),
(@Eq.{(u_1 + 1)} (@Turing.Tape.{u_1} _v0 _v1) (@Turing.Tape.mk₁.{u_1} _v0 _v1 _v2) (@Turing.Tape.mk₂.{u_1} _v0 _v1
  (@List.nil.{u_1} _v0) _v2))))) := by
  exact @Turing.Tape.mk₁.eq_1.{u_1}

-- Complete literal proposition for Turing.Tape.mk₁.eq_1; original proof reused.
theorem PartACanonical.Surface.m0508.{u_1} :
(∀ {_v0 : (Sort (u_1 + 1))},
(∀ [_v1 : (@Inhabited.{(u_1 + 1)} _v0)],
(∀ (_v2 : (@List.{u_1} _v0)),
(@Eq.{(u_1 + 1)} (@Turing.Tape.{u_1} _v0 _v1) (@Turing.Tape.mk₁.{u_1} _v0 _v1 _v2) (@Turing.Tape.mk₂.{u_1} _v0 _v1
  (@List.nil.{u_1} _v0) _v2))))) := by
  exact @Turing.Tape.mk₁.eq_1.{u_1}

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.Decides.
noncomputable def PartACanonical.Types.p0854 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : _v0),
(∀ (_v4 : _v0),
(∀ (_v5 : (@Nat)),
(∀ {_v6 : (@Nat)},
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6)),
(∀ (_v8 : (@Bool)),
(Sort 0)))))))))) := by
  exact @UniformClassBridgeClosure.Ordinary.Decides

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.UniformNP.
noncomputable def PartACanonical.Types.p0855 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(Sort 0)) := by
  exact @UniformClassBridgeClosure.Ordinary.UniformNP

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.UniformP.
noncomputable def PartACanonical.Types.p0856 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(Sort 0)) := by
  exact @UniformClassBridgeClosure.Ordinary.UniformP

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.Verifies.
noncomputable def PartACanonical.Types.p0857 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : _v0),
(∀ (_v4 : _v0),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(Sort 0)))))))) := by
  exact @UniformClassBridgeClosure.Ordinary.Verifies

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.trace.
noncomputable def PartACanonical.Types.p0858 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))))))) := by
  exact @UniformClassBridgeClosure.Ordinary.trace

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.trace.eq_1.
noncomputable def PartACanonical.Types.p0859 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  _v3) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0,
  0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v3)))))) := by
  exact @UniformClassBridgeClosure.Ordinary.trace.eq_1

-- Complete literal proposition for UniformClassBridgeClosure.Ordinary.trace.eq_1; original proof reused.
theorem PartACanonical.Surface.m0509 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  _v3) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0,
  0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v3)))))) := by
  exact @UniformClassBridgeClosure.Ordinary.trace.eq_1

-- Independent literal expected type for UniformClassBridgeClosure.Ordinary.trace.eq_2.
noncomputable def PartACanonical.Types.p0860 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v0 _v1 _v2 (@Nat.succ _v4) _v3) (@Option.bind.{0, 0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v2 _v3)
  (@UniformClassBridgeClosure.Ordinary.trace _v0 _v1 _v2 _v4)))))))) := by
  exact @UniformClassBridgeClosure.Ordinary.trace.eq_2

-- Complete literal proposition for UniformClassBridgeClosure.Ordinary.trace.eq_2; original proof reused.
theorem PartACanonical.Surface.m0510 :
(∀ {_v0 : (Sort (0 + 1))},
(∀ [_v1 : (@Inhabited.{(0 + 1)} _v0)],
(∀ (_v2 : (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1)),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v0 _v1 _v2 (@Nat.succ _v4) _v3) (@Option.bind.{0, 0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v0 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v0 _v1 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v2 _v3)
  (@UniformClassBridgeClosure.Ordinary.trace _v0 _v1 _v2 _v4)))))))) := by
  exact @UniformClassBridgeClosure.Ordinary.trace.eq_2

-- Independent literal expected type for UniformClassBridgeClosure.Target.Lifts.
noncomputable def PartACanonical.Types.p0861 :
(Sort 0) := by
  exact @UniformClassBridgeClosure.Target.Lifts

-- Independent literal expected type for UniformClassBridgeClosure.Target.Transfer.
noncomputable def PartACanonical.Types.p0862 :
(Sort 0) := by
  exact @UniformClassBridgeClosure.Target.Transfer

-- Independent literal expected type for UniformClassBridgeClosure.canonical.
noncomputable def PartACanonical.Types.p0863 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v4)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v5)),
(@UniformClassBridgeClosure.Ordinary.Decides (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v4 _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v4
  _v5) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v4 _v5 _v6 _v7) (@_v2 _v4 _v5 _v6 _v7)))))))))) := by
  exact @UniformClassBridgeClosure.canonical

-- Complete literal proposition for UniformClassBridgeClosure.canonical; original proof reused.
theorem PartACanonical.Surface.m0511 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v4)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v5)),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Exists.{(0 + 1)}
  (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v9 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v4 _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v8
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v4 _v5)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v4 _v5 _v6 _v7))))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v9)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v9) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Eq.{(0 + 1)} (@Bool) (@_v2 _v4 _v5 _v6 _v7) (@Bool.true)) (@instDecidableEqBool (@_v2 _v4 _v5 _v6 _v7)
  (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))) (@Option.some.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v9) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v8)),
(∀ (_v12 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v10
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v4 _v5)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v4 _v5 _v6 _v7))))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v12))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v12) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v12) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))))))))))))))))))))))))) := by
  exact @UniformClassBridgeClosure.canonical

-- Independent literal expected type for UniformClassBridgeClosure.malformed.
noncomputable def PartACanonical.Types.p0864 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v4)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v4 _v5) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)))),
(@UniformClassBridgeClosure.Ordinary.Decides (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v4 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v4 _v5
  (@Bool.false))))))))) := by
  exact @UniformClassBridgeClosure.malformed

-- Complete literal proposition for UniformClassBridgeClosure.malformed; original proof reused.
theorem PartACanonical.Surface.m0512 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v4)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v4 _v5) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Exists.{(0 + 1)}
  (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v8 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v7
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v4 _v5)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v8)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v8) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool) (@Bool.false)
  (@Bool.true)) (@instDecidableEqBool (@Bool.false) (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v8)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))))) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v7)),
(∀ (_v11 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v9
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v4 _v5)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v11))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v11) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v11) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))))))))))))))))))))))))) := by
  exact @UniformClassBridgeClosure.malformed

-- Independent literal expected type for UniformClassBridgeClosure.np_lift.
noncomputable def PartACanonical.Types.p0865 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformNP _v0)),
(@UniformClassBridgeClosure.Ordinary.UniformNP _v0))) := by
  exact @UniformClassBridgeClosure.np_lift

-- Complete literal proposition for UniformClassBridgeClosure.np_lift; original proof reused.
theorem PartACanonical.Surface.m0513 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformNP _v0)),
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation) (fun (_v2 :
  (@Pnp3.Complexity.Uniform.V1.WitnessRelation)) =>
(@Exists.{((0 + 1) + 1)} (Sort (0 + 1)) (fun (_v3 : (Sort (0 + 1))) =>
(@Exists.{(0 + 1)} (@Fintype.{0} _v3) (fun (_v4 : (@Fintype.{0} _v3)) =>
(@Exists.{(0 + 1)} (@Inhabited.{(0 + 1)} _v3) (fun (_v5 : (@Inhabited.{(0 + 1)} _v3)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 _v5) (fun (_v6 :
  (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 _v5)) =>
(@Exists.{(0 + 1)} _v3 (fun (_v7 : _v3) =>
(@Exists.{(0 + 1)} _v3 (fun (_v8 : _v3) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v11)),
(@And (@Ne.{(0 + 1)} _v3 _v7 _v8) (@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (fun (_v14 :
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v11 _v9) _v9)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace _v3 _v5 _v6 _v13 (@Turing.TM0.init.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 _v5 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v11
  _v12)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))
  _v14)) (@And (@Eq.{(0 + 1)} _v3 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v14)
  (@ite.{(0 + 1)} _v3 (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v15 :
  (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v11 _v12) (fun (_v15 : (@Unit)) =>
(@Bool.false)) (fun (_v15 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v2 (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v15 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v11 _v12) (fun (_v15 : (@Unit)) =>
(@Bool.false)) (fun (_v15 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v2 (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) (@Sigma.{0, 0} (@Nat) (fun (_v16 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16))) _v15))))) (@Bool.true)) _v7 _v8)) (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v3 _v5 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v6 _v14) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v13)),
(∀ (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v3 _v5 _v6 _v15 (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v3 _v5 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v11 _v12))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v17))),
(@And (@Ne.{(0 + 1)} _v3 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17)
  _v7) (@Ne.{(0 + 1)} _v3 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v3
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17)
  _v8))))))))))))))))) (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v11)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@_v0 _v11 _v12) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v13) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v13)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v11 _v10) _v10)) (@Eq.{(0 + 1)} (@Bool) (@_v2 _v11 _v13 _v12 _v14)
  (@Bool.true))))))))))))))))))))))))))))))) := by
  exact @UniformClassBridgeClosure.np_lift

-- Independent literal expected type for UniformClassBridgeClosure.np_parameters.
noncomputable def PartACanonical.Types.p0866 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v2 _v3 _v1)),
(∀ (_v6 : (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@_v0 _v6 _v7) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v8) (fun (_v9 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v8))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@Pnp3.Complexity.Uniform.V1.polyClock _v4 _v6)) (@Eq.{(0 + 1)} (@Bool) (@_v1
  _v6 _v8 _v7 _v9) (@Bool.true))))))))))),
(@And (@UniformClassBridgeClosure.Ordinary.Verifies (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v2)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  _v2) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v2) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v1) (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v7)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@_v0 _v7 _v8) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v10 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v7 _v4) _v4)) (@Eq.{(0 + 1)} (@Bool) (@_v1 _v7 _v9 _v8 _v10) (@Bool.true)))))))))))))))))) := by
  exact @UniformClassBridgeClosure.np_parameters

-- Complete literal proposition for UniformClassBridgeClosure.np_parameters; original proof reused.
theorem PartACanonical.Surface.m0514 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v2 _v3 _v1)),
(∀ (_v6 : (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@_v0 _v6 _v7) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v8) (fun (_v9 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v8))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@Pnp3.Complexity.Uniform.V1.polyClock _v4 _v6)) (@Eq.{(0 + 1)} (@Bool) (@_v1
  _v6 _v8 _v7 _v9) (@Bool.true))))))))))),
(@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v7)),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v2) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v2) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Exists.{(0 + 1)}
  (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v10 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v2) _v9
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v7 _v8)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v10)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v10) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool)
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v11 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v7 _v8) (fun (_v11 : (@Unit)) =>
(@Bool.false)) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v11 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v7 _v8) (fun (_v11 : (@Unit)) =>
(@Bool.false)) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) (@Sigma.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v12))) _v11))))) (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v2) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v2) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v2) _v10)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))))) (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v9)),
(∀ (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v2) _v11
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v7 _v8)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v13))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v2) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v2)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v2) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))))))))))))))))))) (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v7)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@_v0 _v7 _v8) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v10 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v7 _v4) _v4)) (@Eq.{(0 + 1)} (@Bool) (@_v1 _v7 _v9 _v8 _v10) (@Bool.true)))))))))))))))))) := by
  exact @UniformClassBridgeClosure.np_parameters

-- Independent literal expected type for UniformClassBridgeClosure.operational.
noncomputable def PartACanonical.Types.p0867 :
(@UniformClassBridgeClosure.Target.Transfer) := by
  exact @UniformClassBridgeClosure.operational

-- Complete literal proposition for UniformClassBridgeClosure.operational; original proof reused.
theorem PartACanonical.Surface.m0515 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v4 : (@Bool)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.DecidesWithin _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3 _v4)),
(@And (@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (0 : Nat))))) (@Option.some.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (0 :
  Nat)))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v6 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v7 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v6
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v2 _v3)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v7)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v7) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool) _v4 (@Bool.true))
  (@instDecidableEqBool _v4 (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (0 : Nat))))) (@Option.some.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (0 :
  Nat))))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v7) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v6)),
(∀ (_v10 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v8
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v2 _v3)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v10))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (0 : Nat)))))) (@Ne.{(0 + 1)}
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (0 : Nat))))))))))))))))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v6 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v7 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@And (@LE.le.{0} (@Nat)
  (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))) (@ite.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Eq.{(0 + 1)} (@Bool) _v4 (@Bool.true))
  (@instDecidableEqBool _v4 (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v6)) (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v2 _v3)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v7)) (@And (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v7) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat)))))) (∀ (_v8 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v7) _v8) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))) (@instDecidableAnd
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8))
  (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))) (fun (_v9 : (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 :
  Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Int.toNat (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8)) (@StandardTMBridgeClosure.Represents._proof_2 _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3)) _v8 _v9))))) (fun (_v9 : (@Not (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v8) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v10 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v8)) (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v2 _v3)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v10)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat)))))) (∀ (_v11 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v10) _v11) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))) (@instDecidableAnd
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11))
  (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))) (fun (_v12 : (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 :
  Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Int.toNat (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11)) (@StandardTMBridgeClosure.Represents._proof_2 _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3)) _v11 _v12))))) (fun (_v12 : (@Not (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3))))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (@And (∀ (_v8 :
  (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v6)),
(let _v10 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) := (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v3));
(let _v11 : (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10)));
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v12 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v8)) (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v2 _v3)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v12)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v12) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v11) (@UniformClassBridgeClosure.Target.Transfer.match_1.{(0 + 1)} (fun
  (_v13 : (@Pnp3.Complexity.Uniform.V1.Move)) =>
(@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v11)) (fun (_v13 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (1 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (1 :
  Nat)))) (fun (_v13 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (2 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (2 :
  Nat)))) (fun (_v13 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@UniformClassBridgeClosure.Target.Transfer._proof_1) (3 :
  Nat)))))))) (∀ (_v13 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v12) _v13) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Int) _v13
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq _v13 (@OfNat.ofNat.{0} (@Int) (0 :
  Nat) (@instOfNat (0 : Nat)))) (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) _v11))) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))) (@instDecidableAnd
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10)))
  _v13)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0}
  (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock
  _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))) (fun (_v14 : (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 :
  Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Int.toNat (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13)) (@UniformClassBridgeClosure.Target.Transfer._proof_2 _v0
  _v1 _v2 _v3 _v8 _v13 _v14))))) (fun (_v14 : (@Not (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0
  : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10)))
  _v13)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2) _v10))) _v13)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  (@Pnp3.Complexity.Uniform.V1.polyClock _v1 _v2))))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))))))))))) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)))),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v10 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v8
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v2 _v3)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v10)))))))))))))))))))))))) := by
  exact @UniformClassBridgeClosure.operational

-- Independent literal expected type for UniformClassBridgeClosure.p_lift.
noncomputable def PartACanonical.Types.p0868 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformP _v0)),
(@UniformClassBridgeClosure.Ordinary.UniformP _v0))) := by
  exact @UniformClassBridgeClosure.p_lift

-- Complete literal proposition for UniformClassBridgeClosure.p_lift; original proof reused.
theorem PartACanonical.Surface.m0516 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.Language)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformP _v0)),
(@Exists.{((0 + 1) + 1)} (Sort (0 + 1)) (fun (_v2 : (Sort (0 + 1))) =>
(@Exists.{(0 + 1)} (@Fintype.{0} _v2) (fun (_v3 : (@Fintype.{0} _v2)) =>
(@Exists.{(0 + 1)} (@Inhabited.{(0 + 1)} _v2) (fun (_v4 : (@Inhabited.{(0 + 1)} _v2)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4) (fun (_v5 :
  (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4)) =>
(@Exists.{(0 + 1)} _v2 (fun (_v6 : _v2) =>
(@Exists.{(0 + 1)} _v2 (fun (_v7 : _v2) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9)),
(@And (@Ne.{(0 + 1)} _v2 _v6 _v7) (@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (fun (_v12 :
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v9 _v8) _v8)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v11 (@Turing.TM0.init.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v9
  _v10)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))
  _v12)) (@And (@Eq.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v12)
  (@ite.{(0 + 1)} _v2 (@Eq.{(0 + 1)} (@Bool) (@_v0 _v9 _v10) (@Bool.true)) (@instDecidableEqBool (@_v0 _v9 _v10)
  (@Bool.true)) _v6 _v7)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v5 _v12) (@Option.none.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 _v11)),
(∀ (_v15 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v13 (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v9 _v10))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v15))),
(@And (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v15)
  _v6) (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v15)
  _v7))))))))))))))))))))))))))))))))) := by
  exact @UniformClassBridgeClosure.p_lift

-- Independent literal expected type for UniformClassBridgeClosure.verifier.
noncomputable def PartACanonical.Types.p0869 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v0 _v1 _v2)),
(@UniformClassBridgeClosure.Ordinary.Verifies (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2))))) := by
  exact @UniformClassBridgeClosure.verifier

-- Complete literal proposition for UniformClassBridgeClosure.verifier; original proof reused.
theorem PartACanonical.Surface.m0517 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.VerifiesRelation _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v4)),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Exists.{(0 + 1)}
  (@Nat) (fun (_v6 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v7 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v6
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v4 _v5)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v7)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v7) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool)
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v8 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v4 _v5) (fun (_v8 : (@Unit)) =>
(@Bool.false)) (fun (_v8 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v2 (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v8 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v4 _v5) (fun (_v8 : (@Unit)) =>
(@Bool.false)) (fun (_v8 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v2 (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) (@Sigma.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v9))) _v8))))) (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v7)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))))) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v6)),
(∀ (_v10 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile _v0) _v8
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v4 _v5)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v10))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))))))))))))))))))))))) := by
  exact @UniformClassBridgeClosure.verifier

-- Independent literal expected type for VirtualFinalClosure.GuardMeaning.check_checked_guard_acceptance.
noncomputable def PartACanonical.Types.p0870 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v6 _v7)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v2 _v3)))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp4.Frontier.ContractExpansion.tagLen))
  (@Option.some.{0} (@Nat) (@Pnp4.Frontier.ContractExpansion.treePrefixTag)))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Option.some.{0} (@Nat) _v4))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(∀ (_v14 : (∀ (_v14 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Fin.val (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  _v14))) (@Bool.false)))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v5 _v0 _v1
  _v6 _v7) (@Bool.true)) (∀ (_v16 : (@Fin (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3) (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v2) _v16))) (@Nat.testBit (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2) _v16) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))))))))))))))))) := by
  exact @VirtualFinalClosure.GuardMeaning.check_checked_guard_acceptance

-- Complete literal proposition for VirtualFinalClosure.GuardMeaning.check_checked_guard_acceptance; original proof reused.
theorem PartACanonical.Surface.m0518 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v6 _v7)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v2 _v3)))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp4.Frontier.ContractExpansion.tagLen))
  (@Option.some.{0} (@Nat) (@Pnp4.Frontier.ContractExpansion.treePrefixTag)))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Option.some.{0} (@Nat) _v4))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(∀ (_v14 : (∀ (_v14 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Fin.val (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  _v14))) (@Bool.false)))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v5 _v0 _v1
  _v6 _v7) (@Bool.true)) (∀ (_v16 : (@Fin (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3) (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v2) _v16))) (@Nat.testBit (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2) _v16) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))))))))))))))))) := by
  exact @VirtualFinalClosure.GuardMeaning.check_checked_guard_acceptance

-- Independent literal expected type for VirtualFinalClosure.GuardMeaning.checked_guard_acceptance.
noncomputable def PartACanonical.Types.p0871 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v6 _v7)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v2 _v3)))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp4.Frontier.ContractExpansion.tagLen))
  (@Option.some.{0} (@Nat) (@Pnp4.Frontier.ContractExpansion.treePrefixTag)))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Option.some.{0} (@Nat) _v4))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(∀ (_v14 : (∀ (_v14 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Fin.val (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  _v14))) (@Bool.false)))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v5 _v0 _v1
  _v6 _v7) (@Bool.true)) (∀ (_v16 : (@Fin (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3) (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v2) _v16))) (@Nat.testBit (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2) _v16) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))))))))))))))))) := by
  exact @VirtualFinalClosure.GuardMeaning.checked_guard_acceptance

-- Complete literal proposition for VirtualFinalClosure.GuardMeaning.checked_guard_acceptance; original proof reused.
theorem PartACanonical.Surface.m0519 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v6 _v7)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v2 _v3)))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp4.Frontier.ContractExpansion.tagLen))
  (@Option.some.{0} (@Nat) (@Pnp4.Frontier.ContractExpansion.treePrefixTag)))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7)
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Option.some.{0} (@Nat) _v4))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(∀ (_v14 : (∀ (_v14 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3)
  (@Pnp3.Models.Partial.tableLen _v2)) (@Pnp4.Frontier.ContractExpansion.idxWidth
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5))) _v2))
  (@Fin.val (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2)
  _v14))) (@Bool.false)))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v5)) _v2))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v5 _v0 _v1
  _v6 _v7) (@Bool.true)) (∀ (_v16 : (@Fin (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v6 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.tagLen) _v3) (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v2) _v16))) (@Nat.testBit (@Fin.val (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2) _v16) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))))))))))))))))) := by
  exact @VirtualFinalClosure.GuardMeaning.checked_guard_acceptance

-- Independent literal expected type for VirtualFinalClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0872 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @VirtualFinalClosure.Target.Raw

-- Independent literal expected type for VirtualFinalClosure.Target.virtualImage.
noncomputable def PartACanonical.Types.p0873 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool)))))))))) := by
  exact @VirtualFinalClosure.Target.virtualImage

-- Independent literal expected type for VirtualFinalClosure.allocation.
noncomputable def PartACanonical.Types.p0874 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @VirtualFinalClosure.allocation

-- Independent literal expected type for VirtualFinalClosure.allocation.eq_1.
noncomputable def PartACanonical.Types.p0875 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@VirtualFinalClosure.allocation _v0 _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (281474976710656 : Nat) (@instOfNatNat (281474976710656 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))))))) := by
  exact @VirtualFinalClosure.allocation.eq_1

-- Complete literal proposition for VirtualFinalClosure.allocation.eq_1; original proof reused.
theorem PartACanonical.Surface.m0520 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@VirtualFinalClosure.allocation _v0 _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (281474976710656 : Nat) (@instOfNatNat (281474976710656 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))))))) := by
  exact @VirtualFinalClosure.allocation.eq_1

-- Independent literal expected type for VirtualFinalClosure.check_raw.
noncomputable def PartACanonical.Types.p0876 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@VirtualFinalClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v5 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@VirtualFinalClosure.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v5) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v5 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@VirtualFinalClosure.deadline _v0 _v1)) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v10 _v7))) (@VirtualFinalClosure.spaceBound _v0 _v1)))) (@And (∀
  (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v10 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v10 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (∀
  (_v12 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v13 : (@Fin (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v10 _v7)) (@VirtualFinalClosure.control _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0
  (@BodyIngress.body _v0 (@SerializedBody.entry _v12)))) _v13)))))))) (@Or (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat)
  _v5 _v3) (fun (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v3)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v11 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@CertificateGuardClosure.deadline _v0
  _v1)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v5
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v5 _v11 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v9 _v7) (@VirtualFinalClosure.config _v0 _v1 _v3 (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@IngressAllocation.extendConfig
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0)) _v1 _v5 _v3 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v5 _v11 _v8)))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v11) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v11)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v1) (fun (_v14 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) _v10 _v12) (@Sigma.mk.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) _v11 _v13)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) (fun (_v15 :
  (@Nat)) =>
(fun (_v16 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v15)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v10 _v11 _v12 _v13)
  _v1 _v14)) (@And (@Eq.{(0 + 1)} (@Nat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v15
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v10 _v11) _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13)) (@Option.some.{0}
  (@Nat) _v16)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v18 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11);
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v21 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15);
(let _v22 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v21) _v18);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 _v22);
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v15);
(let _v25 : (@Nat) := (@Cursor.Target.M _v0 _v15 _v16);
(let _v26 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0);
(let _v27 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v28 : (∀ (_v28 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v27
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v27 (@SmallIngress.prepared _v10
  _v11 _v27 _v12 _v13 _v16 _v15) _v19 _v15));
(let _v29 : (∀ (_v29 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v28 _v18 _v16 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v16)) _v21 _v21 (@Bool.false));
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v29 _v20 _v23) _v19 _v15 _v20 _v23);
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v30 _v19 _v15 _v20 _v23);
(let _v32 : (∀ (_v32 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v31 _v20 _v23 _v15);
(let _v33 : (∀ (_v33 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v32 _v19 _v15 _v20 _v23
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v26 _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v20 _v23 _v15 _v26
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v24);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v10 _v11 _v16))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v21) _v20) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v18) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24 _v23) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v20 _v23 _v15 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v25 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v18)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v33 _v34) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool)
  _v12 _v13 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v34
  _v36))))))) (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v5 _v3) (fun (_v34 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v3))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LE.le.{0} (@Nat) (@instLENat) _v35 _v9)),
(@Exists.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (fun (_v37 : (@Fin
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v35 _v7) (@VirtualFinalClosure.config _v0 _v1 _v3 _v37
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0)) _v1 _v5 _v3 _v34 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v5 _v35 _v8)))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v9 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@VirtualFinalClosure.control _v0
  (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11)
  (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13) _v25))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (144 : Nat)
  (@instOfNatNat (144 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v16) _v15) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v17) (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)))
  =>
(@SerializedBody.prepared _v33 _v18 _v25 _v20 _v23 _v15 _v26 _v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v3) _v35)))))))))))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v18 _v25) (@And (@Or (@Eq.{(0 + 1)} (@Nat) _v22 _v18)
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v18) (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v23
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v35 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v36 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@CappedWeight.Target.Cap _v0 _v15 _v23 _v34 _v35 _v36 _v37 _v38))))))))))))))) (@And (∀ (_v34 : (@Fin _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 (@Fin.val _v24 _v34))) (@Bool.false))) (@And (∀ (_v34
  : (@Eq.{(0 + 1)} (@Nat) _v15 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v15)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15 (fun (_v35 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15)))
  =>
(@Bool.false))) (@Option.none.{0} (@Pnp3.Models.Circuit _v15)))) (@And (∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v15)),
(@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v15)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15 (fun (_v35 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v15) (@Pnp3.Models.Circuit.input _v15 (@Fin.mk _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v34))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat))
  =>
(@And (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v22 _v18) (@Eq.{(0 + 1)} (@Nat) _v34 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v18) (@And (@LE.le.{0} (@Nat) (@instLENat) _v23
  _v34) (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v24 _v23) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v34)) _v15) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v9 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@ite.{(0
  + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@instDecidableEqBool (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v17) (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@VirtualFinalClosure.Target.virtualImage _v29 _v18 _v16 _v15 _v20 _v22 _v34 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v35)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @VirtualFinalClosure.check_raw

-- Complete literal proposition for VirtualFinalClosure.check_raw; original proof reused.
theorem PartACanonical.Surface.m0521 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@VirtualFinalClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v5 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@VirtualFinalClosure.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v5) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v5 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@VirtualFinalClosure.deadline _v0 _v1)) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v10 _v7))) (@VirtualFinalClosure.spaceBound _v0 _v1)))) (@And (∀
  (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v10 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v10 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (∀
  (_v12 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v13 : (@Fin (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v10 _v7)) (@VirtualFinalClosure.control _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0
  (@BodyIngress.body _v0 (@SerializedBody.entry _v12)))) _v13)))))))) (@Or (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat)
  _v5 _v3) (fun (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v3)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v11 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@CertificateGuardClosure.deadline _v0
  _v1)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v5
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v5 _v11 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v9 _v7) (@VirtualFinalClosure.config _v0 _v1 _v3 (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@IngressAllocation.extendConfig
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0)) _v1 _v5 _v3 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v5 _v11 _v8)))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v11) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v11)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v1) (fun (_v14 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) _v10 _v12) (@Sigma.mk.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) _v11 _v13)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) (fun (_v15 :
  (@Nat)) =>
(fun (_v16 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v15)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v10 _v11 _v12 _v13)
  _v1 _v14)) (@And (@Eq.{(0 + 1)} (@Nat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v15
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v10 _v11) _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13)) (@Option.some.{0}
  (@Nat) _v16)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v18 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11);
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v21 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15);
(let _v22 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v21) _v18);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 _v22);
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v15);
(let _v25 : (@Nat) := (@Cursor.Target.M _v0 _v15 _v16);
(let _v26 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0);
(let _v27 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v28 : (∀ (_v28 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v27
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v27 (@SmallIngress.prepared _v10
  _v11 _v27 _v12 _v13 _v16 _v15) _v19 _v15));
(let _v29 : (∀ (_v29 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v28 _v18 _v16 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v16)) _v21 _v21 (@Bool.false));
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v29 _v20 _v23) _v19 _v15 _v20 _v23);
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v30 _v19 _v15 _v20 _v23);
(let _v32 : (∀ (_v32 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v31 _v20 _v23 _v15);
(let _v33 : (∀ (_v33 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v32 _v19 _v15 _v20 _v23
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v26 _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v20 _v23 _v15 _v26
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v24);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v10 _v11 _v16))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v21) _v20) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v18) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24 _v23) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v20 _v23 _v15 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v25 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v18)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v33 _v34) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool)
  _v12 _v13 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v34
  _v36))))))) (@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v5 _v3) (fun (_v34 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v3))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LE.le.{0} (@Nat) (@instLENat) _v35 _v9)),
(@Exists.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (fun (_v37 : (@Fin
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v35 _v7) (@VirtualFinalClosure.config _v0 _v1 _v3 _v37
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0)) _v1 _v5 _v3 _v34 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v5 _v35 _v8)))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v9 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@VirtualFinalClosure.control _v0
  (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11)
  (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13) _v25))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (144 : Nat)
  (@instOfNatNat (144 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (144 : Nat) (@instOfNatNat (144 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v16) _v15) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v17) (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)))
  =>
(@SerializedBody.prepared _v33 _v18 _v25 _v20 _v23 _v15 _v26 _v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v3) _v35)))))))))))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v18 _v25) (@And (@Or (@Eq.{(0 + 1)} (@Nat) _v22 _v18)
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v18) (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v23
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v35 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v36 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v40 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v39)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v15) (@And (@Eq.{(0 + 1)} (@Nat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v40 _v15) _v41)) (@And (@Eq.{(0 + 1)} (@Nat) _v34 (@Pnp4.Frontier.ContractExpansion.bitLength _v15)) (@And (@Eq.{(0 +
  1)} (@Nat) _v35 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v39) _v40) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v36 _v23) (@And (@Eq.{(0 + 1)} (@Nat) _v37 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v41 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v39) _v23) (@And (@Eq.{(0 + 1)} (@Nat) _v34
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15)) (@And (@Eq.{(0 + 1)} (@Nat) _v35 _v23) (@And (@Eq.{(0 + 1)} (@Nat)
  _v36 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v37 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v38 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v39 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v39) _v23) (@And (@Eq.{(0 + 1)} (@Nat) _v34 _v23) (@And (@Eq.{(0 +
  1)} (@Nat) _v35 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v36 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v37 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v38 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v40 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v15) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v15 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0)) _v40)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v34 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v15) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v39) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v35 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v40) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v36 _v23) (@And (@Eq.{(0 + 1)} (@Nat) _v37 _v40) (@Eq.{(0 + 1)} (@Nat) _v38
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))))) (@And (∀ (_v34 : (@Fin
  _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 (@Fin.val _v24 _v34))) (@Bool.false))) (@And (∀ (_v34
  : (@Eq.{(0 + 1)} (@Nat) _v15 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v15)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15 (fun (_v35 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15)))
  =>
(@Bool.false))) (@Option.none.{0} (@Pnp3.Models.Circuit _v15)))) (@And (∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v15)),
(@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v15)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15 (fun (_v35 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v15) (@Pnp3.Models.Circuit.input _v15 (@Fin.mk _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v34))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat))
  =>
(@And (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v22 _v18) (@Eq.{(0 + 1)} (@Nat) _v34 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v18) (@And (@LE.le.{0} (@Nat) (@instLENat) _v23
  _v34) (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v24 _v23) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v34)) _v15) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v9 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@ite.{(0
  + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@instDecidableEqBool (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v17) (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@VirtualFinalClosure.Target.virtualImage _v29 _v18 _v16 _v15 _v20 _v22 _v34 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v35)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @VirtualFinalClosure.check_raw

-- Independent literal expected type for VirtualFinalClosure.check_virtual_relation.
noncomputable def PartACanonical.Types.p0877 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ {_v5 : (@Sigma.{0, 0} (@Nat) (fun (_v5 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v5))))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v7))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v7))) _v5)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v3 _v4)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v8)))) _v5))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Pnp4.Frontier.ContractExpansion.PrefixBitVec
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)))) (@Pnp4.Frontier.ContractExpansion.contentWitness
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v3 _v4) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5))) (fun (_v9 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5))))) =>
(@Bool.false)))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v2 _v0 _v1
  _v3 _v4) (@Bool.true)) (@And (@Pnp4.Frontier.ContractExpansion.PrefixInput.prefixAgrees
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5) (fun (_v10 : (@Fin
  (@Pnp4.Frontier.SearchMCSPCompressionProblem.witnessBits (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5))))) =>
(@Bool.false))) (∀ (_v10 : (@Fin (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.x (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5) _v10) (@Nat.testBit (@Fin.val (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5))) _v10) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))))))))) := by
  exact @VirtualFinalClosure.check_virtual_relation

-- Complete literal proposition for VirtualFinalClosure.check_virtual_relation; original proof reused.
theorem PartACanonical.Surface.m0522 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ {_v5 : (@Sigma.{0, 0} (@Nat) (fun (_v5 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v5))))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v7))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v7))) _v5)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v3 _v4)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v8)))) _v5))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Pnp4.Frontier.ContractExpansion.PrefixBitVec
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)))) (@Pnp4.Frontier.ContractExpansion.contentWitness
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v3 _v4) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5))) (fun (_v9 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v9))) _v5))))) =>
(@Bool.false)))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v2 _v0 _v1
  _v3 _v4) (@Bool.true)) (@And (@Pnp4.Frontier.ContractExpansion.PrefixInput.prefixAgrees
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5) (fun (_v10 : (@Fin
  (@Pnp4.Frontier.SearchMCSPCompressionProblem.witnessBits (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5))))) =>
(@Bool.false))) (∀ (_v10 : (@Fin (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v10))) _v5))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.x (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5) _v10) (@Nat.testBit (@Fin.val (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v2)) _v11))) _v5))) _v10) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))))))))) := by
  exact @VirtualFinalClosure.check_virtual_relation
