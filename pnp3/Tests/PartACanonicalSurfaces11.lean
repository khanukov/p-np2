import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for RawPrelude.Target.Raw.
noncomputable def PartACanonical.Types.p0629 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RawPrelude.Target.Raw

-- Independent literal expected type for RawPrelude.accepted_prelude.
noncomputable def PartACanonical.Types.p0630 :
(∀ (_v0 : (@Nat)),
(@RawPrelude.Target.Raw _v0)) := by
  exact @RawPrelude.accepted_prelude

-- Complete literal proposition for RawPrelude.accepted_prelude; original proof reused.
theorem PartACanonical.Surface.m0378 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(@Exists.{(0 + 1)} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6)))) (fun (_v6 : (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) _v6)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (let _v9 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2);
(let _v10 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v10);
(let _v12 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6));
(let _v13 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 _v12) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))));
(let _v15 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v10);
(let _v16 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12)) _v9);
(let _v17 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v16);
(let _v18 : (∀ (_v18 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@SmallIngress.prepared _v1 _v2
  _v11 _v3 _v4 _v7 _v12) _v13 _v12));
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v18 _v9 _v7 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@Bool.false));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v19 _v15 _v17) _v13 _v12 _v15 _v17);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v20 _v13 _v12 _v15 _v17);
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v21 _v15 _v17 _v12);
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v3 _v4));
(@And (∀ (_v24 : (@Eq.{(0 + 1)} (@Nat) _v16 _v9)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v25 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v25 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2147483648 : Nat) (@instOfNatNat (2147483648 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v25 _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@RawPrelude.Target.Raw._proof_3))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v8) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@_v19 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v26)))))) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v26 _v25)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v26 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v26 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))))))))))) (∀ (_v24 : (@LT.lt.{0} (@Nat)
  (@instLTNat) _v16 _v9)),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v17)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v25 :
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v17)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) _v9 (@Cursor.Target.M _v0 _v12 _v7)) (@Exists.{(0 + 1)} (@Nat) (fun (_v26 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v26 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v26 _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (250 : Nat) (@instOfNatNat (250 : Nat))) (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@RawPrelude.Target.Raw._proof_4 _v0 _v1 _v2 _v6 _v7 _v25)) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@_v21 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v27)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v15 _v14) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (19 : Nat) (@instOfNatNat (19 : Nat))) _v17))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) _v12)) (@OfNat.ofNat.{0} (@Nat) (48 : Nat) (@instOfNatNat (48 : Nat))))) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2147483648 : Nat) (@instOfNatNat (2147483648 : Nat))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v15 _v14) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (19 : Nat) (@instOfNatNat (19 : Nat))) _v17)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v12))
  (@OfNat.ofNat.{0} (@Nat) (48 : Nat) (@instOfNatNat (48 : Nat))))) _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@RawPrelude.Target.Raw._proof_3))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v8) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Cursor.Target.image _v19 _v0 _v9 _v12 _v7 _v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v27)))))) (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v15 _v14)
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (19 : Nat)
  (@instOfNatNat (19 : Nat))) _v17)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v12)) (@OfNat.ofNat.{0} (@Nat) (48 : Nat) (@instOfNatNat
  (48 : Nat))))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v27 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v27 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))))))))))))) (@And (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v17) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Cursor.Target.W _v0 _v12) _v17) (@Exists.{(0 + 1)} (@Nat) (fun (_v26 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v26 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v27
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (524288 : Nat)
  (@instOfNatNat (524288 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v26 _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@RawPrelude.Target.Raw._proof_4 _v0 _v1 _v2 _v6 _v7 _v25)) (fun (_v28 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v22 _v13 _v12 _v15 _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v28)))))) (@And (∀ (_v28 :
  (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v26)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v26 _v27) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2147483648 : Nat) (@instOfNatNat (2147483648 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v26 _v27) _v23) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight
  (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10 _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 :
  Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@RawPrelude.Target.Raw._proof_5 _v0 _v1 _v2 _v6 _v7 _v25)) (fun (_v28 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v22 _v13 _v12 _v15 _v17 (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0
  _v12)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Cursor.Target.W _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v28)))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v27))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))))))))))))))))) (@Exists.{(0 + 1)} (@Nat)
  (fun (_v26 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@And (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v32 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v31)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v12) (@And (@Eq.{(0 + 1)} (@Nat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v32 _v12) _v33)) (@And (@Eq.{(0 + 1)} (@Nat) _v26 (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@Eq.{(0 +
  1)} (@Nat) _v27 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v31) _v32) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v28 _v17) (@And (@Eq.{(0 + 1)} (@Nat) _v29 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v33 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v31) _v17) (@And (@Eq.{(0 + 1)} (@Nat) _v26
  (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@Eq.{(0 + 1)} (@Nat) _v27 _v17) (@And (@Eq.{(0 + 1)} (@Nat)
  _v28 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v29 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v30 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v31 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v31) _v17) (@And (@Eq.{(0 + 1)} (@Nat) _v26 _v17) (@And (@Eq.{(0 +
  1)} (@Nat) _v27 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v28 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v29 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v30 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0)) _v32)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v26 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v31) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v27 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) _v32) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v28 _v17) (@And (@Eq.{(0 + 1)} (@Nat) _v29 _v32) (@Eq.{(0 + 1)} (@Nat) _v30
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v31 _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (798 : Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@RawPrelude.Target.Raw._proof_5 _v0
  _v1 _v2 _v6 _v7 _v25)) (fun (_v32 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v22 _v13 _v12 _v15 _v17 _v26 _v27 _v28 _v29 _v30 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v32)))))) (@And (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v31)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (798 : Nat)
  (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v15 _v14) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (18 : Nat) (@instOfNatNat (18 : Nat))) _v17))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))) _v12)) (@OfNat.ofNat.{0} (@Nat) (44 : Nat) (@instOfNatNat (44 : Nat))))) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2147483648 : Nat) (@instOfNatNat (2147483648 : Nat))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v15 _v14) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (18 : Nat) (@instOfNatNat (18 : Nat))) _v17)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) _v12))
  (@OfNat.ofNat.{0} (@Nat) (44 : Nat) (@instOfNatNat (44 : Nat))))) _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@RawPrelude.Target.Raw._proof_3))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v8) (fun (_v32 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Cursor.Target.image _v19 _v0 _v9 _v12 _v7 _v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v32)))))) (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v15 _v14)
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (18 : Nat)
  (@instOfNatNat (18 : Nat))) _v17)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) _v12)) (@OfNat.ofNat.{0} (@Nat) (44 : Nat) (@instOfNatNat
  (44 : Nat))))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine
  _v0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @RawPrelude.accepted_prelude

-- Independent literal expected type for RepairedFrontier.Target.Frontier.
noncomputable def PartACanonical.Types.p0631 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RepairedFrontier.Target.Frontier

-- Independent literal expected type for RepairedFrontier.Target.ProducerEntry.
noncomputable def PartACanonical.Types.p0632 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RepairedFrontier.Target.ProducerEntry

-- Independent literal expected type for RepairedFrontier.Target.RawWords.
noncomputable def PartACanonical.Types.p0633 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RepairedFrontier.Target.RawWords

-- Independent literal expected type for RepairedFrontier.early_reject_sound.
noncomputable def PartACanonical.Types.p0634 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@IngressRepair.machine _v0)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v5)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))) := by
  exact @RepairedFrontier.early_reject_sound

-- Complete literal proposition for RepairedFrontier.early_reject_sound; original proof reused.
theorem PartACanonical.Surface.m0379 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@IngressRepair.machine _v0)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v5)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))) := by
  exact @RepairedFrontier.early_reject_sound

-- Independent literal expected type for RepairedFrontier.producer_entry.
noncomputable def PartACanonical.Types.p0635 :
(∀ (_v0 : (@Nat)),
(@RepairedFrontier.Target.ProducerEntry _v0)) := by
  exact @RepairedFrontier.producer_entry

-- Complete literal proposition for RepairedFrontier.producer_entry; original proof reused.
theorem PartACanonical.Surface.m0380 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v6 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@IngressRepair.machine _v0))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Cursor.machine _v0))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v6)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@IngressRepair.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Cursor.machine _v0))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@IngressRepair.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (∀ (_v7 : (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@IngressRepair.machine _v0)))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false))))))))))))))) := by
  exact @RepairedFrontier.producer_entry

-- Independent literal expected type for RepairedFrontier.supported_producer.
noncomputable def PartACanonical.Types.p0636 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v2 _v3)) (@Option.some.{0} (@Nat) _v4))),
(∀ (_v7 : (@Or (@Eq.{(0 + 1)} (@Nat) _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SmallIngress.producer))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SmallIngress.producer))))))))))))))) := by
  exact @RepairedFrontier.supported_producer

-- Complete literal proposition for RepairedFrontier.supported_producer; original proof reused.
theorem PartACanonical.Surface.m0381 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v2 _v3)) (@Option.some.{0} (@Nat) _v4))),
(∀ (_v7 : (@Or (@Eq.{(0 + 1)} (@Nat) _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SmallIngress.producer))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SmallIngress.producer))))))))))))))) := by
  exact @RepairedFrontier.supported_producer

-- Independent literal expected type for RuntimeBitLength.Target.FullRaw.
noncomputable def PartACanonical.Types.p0637 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RuntimeBitLength.Target.FullRaw

-- Independent literal expected type for RuntimeBitLength.Target.Raw.
noncomputable def PartACanonical.Types.p0638 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RuntimeBitLength.Target.Raw

-- Independent literal expected type for RuntimeBitLength.Target.fullImage.
noncomputable def PartACanonical.Types.p0639 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))))))) := by
  exact @RuntimeBitLength.Target.fullImage

-- Independent literal expected type for RuntimeBitLength.Target.fullImage.eq_1.
noncomputable def PartACanonical.Types.p0640 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@RuntimeBitLength.Target.fullImage _v0 _v1 _v2 _v3 _v4 _v5) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v1 _v5)
  (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))))) (@Nat.decLt _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat)
  (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@Nat.decLe _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))))))) (@Nat.decLt _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v2))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat)
  (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0}
  (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat)
  (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Nat.decLe _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0}
  (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LE.le.{0} (@Nat)
  (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2) _v4)))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LE.le.{0} (@Nat)
  (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2) _v4))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Nat.decLe _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@Pnp4.Frontier.ContractExpansion.bitLength _v2) _v4)))) (@Option.some.{0} (@Bool) (@Bool.true))
  (@_v0 _v5))))))))))) := by
  exact @RuntimeBitLength.Target.fullImage.eq_1

-- Complete literal proposition for RuntimeBitLength.Target.fullImage.eq_1; original proof reused.
theorem PartACanonical.Surface.m0382 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@RuntimeBitLength.Target.fullImage _v0 _v1 _v2 _v3 _v4 _v5) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v1 _v5)
  (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))))) (@Nat.decLt _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat)
  (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@Nat.decLe _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2)) (@And (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))))))) (@Nat.decLt _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v2))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat)
  (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0}
  (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat)
  (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Nat.decLe _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0}
  (@Nat) (@Nat.instDiv)) _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LE.le.{0} (@Nat)
  (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2) _v4)))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LE.le.{0} (@Nat)
  (@instLENat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v2) _v4))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Nat.decLe _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@Pnp4.Frontier.ContractExpansion.bitLength _v2) _v4)))) (@Option.some.{0} (@Bool) (@Bool.true))
  (@_v0 _v5))))))))))) := by
  exact @RuntimeBitLength.Target.fullImage.eq_1

-- Independent literal expected type for RuntimeBitLength.Target.image.
noncomputable def PartACanonical.Types.p0641 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))))))) := by
  exact @RuntimeBitLength.Target.image

-- Independent literal expected type for RuntimeBitLength.halve.
noncomputable def PartACanonical.Types.p0642 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v6)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v14) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v16)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v16) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v17) (@Option.none.{0} (@Bool))))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v20) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v22) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v23 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v24 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v26 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v26 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v26 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v27 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@RuntimeBitLength.halve._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v9 _v10 _v25 _v27)))) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v27))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (254 : Nat) (@instOfNatNat (254 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v27 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@RuntimeBitLength.halve._proof_2 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v9 _v10 _v25 _v27)))) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@RuntimeBitLength.Target.image _v8 _v3 _v4 _v6 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v27)))))
  (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v26)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v27 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v29 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@RuntimeBitLength.halve._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v9 _v10 _v25 _v29)))) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v29))))))) (@OfNat.ofNat.{0} (@Nat) (254 : Nat)
  (@instOfNatNat (254 : Nat)))))))))))))))))))))))))))))))))))) := by
  exact @RuntimeBitLength.halve

-- Complete literal proposition for RuntimeBitLength.halve; original proof reused.
theorem PartACanonical.Surface.m0383 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v6)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v14) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v16)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v16) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v17) (@Option.none.{0} (@Bool))))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v20) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v22) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v23 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v24 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v26 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v26 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v26 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v27 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@RuntimeBitLength.halve._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v9 _v10 _v25 _v27)))) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v27))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (254 : Nat) (@instOfNatNat (254 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v27 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@RuntimeBitLength.halve._proof_2 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v9 _v10 _v25 _v27)))) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@RuntimeBitLength.Target.image _v8 _v3 _v4 _v6 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v27)))))
  (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v26)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v27 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v29 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@RuntimeBitLength.halve._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v9 _v10 _v25 _v29)))) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v29))))))) (@OfNat.ofNat.{0} (@Nat) (254 : Nat)
  (@instOfNatNat (254 : Nat)))))))))))))))))))))))))))))))))))) := by
  exact @RuntimeBitLength.halve

-- Independent literal expected type for RuntimeBitLength.instructions.
noncomputable def PartACanonical.Types.p0643 :
(@List.{0} (@Nat)) := by
  exact @RuntimeBitLength.instructions

-- Independent literal expected type for RuntimeBitLength.raw_accepted_half.
noncomputable def PartACanonical.Types.p0645 :
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
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2097152 : Nat) (@instOfNatNat (2097152 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v11 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))) (@And (∀ (_v14
  : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))))) (@And (∀
  (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (254 : Nat) (@instOfNatNat (254 : Nat))))))))) (let _v14 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2);
(let _v15 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6));
(let _v16 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v17 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v14 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15)) _v14));
(let _v18 : (∀ (_v18 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v15) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15));
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v18 _v14 _v9 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) (@Bool.false));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v19 _v16 _v17) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v14 _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15 _v16 _v17);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v16 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v17)) _v15) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (254 : Nat) (@instOfNatNat (254 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v16 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) _v13) (fun (_v21 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@RuntimeBitLength.Target.image _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v9) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v15 _v16 _v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v21))))))))))))))))))))))))))))))))))))))) := by
  exact @RuntimeBitLength.raw_accepted_half

-- Complete literal proposition for RuntimeBitLength.raw_accepted_half; original proof reused.
theorem PartACanonical.Surface.m0385 :
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
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2097152 : Nat) (@instOfNatNat (2097152 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v11 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))) (@And (∀ (_v14
  : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))))) (@And (∀
  (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (254 : Nat) (@instOfNatNat (254 : Nat))))))))) (let _v14 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2);
(let _v15 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6));
(let _v16 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v17 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v14 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15)) _v14));
(let _v18 : (∀ (_v18 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v15) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15));
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v18 _v14 _v9 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) (@Bool.false));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v19 _v16 _v17) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v14 _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15 _v16 _v17);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v16 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v17)) _v15) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (254 : Nat) (@instOfNatNat (254 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v16 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) _v13) (fun (_v21 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@RuntimeBitLength.Target.image _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v9) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v15 _v16 _v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v21))))))))))))))))))))))))))))))))))))))) := by
  exact @RuntimeBitLength.raw_accepted_half

-- Independent literal expected type for RuntimeBitLength.raw_half.
noncomputable def PartACanonical.Types.p0646 :
(∀ (_v0 : (@Nat)),
(@RuntimeBitLength.Target.Raw _v0)) := by
  exact @RuntimeBitLength.raw_half

-- Complete literal proposition for RuntimeBitLength.raw_half; original proof reused.
theorem PartACanonical.Surface.m0386 :
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
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2097152 : Nat) (@instOfNatNat (2097152 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v14 _v15) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v14 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))) (@And (∀ (_v17
  : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v14)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v17 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))))) (@And (∀
  (_v17 : (@Nat)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v17 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (254 : Nat) (@instOfNatNat (254 : Nat))))))))) (let _v17 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2);
(let _v18 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5));
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v18)) _v17));
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v18) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v18));
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v21 _v17 _v9 _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v18) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v18) (@Bool.false));
(let _v23 : (∀ (_v23 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v22 _v19 _v20) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v17 _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v18 _v19 _v20);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v20)) _v18) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v15 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (254 : Nat) (@instOfNatNat (254 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) _v16) (fun (_v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@RuntimeBitLength.Target.image _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v9) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v18 _v19 _v20 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v24)))))))))))))))))))))))))))))))))))))))))) := by
  exact @RuntimeBitLength.raw_half

-- Independent literal expected type for SerializedBody.Target.Body.
noncomputable def PartACanonical.Types.p0647 :
(Sort 0) := by
  exact @SerializedBody.Target.Body

-- Independent literal expected type for SerializedBody.delimiter.
noncomputable def PartACanonical.Types.p0648 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Nat))))) := by
  exact @SerializedBody.delimiter

-- Independent literal expected type for SerializedBody.delimiter.eq_1.
noncomputable def PartACanonical.Types.p0649 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_1

-- Complete literal proposition for SerializedBody.delimiter.eq_1; original proof reused.
theorem PartACanonical.Surface.m0387 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_1

-- Independent literal expected type for SerializedBody.delimiter.eq_10.
noncomputable def PartACanonical.Types.p0650 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_10

-- Complete literal proposition for SerializedBody.delimiter.eq_10; original proof reused.
theorem PartACanonical.Surface.m0388 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_10

-- Independent literal expected type for SerializedBody.delimiter.eq_11.
noncomputable def PartACanonical.Types.p0651 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_11

-- Complete literal proposition for SerializedBody.delimiter.eq_11; original proof reused.
theorem PartACanonical.Surface.m0389 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_11

-- Independent literal expected type for SerializedBody.delimiter.eq_12.
noncomputable def PartACanonical.Types.p0652 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (15 : Nat)
  (@instOfNatNat (15 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_12

-- Complete literal proposition for SerializedBody.delimiter.eq_12; original proof reused.
theorem PartACanonical.Surface.m0390 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (15 : Nat)
  (@instOfNatNat (15 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_12

-- Independent literal expected type for SerializedBody.delimiter.eq_13.
noncomputable def PartACanonical.Types.p0653 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@False))),
(∀ (_v5 : (∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))),
(@False))),
(∀ (_v6 : (∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))),
(@False))),
(∀ (_v7 : (∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@False))),
(∀ (_v8 : (∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))),
(@False))),
(∀ (_v9 : (∀ (_v9 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))),
(@False))),
(∀ (_v10 : (∀ (_v10 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@False))),
(∀ (_v11 : (∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))),
(@False))),
(∀ (_v12 : (∀ (_v12 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))),
(@False))),
(∀ (_v13 : (∀ (_v13 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(@False))),
(∀ (_v14 : (∀ (_v14 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))),
(@False))),
(∀ (_v15 : (∀ (_v15 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))),
(@False))),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))))))))))))))))))) := by
  exact @SerializedBody.delimiter.eq_13

-- Complete literal proposition for SerializedBody.delimiter.eq_13; original proof reused.
theorem PartACanonical.Surface.m0391 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@False))),
(∀ (_v5 : (∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))),
(@False))),
(∀ (_v6 : (∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))),
(@False))),
(∀ (_v7 : (∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@False))),
(∀ (_v8 : (∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))),
(@False))),
(∀ (_v9 : (∀ (_v9 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))),
(@False))),
(∀ (_v10 : (∀ (_v10 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@False))),
(∀ (_v11 : (∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))),
(@False))),
(∀ (_v12 : (∀ (_v12 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))),
(@False))),
(∀ (_v13 : (∀ (_v13 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(@False))),
(∀ (_v14 : (∀ (_v14 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))),
(@False))),
(∀ (_v15 : (∀ (_v15 : (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))),
(@False))),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))))))))))))))))))) := by
  exact @SerializedBody.delimiter.eq_13

-- Independent literal expected type for SerializedBody.delimiter.eq_2.
noncomputable def PartACanonical.Types.p0654 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_2

-- Complete literal proposition for SerializedBody.delimiter.eq_2; original proof reused.
theorem PartACanonical.Surface.m0392 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_2

-- Independent literal expected type for SerializedBody.delimiter.eq_3.
noncomputable def PartACanonical.Types.p0655 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_3

-- Complete literal proposition for SerializedBody.delimiter.eq_3; original proof reused.
theorem PartACanonical.Surface.m0393 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_3

-- Independent literal expected type for SerializedBody.delimiter.eq_4.
noncomputable def PartACanonical.Types.p0656 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_4

-- Complete literal proposition for SerializedBody.delimiter.eq_4; original proof reused.
theorem PartACanonical.Surface.m0394 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_4

-- Independent literal expected type for SerializedBody.delimiter.eq_5.
noncomputable def PartACanonical.Types.p0657 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_5

-- Complete literal proposition for SerializedBody.delimiter.eq_5; original proof reused.
theorem PartACanonical.Surface.m0395 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_5

-- Independent literal expected type for SerializedBody.delimiter.eq_6.
noncomputable def PartACanonical.Types.p0658 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_6

-- Complete literal proposition for SerializedBody.delimiter.eq_6; original proof reused.
theorem PartACanonical.Surface.m0396 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_6

-- Independent literal expected type for SerializedBody.delimiter.eq_7.
noncomputable def PartACanonical.Types.p0659 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_7

-- Complete literal proposition for SerializedBody.delimiter.eq_7; original proof reused.
theorem PartACanonical.Surface.m0397 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_7

-- Independent literal expected type for SerializedBody.delimiter.eq_8.
noncomputable def PartACanonical.Types.p0660 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_8

-- Complete literal proposition for SerializedBody.delimiter.eq_8; original proof reused.
theorem PartACanonical.Surface.m0398 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_8

-- Independent literal expected type for SerializedBody.delimiter.eq_9.
noncomputable def PartACanonical.Types.p0661 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_9

-- Complete literal proposition for SerializedBody.delimiter.eq_9; original proof reused.
theorem PartACanonical.Surface.m0399 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@SerializedBody.delimiter _v0 _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v1)) _v2) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))))))) := by
  exact @SerializedBody.delimiter.eq_9

-- Independent literal expected type for SerializedBody.done.
noncomputable def PartACanonical.Types.p0662 :
(∀ (_v0 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))) := by
  exact @SerializedBody.done

-- Independent literal expected type for SerializedBody.entry.
noncomputable def PartACanonical.Types.p0663 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))) := by
  exact @SerializedBody.entry

-- Independent literal expected type for SerializedBody.image.
noncomputable def PartACanonical.Types.p0664 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(@Option.{0} (@Bool)))))))))))))) := by
  exact @SerializedBody.image

-- Independent literal expected type for SerializedBody.image.eq_1.
noncomputable def PartACanonical.Types.p0665 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11))
  (@instDecidableOr (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1
  _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11)) (@_v0 _v11) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat
  (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) _v4))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v3)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@Pnp4.Frontier.ContractExpansion.bitLength _v3)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) _v5))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v7) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat))))) _v7))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Option.some.{0}
  (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v10))) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v8)
  (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v8)))))))))))))))))))))))))))) := by
  exact @SerializedBody.image.eq_1

-- Complete literal proposition for SerializedBody.image.eq_1; original proof reused.
theorem PartACanonical.Surface.m0400 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11))
  (@instDecidableOr (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1
  _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11)) (@_v0 _v11) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat
  (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) _v4))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v3)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@Pnp4.Frontier.ContractExpansion.bitLength _v3)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) _v5))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v7) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat))))) _v7))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Option.some.{0}
  (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v10))) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v8)
  (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v8)))))))))))))))))))))))))))) := by
  exact @SerializedBody.image.eq_1

-- Independent literal expected type for SerializedBody.machine.
noncomputable def PartACanonical.Types.p0666 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @SerializedBody.machine

-- Independent literal expected type for SerializedBody.prepared.
noncomputable def PartACanonical.Types.p0667 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool))))))))))) := by
  exact @SerializedBody.prepared

-- Independent literal expected type for SerializedBody.prepared.eq_1.
noncomputable def PartACanonical.Types.p0668 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 _v2) (@Nat.decLt _v8
  _v1)) (@Option.none.{0} (@Bool)) (@SerializedBody.image _v0 _v3 _v4 _v5 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v2 _v1)) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7 _v6
  _v8)))))))))))) := by
  exact @SerializedBody.prepared.eq_1

-- Complete literal proposition for SerializedBody.prepared.eq_1; original proof reused.
theorem PartACanonical.Surface.m0401 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 _v2) (@Nat.decLt _v8
  _v1)) (@Option.none.{0} (@Bool)) (@SerializedBody.image _v0 _v3 _v4 _v5 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v2 _v1)) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7 _v6
  _v8)))))))))))) := by
  exact @SerializedBody.prepared.eq_1

-- Independent literal expected type for SerializedBody.sourceMode.
noncomputable def PartACanonical.Types.p0669 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) := by
  exact @SerializedBody.sourceMode

-- Independent literal expected type for SerializedBody.sourceMode.eq_1.
noncomputable def PartACanonical.Types.p0670 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@SerializedBody.sourceMode _v0 _v1
  _v2) (@dite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v2 _v0) (@Nat.decLt _v2 _v0) (fun (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v0)) =>
(@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Bool) (@_v1
  (@Fin.mk _v0 _v2 _v3)) (@Bool.true)) (@instDecidableEqBool (@_v1 (@Fin.mk _v0 _v2 _v3)) (@Bool.true)) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))) (@SerializedBody.sourceMode._proof_1)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@SerializedBody.sourceMode._proof_2)))) (fun (_v3 : (@Not
  (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v0))) =>
(@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))) (@SerializedBody.sourceMode._proof_3)))))))) := by
  exact @SerializedBody.sourceMode.eq_1

-- Complete literal proposition for SerializedBody.sourceMode.eq_1; original proof reused.
theorem PartACanonical.Surface.m0402 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@SerializedBody.sourceMode _v0 _v1
  _v2) (@dite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v2 _v0) (@Nat.decLt _v2 _v0) (fun (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v0)) =>
(@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Bool) (@_v1
  (@Fin.mk _v0 _v2 _v3)) (@Bool.true)) (@instDecidableEqBool (@_v1 (@Fin.mk _v0 _v2 _v3)) (@Bool.true)) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))) (@SerializedBody.sourceMode._proof_1)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@SerializedBody.sourceMode._proof_2)))) (fun (_v3 : (@Not
  (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v0))) =>
(@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))) (@SerializedBody.sourceMode._proof_3)))))))) := by
  exact @SerializedBody.sourceMode.eq_1

-- Independent literal expected type for SerializedBody.window.
noncomputable def PartACanonical.Types.p0671 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@List.{0} (@Bool)))))) := by
  exact @SerializedBody.window

-- Independent literal expected type for SerializedBody.window.eq_1.
noncomputable def PartACanonical.Types.p0672 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@SerializedBody.window _v0 _v1 _v2 _v3) (@List.ofFn.{0} (@Bool) _v3 (fun (_v4 :
  (@Fin _v3)) =>
(@Pnp4.Frontier.ContractExpansion.padRead _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@Fin.val _v3 _v4)))))))))) := by
  exact @SerializedBody.window.eq_1

-- Complete literal proposition for SerializedBody.window.eq_1; original proof reused.
theorem PartACanonical.Surface.m0403 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@SerializedBody.window _v0 _v1 _v2 _v3) (@List.ofFn.{0} (@Bool) _v3 (fun (_v4 :
  (@Fin _v3)) =>
(@Pnp4.Frontier.ContractExpansion.padRead _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@Fin.val _v3 _v4)))))))))) := by
  exact @SerializedBody.window.eq_1

-- Independent literal expected type for SerializedBodyCompletion.abort_cleanup.
noncomputable def PartACanonical.Types.p0673 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v24) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.abort_cleanup

-- Complete literal proposition for SerializedBodyCompletion.abort_cleanup; original proof reused.
theorem PartACanonical.Surface.m0404 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v24) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.abort_cleanup

-- Independent literal expected type for SerializedBodyCompletion.abort_cleanup_mirror.
noncomputable def PartACanonical.Types.p0674 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v24) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.abort_cleanup_mirror

-- Complete literal proposition for SerializedBodyCompletion.abort_cleanup_mirror; original proof reused.
theorem PartACanonical.Surface.m0405 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v24) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.abort_cleanup_mirror

-- Independent literal expected type for SerializedBodyCompletion.entry_need.
noncomputable def PartACanonical.Types.p0675 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v4)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v16)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v16) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v17) (@Option.none.{0} (@Bool))))))),
(let _v18 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6 (@SerializedBody.entry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v2 _v12) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v18))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2)
  _v18) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v13) (fun (_v19 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v19))))) (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v5 _v6
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6 _v19 _v18)))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.entry_need

-- Complete literal proposition for SerializedBodyCompletion.entry_need; original proof reused.
theorem PartACanonical.Surface.m0406 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v4)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v16)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v16) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v17) (@Option.none.{0} (@Bool))))))),
(let _v18 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6 (@SerializedBody.entry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v2 _v12) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v18))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2)
  _v18) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v13) (fun (_v19 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v19))))) (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v5 _v6
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6 _v19 _v18)))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.entry_need

-- Independent literal expected type for SerializedBodyCompletion.entry_need_mirror.
noncomputable def PartACanonical.Types.p0676 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v4)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v16)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v16) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v17) (@Option.none.{0} (@Bool))))))),
(let _v18 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6 (@SerializedBody.entry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v2 _v12) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v18))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2)
  _v18) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v13) (fun (_v19 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v19))))) (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v5 _v6
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6 _v19 _v18)))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.entry_need_mirror

-- Complete literal proposition for SerializedBodyCompletion.entry_need_mirror; original proof reused.
theorem PartACanonical.Surface.m0407 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v4)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v16)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v16) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v17) (@Option.none.{0} (@Bool))))))),
(let _v18 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v5
  _v6 (@SerializedBody.entry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v2 _v12) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v18))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2)
  _v18) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v5 _v6 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v13) (fun (_v19 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v5 _v6) _v19))))) (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v5 _v6
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v5 _v6 _v19 _v18)))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.entry_need_mirror

-- Independent literal expected type for SerializedBodyCompletion.exhausted_consumer.
noncomputable def PartACanonical.Types.p0677 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Fin _v3)),
(@Bool))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v21) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v22 _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v22) (@_v1 _v23))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v23)) (@Option.none.{0} (@Bool)))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v24) _v25)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v24 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v29 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v25) (@Option.some.{0} (@Bool) _v29)))))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v13)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v40 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.some.{0} (@Bool) _v40)))))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v38)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v41 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v38) (@Option.some.{0} (@Bool) _v41)))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v39)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v40) (@Option.none.{0} (@Bool))))))),
(∀ (_v41 : (∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v10) (@Option.none.{0} (@Bool))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v42)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v42) (@Option.some.{0} (@Bool) (@_v14 (@Fin.mk _v3 _v42 _v44)))))))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v43)
  (@Nat.decLt _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v14 _v10)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v31) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v5 _v32) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v11 _v12))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3) (@Nat.decLt _v10 _v3) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v14 _v10)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11
  _v12) _v46))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46)))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LT.lt.{0} (@Nat) (@instLTNat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.exhausted_consumer

-- Complete literal proposition for SerializedBodyCompletion.exhausted_consumer; original proof reused.
theorem PartACanonical.Surface.m0408 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Fin _v3)),
(@Bool))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v21) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v22 _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v22) (@_v1 _v23))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v23)) (@Option.none.{0} (@Bool)))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v24) _v25)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v24 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v29 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v25) (@Option.some.{0} (@Bool) _v29)))))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v13)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v40 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.some.{0} (@Bool) _v40)))))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v38)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v41 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v38) (@Option.some.{0} (@Bool) _v41)))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v39)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v40) (@Option.none.{0} (@Bool))))))),
(∀ (_v41 : (∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v10) (@Option.none.{0} (@Bool))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v42)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v42) (@Option.some.{0} (@Bool) (@_v14 (@Fin.mk _v3 _v42 _v44)))))))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v43)
  (@Nat.decLt _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v14 _v10)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v31) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v5 _v32) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v11 _v12))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3) (@Nat.decLt _v10 _v3) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v14 _v10)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11
  _v12) _v46))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46)))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LT.lt.{0} (@Nat) (@instLTNat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.exhausted_consumer

-- Independent literal expected type for SerializedBodyCompletion.exhausted_consumer_mirror.
noncomputable def PartACanonical.Types.p0678 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Fin _v3)),
(@Bool))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v21) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v22 _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v22) (@_v1 _v23))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v23)) (@Option.none.{0} (@Bool)))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v24) _v25)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v24 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v29 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v25) (@Option.some.{0} (@Bool) _v29)))))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v13)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v40 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.some.{0} (@Bool) _v40)))))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v38)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v41 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v38) (@Option.some.{0} (@Bool) _v41)))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v39)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v40) (@Option.none.{0} (@Bool))))))),
(∀ (_v41 : (∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v10) (@Option.none.{0} (@Bool))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v42)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v42) (@Option.some.{0} (@Bool) (@_v14 (@Fin.mk _v3 _v42 _v44)))))))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v43)
  (@Nat.decLt _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v14 _v10)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v31) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v5 _v32) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v11 _v12))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3) (@Nat.decLt _v10 _v3) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v14 _v10)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11
  _v12) _v46))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46)))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LT.lt.{0} (@Nat) (@instLTNat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.exhausted_consumer_mirror

-- Complete literal proposition for SerializedBodyCompletion.exhausted_consumer_mirror; original proof reused.
theorem PartACanonical.Surface.m0409 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Fin _v3)),
(@Bool))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v21) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v22 _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v22) (@_v1 _v23))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v23)) (@Option.none.{0} (@Bool)))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v24) _v25)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v24 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v29 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v25) (@Option.some.{0} (@Bool) _v29)))))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v13)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v40 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.some.{0} (@Bool) _v40)))))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v38)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v41 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v38) (@Option.some.{0} (@Bool) _v41)))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v39)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v40) (@Option.none.{0} (@Bool))))))),
(∀ (_v41 : (∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v10) (@Option.none.{0} (@Bool))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v42)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v42) (@Option.some.{0} (@Bool) (@_v14 (@Fin.mk _v3 _v42 _v44)))))))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v1 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v43)
  (@Nat.decLt _v43 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v44 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat) (@instLTNat) _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v44) _v43) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v43 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v1 _v44) _v43) (@Nat.decLt _v43 (@_v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v14 _v10)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v31) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v5 _v32) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v11 _v12))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v3) (@Nat.decLt _v10 _v3) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46) _v10) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v14 _v10)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11
  _v12) _v46))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v46)))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LT.lt.{0} (@Nat) (@instLTNat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.exhausted_consumer_mirror

-- Independent literal expected type for SerializedBodyCompletion.image_equation_mirror.
noncomputable def PartACanonical.Types.p0679 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11))
  (@instDecidableOr (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1
  _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11)) (@_v0 _v11) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat
  (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) _v4))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v3)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@Pnp4.Frontier.ContractExpansion.bitLength _v3)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) _v5))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v7) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat))))) _v7))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Option.some.{0}
  (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v10))) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v8)
  (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v8)))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.image_equation_mirror

-- Complete literal proposition for SerializedBodyCompletion.image_equation_mirror; original proof reused.
theorem PartACanonical.Surface.m0410 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11))
  (@instDecidableOr (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1
  _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v11)) (@_v0 _v11) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat
  (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.range (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat)))) (fun (_v12 : (@Nat)) =>
(@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 _v12)))) (@Bool.true)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) _v4))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v3)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@Pnp4.Frontier.ContractExpansion.bitLength _v3)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) _v5))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter
  _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v7) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat))))) _v7))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Option.some.{0}
  (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v10))) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0}
  (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6) (@Nat.decLe
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@SerializedBody.delimiter _v1 _v2
  _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) _v6))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt _v11 (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v8)
  (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11
  (@SerializedBody.delimiter _v1 _v2 _v3 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v8)))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.image_equation_mirror

-- Independent literal expected type for SerializedBodyCompletion.needEntry.
noncomputable def PartACanonical.Types.p0680 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))) := by
  exact @SerializedBodyCompletion.needEntry

-- Independent literal expected type for SerializedBodyCompletion.need_get.
noncomputable def PartACanonical.Types.p0681 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v9) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v11)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v10) (@_v1 _v11))))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v11)) (@Option.none.{0} (@Bool)))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v12) _v13)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v13) (@Option.some.{0} (@Bool) _v17)))))))))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v8)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v3)),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v20) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  _v4)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v21) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v5)))))))),
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15) (fun (_v23 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v23))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v22 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v22
  _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7 (@SerializedBodyRefinement.getEntry (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0}
  (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v15) (fun (_v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7)
  _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24))))))) (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v24 _v23)))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.need_get

-- Complete literal proposition for SerializedBodyCompletion.need_get; original proof reused.
theorem PartACanonical.Surface.m0411 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v9) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v11)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v10) (@_v1 _v11))))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v11)) (@Option.none.{0} (@Bool)))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v12) _v13)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v13) (@Option.some.{0} (@Bool) _v17)))))))))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v8)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v3)),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v20) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  _v4)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v21) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v5)))))))),
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15) (fun (_v23 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v23))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v22 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v22
  _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7 (@SerializedBodyRefinement.getEntry (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0}
  (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v15) (fun (_v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7)
  _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24))))))) (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v24 _v23)))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.need_get

-- Independent literal expected type for SerializedBodyCompletion.need_get_mirror.
noncomputable def PartACanonical.Types.p0682 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v9) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v11)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v10) (@_v1 _v11))))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v11)) (@Option.none.{0} (@Bool)))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v12) _v13)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v13) (@Option.some.{0} (@Bool) _v17)))))))))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v8)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v3)),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v20) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  _v4)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v21) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v5)))))))),
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15) (fun (_v23 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v23))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v22 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v22
  _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7 (@SerializedBodyRefinement.getEntry (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0}
  (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v15) (fun (_v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7)
  _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24))))))) (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v24 _v23)))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.need_get_mirror

-- Complete literal proposition for SerializedBodyCompletion.need_get_mirror; original proof reused.
theorem PartACanonical.Surface.m0412 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v9) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v11)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v10) (@_v1 _v11))))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v11)) (@Option.none.{0} (@Bool)))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v12) _v13)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v13) (@Option.some.{0} (@Bool) _v17)))))))))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v8)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v3)),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v20) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v4) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  _v4)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v21) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v5)))))))),
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v6
  _v7 (@SerializedBodyCompletion.needEntry _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15) (fun (_v23 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v23))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v22 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v22
  _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v6 _v7 (@SerializedBodyRefinement.getEntry (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0}
  (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v15) (fun (_v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7)
  _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v6 _v7) _v24))))))) (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v6 _v7 _v24 _v23)))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.need_get_mirror

-- Independent literal expected type for SerializedBodyCompletion.prepared_equation_mirror.
noncomputable def PartACanonical.Types.p0683 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 _v2) (@Nat.decLt _v8
  _v1)) (@Option.none.{0} (@Bool)) (@SerializedBody.image _v0 _v3 _v4 _v5 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v2 _v1)) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7 _v6
  _v8)))))))))))) := by
  exact @SerializedBodyCompletion.prepared_equation_mirror

-- Complete literal proposition for SerializedBodyCompletion.prepared_equation_mirror; original proof reused.
theorem PartACanonical.Surface.m0413 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SerializedBody.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) _v8 _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 _v2) (@Nat.decLt _v8
  _v1)) (@Option.none.{0} (@Bool)) (@SerializedBody.image _v0 _v3 _v4 _v5 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v2 _v1)) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7 _v6
  _v8)))))))))))) := by
  exact @SerializedBodyCompletion.prepared_equation_mirror

-- Independent literal expected type for SerializedBodyCompletion.zero_quota_body_mirror.
noncomputable def PartACanonical.Types.p0685 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Fin _v1)),
(@Bool))),
(∀ (_v9 : (∀ (_v9 : (@Fin _v3)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v6 _v1)) _v4)),
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v20)),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@_v8 (@Fin.mk _v1 _v23 _v25)))))))),
(∀ (_v24 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v18)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v25) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v18) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v19 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v27))) (@Option.some.{0} (@Bool) (@_v9 _v27))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v29)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v29) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v30) (@Option.none.{0} (@Bool))))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(let _v34 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v8 _v6 _v5);
(let _v35 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v8 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun
  (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.prepared _v10 _v1 _v6 _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v35))));
(let _v36 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v34) (fun
  (_v36 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@SerializedBodyCompletion.zero_quota_body_mirror.match_1.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v36 (fun (_v37 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v38 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v37)
  (@Pnp3.Models.Circuit.eval _v3 _v37 _v9)) _v38)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LE.le.{0} (@Nat) (@instLENat) _v38 _v37)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body_mirror.match_3.{(0 + 1)} (fun (_v38 : (@Option.{0}
  (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v36 (fun (_v38 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37
  _v35) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun (_v39 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v39)))))) (fun
  (_v38 : (@Nat)) =>
(fun (_v39 : (@Bool)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v41 _v5) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v40 (@List.drop.{0} (@Bool)
  _v41 _v34)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37
  _v35) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17 (@SerializedBody.done _v39) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v17) _v19 _v33) (fun (_v42 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) _v38 _v41 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v5 _v41) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v42))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_quota_body_mirror

-- Complete literal proposition for SerializedBodyCompletion.zero_quota_body_mirror; original proof reused.
theorem PartACanonical.Surface.m0415 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Fin _v1)),
(@Bool))),
(∀ (_v9 : (∀ (_v9 : (@Fin _v3)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v6 _v1)) _v4)),
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v20)),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@_v8 (@Fin.mk _v1 _v23 _v25)))))))),
(∀ (_v24 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v18)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v25) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v18) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v19 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v27))) (@Option.some.{0} (@Bool) (@_v9 _v27))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v29)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v29) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v30) (@Option.none.{0} (@Bool))))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(let _v34 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v8 _v6 _v5);
(let _v35 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v8 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun
  (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.prepared _v10 _v1 _v6 _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v35))));
(let _v36 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v34) (fun
  (_v36 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@SerializedBodyCompletion.zero_quota_body_mirror.match_1.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v36 (fun (_v37 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v38 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v37)
  (@Pnp3.Models.Circuit.eval _v3 _v37 _v9)) _v38)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LE.le.{0} (@Nat) (@instLENat) _v38 _v37)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body_mirror.match_3.{(0 + 1)} (fun (_v38 : (@Option.{0}
  (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v36 (fun (_v38 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37
  _v35) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun (_v39 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v39)))))) (fun
  (_v38 : (@Nat)) =>
(fun (_v39 : (@Bool)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v41 _v5) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v40 (@List.drop.{0} (@Bool)
  _v41 _v34)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37
  _v35) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17 (@SerializedBody.done _v39) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v17) _v19 _v33) (fun (_v42 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) _v38 _v41 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v5 _v41) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v42))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_quota_body_mirror

-- Independent literal expected type for SerializedBodyCompletion.zero_quota_native.
noncomputable def PartACanonical.Types.p0686 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBody.entry (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9) _v4 _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v23) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_quota_native

-- Complete literal proposition for SerializedBodyCompletion.zero_quota_native; original proof reused.
theorem PartACanonical.Surface.m0416 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBody.entry (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9) _v4 _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v23) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_quota_native

-- Independent literal expected type for SerializedBodyCompletion.zero_quota_native_mirror.
noncomputable def PartACanonical.Types.p0687 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBody.entry (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9) _v4 _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v23) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_quota_native_mirror

-- Complete literal proposition for SerializedBodyCompletion.zero_quota_native_mirror; original proof reused.
theorem PartACanonical.Surface.m0417 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Nat)),
(∀ (_v11 : (∀ (_v11 : (@Fin _v2)),
(@Bool))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v17) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v18) (@_v0 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v10)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v32 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v29) (@Option.some.{0} (@Bool) _v32)))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v33 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v33)))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v7) (@Option.none.{0} (@Bool))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v2 _v34 _v36)))))))),
(let _v35 : (∀ (_v35 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v35 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@_v0 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) _v35)
  (@Nat.decLt _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Bool) (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@instDecidableEqBool (@List.any.{0} (@Nat) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@List.nil.{0} (@Nat))))))))) (fun (_v36 : (@Nat)) =>
(@Decidable.decide (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v36) _v35) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v35 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Nat.decLt (@_v0 _v36) _v35) (@Nat.decLt _v35 (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))))) (@Bool.true)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v1 _v35))));
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v8
  _v9 (@SerializedBody.entry (@SerializedBody.sourceMode _v2 _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9) _v4 _v23) (fun (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9))) =>
(@_v1 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v36))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v37
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v8 _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v4 _v23) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v8 _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2) (@Nat.decLt _v7 _v2) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38) _v7) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v11 _v7)) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8
  _v9) _v38))) (@_v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v8 _v9) _v38)))))) (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v8 _v9
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v8 _v9 _v38
  _v36))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_quota_native_mirror

-- Independent literal expected type for SerializedBodyCompletion.zero_window_body_mirror.
noncomputable def PartACanonical.Types.p0689 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Fin _v1)),
(@Bool))),
(∀ (_v9 : (∀ (_v9 : (@Fin _v3)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v6 _v1)) _v4)),
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v20)),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@_v8 (@Fin.mk _v1 _v23 _v25)))))))),
(∀ (_v24 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v18)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v25) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v18) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v19 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v27))) (@Option.some.{0} (@Bool) (@_v9 _v27))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v29)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v29) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v30) (@Option.none.{0} (@Bool))))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(let _v34 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v8 _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))));
(let _v35 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v8 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun
  (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.prepared _v10 _v1 _v6 _v20 _v4 _v3 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v35))));
(let _v36 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v34) (fun
  (_v36 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@SerializedBodyCompletion.zero_quota_body_mirror.match_1.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v36 (fun (_v37 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v38 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v37) _v5) (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v37) _v5)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v37)
  (@Pnp3.Models.Circuit.eval _v3 _v37 _v9)) _v38)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LE.le.{0} (@Nat) (@instLENat) _v38 _v37)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body_mirror.match_3.{(0 + 1)} (fun (_v38 : (@Option.{0}
  (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v36 (fun (_v38 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37
  _v35) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun (_v39 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v39)))))) (fun
  (_v38 : (@Nat)) =>
(fun (_v39 : (@Bool)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v41 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0
  + 1)} (@List.{0} (@Bool)) _v40 (@List.drop.{0} (@Bool) _v41 _v34)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37 _v35)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0
  _v17 (@SerializedBody.done _v39) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun (_v42 :
  (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) _v38 _v41 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v41) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17)
  _v42))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_window_body_mirror

-- Complete literal proposition for SerializedBodyCompletion.zero_window_body_mirror; original proof reused.
theorem PartACanonical.Surface.m0419 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Fin _v1)),
(@Bool))),
(∀ (_v9 : (∀ (_v9 : (@Fin _v3)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v6 _v1)) _v4)),
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v20)),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@_v8 (@Fin.mk _v1 _v23 _v25)))))))),
(∀ (_v24 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v18)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v25) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v18) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v19 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v27))) (@Option.some.{0} (@Bool) (@_v9 _v27))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v29)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v29) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v19 _v7) _v30)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v30) (@Option.none.{0} (@Bool))))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v20 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))),
(let _v34 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v8 _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))));
(let _v35 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v8 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun
  (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.prepared _v10 _v1 _v6 _v20 _v4 _v3 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v35))));
(let _v36 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v34) (fun
  (_v36 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@SerializedBodyCompletion.zero_quota_body_mirror.match_1.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v36 (fun (_v37 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v38 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v37) _v5) (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v37) _v5)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v37)
  (@Pnp3.Models.Circuit.eval _v3 _v37 _v9)) _v38)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LE.le.{0} (@Nat) (@instLENat) _v38 _v37)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v37)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v38 _v35)) (@SerializedBody.done
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body_mirror.match_3.{(0 + 1)} (fun (_v38 : (@Option.{0}
  (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v36 (fun (_v38 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37
  _v35) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun (_v39 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v39)))))) (fun
  (_v38 : (@Nat)) =>
(fun (_v39 : (@Bool)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v41 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v41 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0
  + 1)} (@List.{0} (@Bool)) _v40 (@List.drop.{0} (@Bool) _v41 _v34)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v17 _v37 _v35)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0
  _v17 (@SerializedBody.done _v39) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17) _v19 _v33) (fun (_v42 :
  (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17))) =>
(@SerializedBody.image _v10 _v20 _v4 _v3 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) _v6 _v1)) _v38 _v41 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v41) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v17)
  _v42))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyCompletion.zero_window_body_mirror

-- Independent literal expected type for SerializedBodyRefinement.counter_phase.
noncomputable def PartACanonical.Types.p0690 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Nat))),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4)),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v11) (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v2 _v12) (@_v2 _v13))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 (@_v2 _v13)) (@Option.none.{0} (@Bool)))))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v14) _v15)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v19 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v15) (@Option.some.{0} (@Bool) _v19)))))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v17) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v5)))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v18)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v18) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v6) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v6)))))))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v9)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(let _v22 : (@Nat) := (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))));
(let _v23 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@SerializedBodyRefinement.getAbort _v1) (@SerializedBodyRefinement.getBody _v0 _v1));
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@ite.{(0 + 1)} (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v3 (fun (_v24 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v5)) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v3 _v24)))));
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8 (@SerializedBodyRefinement.getEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v25))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v22
  _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8 _v23 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v26))))) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v26 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v7 _v8
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v26 _v25))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.counter_phase

-- Complete literal proposition for SerializedBodyRefinement.counter_phase; original proof reused.
theorem PartACanonical.Surface.m0420 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Nat))),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4)),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v11) (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v2 _v12) (@_v2 _v13))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 (@_v2 _v13)) (@Option.none.{0} (@Bool)))))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v14) _v15)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v19 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v15) (@Option.some.{0} (@Bool) _v19)))))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v17) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v5)))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v18)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v18) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v6) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v6)))))))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v9)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(let _v22 : (@Nat) := (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))));
(let _v23 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@SerializedBodyRefinement.getAbort _v1) (@SerializedBodyRefinement.getBody _v0 _v1));
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@ite.{(0 + 1)} (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v3 (fun (_v24 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v5)) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v3 _v24)))));
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8 (@SerializedBodyRefinement.getEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v25))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v22
  _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8 _v23 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v26))))) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v26 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v7 _v8
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v26 _v25))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.counter_phase

-- Independent literal expected type for SerializedBodyRefinement.counter_phase_mirror.
noncomputable def PartACanonical.Types.p0691 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Nat))),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4)),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v11) (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v2 _v12) (@_v2 _v13))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 (@_v2 _v13)) (@Option.none.{0} (@Bool)))))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v14) _v15)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v19 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v15) (@Option.some.{0} (@Bool) _v19)))))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v17) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v5)))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v18)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v18) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v6) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v6)))))))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v9)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(let _v22 : (@Nat) := (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))));
(let _v23 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@SerializedBodyRefinement.getAbort _v1) (@SerializedBodyRefinement.getBody _v0 _v1));
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@ite.{(0 + 1)} (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v3 (fun (_v24 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v5)) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v3 _v24)))));
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8 (@SerializedBodyRefinement.getEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v25))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v22
  _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8 _v23 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v26))))) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v26 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v7 _v8
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v26 _v25))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.counter_phase_mirror

-- Complete literal proposition for SerializedBodyRefinement.counter_phase_mirror; original proof reused.
theorem PartACanonical.Surface.m0421 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Nat))),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4)),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v11) (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v2 _v12) (@_v2 _v13))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 (@_v2 _v13)) (@Option.none.{0} (@Bool)))))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 _v14) _v15)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v19 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v15) (@Option.some.{0} (@Bool) _v19)))))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Nat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v17) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v5) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v5)))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v18)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v3 _v18) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v6) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v6)))))))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) _v9)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))),
(let _v22 : (@Nat) := (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))));
(let _v23 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@SerializedBodyRefinement.getAbort _v1) (@SerializedBodyRefinement.getBody _v0 _v1));
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@ite.{(0 + 1)} (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v3 (fun (_v24 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v2 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v24 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v5)) (@instDecidableEqNat _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v2 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v3 _v24)))));
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v7
  _v8 (@SerializedBodyRefinement.getEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v25))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v22
  _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v7 _v8 _v23 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) (@_v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v21) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8))) =>
(@_v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v7 _v8) _v26))))) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v26 _v22)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v7 _v8
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v7 _v8 _v26 _v25))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.counter_phase_mirror
