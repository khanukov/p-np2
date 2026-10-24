import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for PhysicalCallerClosure.raw_first.
noncomputable def PartACanonical.Types.p0569 :
(∀ (_v0 : (@Nat)),
(@PhysicalCallerClosure.RawFirst _v0)) := by
  exact @PhysicalCallerClosure.raw_first

-- Complete literal proposition for PhysicalCallerClosure.raw_first; original proof reused.
theorem PartACanonical.Surface.m0335 :
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
(let _v14 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v10);
(let _v15 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12)) _v9);
(let _v16 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v15);
(let _v17 : (@Nat) := (@Cursor.Target.W _v0 _v12);
(let _v18 : (@Nat) := (@Cursor.Target.M _v0 _v12 _v7);
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@SmallIngress.prepared _v1 _v2
  _v11 _v3 _v4 _v7 _v12) _v13 _v12));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v19 _v9 _v7 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@Bool.false));
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v20 _v14 _v16) _v13 _v12 _v14 _v16);
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v21 _v13 _v12 _v14 _v16);
(let _v23 : (∀ (_v23 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v22 _v14 _v16 _v12);
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v23 _v13 _v12 _v14 _v16
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v17)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v17);
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(let _v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) := (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v8);
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)),
(let _v30 : (@List.{0} (@Bool)) := (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18 _v17);
(let _v31 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v12 (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v30) (fun
  (_v31 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.RawFirst.match_1.{(0 + 1)} _v12 (fun (_v32 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v31 (fun (_v32 : (@Pnp3.Models.Circuit
  _v12)) =>
(fun (_v33 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v12 _v32) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0)) (@Nat.decLe (@Pnp3.Models.Circuit.size _v12 _v32) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0)) (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0}
  (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0}
  (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v12 _v32) (@Pnp3.Models.Circuit.eval _v12 _v32 (fun (_v34 : (@Fin _v12)) =>
(@Bool.false)))) _v33)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v33
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 :
  Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (34359738368 : Nat) (@instOfNatNat (34359738368 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v25)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18))) _v26 (fun (_v34 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.prepared _v24 _v9 _v18 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v34))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v32)),
(∀ (_v36 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.entry _v36)))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v32 _v33))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v32 _v33))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.true)))))))) (@PhysicalCallerClosure.RawFirst.match_3.{(0 + 1)} (fun
  (_v34 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v31 (fun (_v34 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@BodyIngress.machine _v0)) _v26 (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.image _v24 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v9 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v18 _v9)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v35)))))) (fun (_v34 : (@Nat)) =>
(fun (_v35 : (@Bool)) =>
(fun (_v36 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 _v17) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v36 (@List.drop.{0} (@Bool)
  _v37 _v30)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.body _v0 (@SerializedBody.done _v35))
  _v26 (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v11))) =>
(@SerializedBody.image _v24 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v9 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v18 _v9)) _v34 _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v17 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  _v38))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.raw_first

-- Independent literal expected type for PhysicalCallerClosure.raw_first_mirror.
noncomputable def PartACanonical.Types.p0570 :
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
(let _v14 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v10);
(let _v15 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12)) _v9);
(let _v16 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v15);
(let _v17 : (@Nat) := (@Cursor.Target.W _v0 _v12);
(let _v18 : (@Nat) := (@Cursor.Target.M _v0 _v12 _v7);
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@SmallIngress.prepared _v1 _v2
  _v11 _v3 _v4 _v7 _v12) _v13 _v12));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v19 _v9 _v7 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@Bool.false));
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v20 _v14 _v16) _v13 _v12 _v14 _v16);
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v21 _v13 _v12 _v14 _v16);
(let _v23 : (∀ (_v23 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v22 _v14 _v16 _v12);
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v23 _v13 _v12 _v14 _v16
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v17)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v17);
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(let _v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) := (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v8);
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)),
(let _v30 : (@List.{0} (@Bool)) := (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18 _v17);
(let _v31 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v12 (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v30) (fun
  (_v31 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.raw_first_mirror.match_1.{(0 + 1)} _v12 (fun (_v32 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v31 (fun (_v32 : (@Pnp3.Models.Circuit
  _v12)) =>
(fun (_v33 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v12 _v32) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0)) (@Nat.decLe (@Pnp3.Models.Circuit.size _v12 _v32) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0)) (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0}
  (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0}
  (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v12 _v32) (@Pnp3.Models.Circuit.eval _v12 _v32 (fun (_v34 : (@Fin _v12)) =>
(@Bool.false)))) _v33)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v33
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 :
  Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (34359738368 : Nat) (@instOfNatNat (34359738368 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v25)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18))) _v26 (fun (_v34 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.prepared _v24 _v9 _v18 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v34))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v32)),
(∀ (_v36 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.entry _v36)))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v32 _v33))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v32 _v33))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.true)))))))) (@PhysicalCallerClosure.raw_first_mirror.match_3.{(0 +
  1)} (fun (_v34 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v31 (fun (_v34 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@BodyIngress.machine _v0)) _v26 (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.image _v24 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v9 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v18 _v9)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v35)))))) (fun (_v34 : (@Nat)) =>
(fun (_v35 : (@Bool)) =>
(fun (_v36 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 _v17) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v36 (@List.drop.{0} (@Bool)
  _v37 _v30)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.body _v0 (@SerializedBody.done _v35))
  _v26 (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v11))) =>
(@SerializedBody.image _v24 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v9 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v18 _v9)) _v34 _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v17 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  _v38))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.raw_first_mirror

-- Complete literal proposition for PhysicalCallerClosure.raw_first_mirror; original proof reused.
theorem PartACanonical.Surface.m0336 :
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
(let _v14 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v10);
(let _v15 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12)) _v9);
(let _v16 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v15);
(let _v17 : (@Nat) := (@Cursor.Target.W _v0 _v12);
(let _v18 : (@Nat) := (@Cursor.Target.M _v0 _v12 _v7);
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@SmallIngress.prepared _v1 _v2
  _v11 _v3 _v4 _v7 _v12) _v13 _v12));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v19 _v9 _v7 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@Bool.false));
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v20 _v14 _v16) _v13 _v12 _v14 _v16);
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v21 _v13 _v12 _v14 _v16);
(let _v23 : (∀ (_v23 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v22 _v14 _v16 _v12);
(let _v24 : (∀ (_v24 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v23 _v13 _v12 _v14 _v16
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v17)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v17);
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(let _v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) := (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v8);
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)),
(let _v30 : (@List.{0} (@Bool)) := (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18 _v17);
(let _v31 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v12 (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v30) (fun
  (_v31 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.raw_first_mirror.match_1.{(0 + 1)} _v12 (fun (_v32 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v12)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v31 (fun (_v32 : (@Pnp3.Models.Circuit
  _v12)) =>
(fun (_v33 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v12 _v32) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0)) (@Nat.decLe (@Pnp3.Models.Circuit.size _v12 _v32) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0)) (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0}
  (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0}
  (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v12 _v32) (@Pnp3.Models.Circuit.eval _v12 _v32 (fun (_v34 : (@Fin _v12)) =>
(@Bool.false)))) _v33)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v33
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 :
  Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (34359738368 : Nat) (@instOfNatNat (34359738368 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v25)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18))) _v26 (fun (_v34 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.prepared _v24 _v9 _v18 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v34))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v32)),
(∀ (_v36 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.entry _v36)))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v32 _v33))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))))) (@And (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v32 _v33))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v34 _v25))
  (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.true)))))))) (@PhysicalCallerClosure.raw_first_mirror.match_3.{(0 +
  1)} (fun (_v34 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v31 (fun (_v34 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@BodyIngress.machine _v0)) _v26 (fun (_v35 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.image _v24 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v9 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v18 _v9)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v35)))))) (fun (_v34 : (@Nat)) =>
(fun (_v35 : (@Bool)) =>
(fun (_v36 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v37 _v17) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v36 (@List.drop.{0} (@Bool)
  _v37 _v30)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v32 _v33) _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.body _v0 (@SerializedBody.done _v35))
  _v26 (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v11))) =>
(@SerializedBody.image _v24 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v9 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v18 _v9)) _v34 _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v17 _v37) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  _v38))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.raw_first_mirror

-- Independent literal expected type for PhysicalCallerClosure.resetCopyEntry.
noncomputable def PartACanonical.Types.p0571 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0))))) := by
  exact @PhysicalCallerClosure.resetCopyEntry

-- Independent literal expected type for PhysicalCallerClosure.resetEntry.
noncomputable def PartACanonical.Types.p0572 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0))))) := by
  exact @PhysicalCallerClosure.resetEntry

-- Independent literal expected type for PhysicalCallerClosure.reset_body_entry.
noncomputable def PartACanonical.Types.p0573 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
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
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(@Nat))),
(∀ (_v15 : (∀ (_v15 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Fin _v4)),
(@Bool))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v17) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v14 _v18) (@_v14 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 (@_v14 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))
  _v10)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Or (@Eq.{(0
  + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))),
(@Eq.{(0 + 1)} (@Nat) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v14 _v24) _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v25) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  _v12)))))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v26) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  _v13)))))))),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v11)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v13 _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v9)),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v6) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v9) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v9)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v6)),
(∀ (_v37 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v38 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v42 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v39) (@Option.some.{0} (@Bool) _v42)))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v6)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v43 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v40) (@Option.some.{0} (@Bool) _v43)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v41) (@Option.some.{0} (@Bool) (@_v16 (@Fin.mk _v4 _v41 _v43)))))))),
(∀ (_v42 : (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7))),
(∀ (_v43 : (∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v4)),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7) (@Eq.{(0 + 1)}
  (@Option.{0} (@Bool)) (@_v15 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))))),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(let _v45 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun
  (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v45))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v46 _v45) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v4 _v16 _v7))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun (_v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v3) _v47) _v7) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)))))))))) (@And (∀ (_v47 :
  (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))) _v10) (∀ (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45) _v49) (@_v15
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49)))))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))
  (@PhysicalCallerClosure.rowsDone _v0)))))) (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47
  _v45)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_body_entry

-- Complete literal proposition for PhysicalCallerClosure.reset_body_entry; original proof reused.
theorem PartACanonical.Surface.m0337 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
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
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(@Nat))),
(∀ (_v15 : (∀ (_v15 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Fin _v4)),
(@Bool))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v17) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v14 _v18) (@_v14 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 (@_v14 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))
  _v10)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Or (@Eq.{(0
  + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))),
(@Eq.{(0 + 1)} (@Nat) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v14 _v24) _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v25) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  _v12)))))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v26) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  _v13)))))))),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v11)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v13 _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v9)),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v6) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v9) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v9)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v6)),
(∀ (_v37 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v38 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v42 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v39) (@Option.some.{0} (@Bool) _v42)))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v6)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v43 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v40) (@Option.some.{0} (@Bool) _v43)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v41) (@Option.some.{0} (@Bool) (@_v16 (@Fin.mk _v4 _v41 _v43)))))))),
(∀ (_v42 : (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7))),
(∀ (_v43 : (∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v4)),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7) (@Eq.{(0 + 1)}
  (@Option.{0} (@Bool)) (@_v15 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))))),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(let _v45 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun
  (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v45))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v46 _v45) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v4 _v16 _v7))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun (_v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v3) _v47) _v7) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)))))))))) (@And (∀ (_v47 :
  (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))) _v10) (∀ (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45) _v49) (@_v15
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49)))))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))
  (@PhysicalCallerClosure.rowsDone _v0)))))) (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47
  _v45)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_body_entry

-- Independent literal expected type for PhysicalCallerClosure.reset_body_entry_mirror.
noncomputable def PartACanonical.Types.p0574 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
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
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(@Nat))),
(∀ (_v15 : (∀ (_v15 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Fin _v4)),
(@Bool))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v17) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v14 _v18) (@_v14 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 (@_v14 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))
  _v10)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Or (@Eq.{(0
  + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))),
(@Eq.{(0 + 1)} (@Nat) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v14 _v24) _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v25) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  _v12)))))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v26) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  _v13)))))))),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v11)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v13 _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v9)),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v6) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v9) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v9)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v6)),
(∀ (_v37 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v38 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v42 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v39) (@Option.some.{0} (@Bool) _v42)))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v6)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v43 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v40) (@Option.some.{0} (@Bool) _v43)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v41) (@Option.some.{0} (@Bool) (@_v16 (@Fin.mk _v4 _v41 _v43)))))))),
(∀ (_v42 : (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7))),
(∀ (_v43 : (∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v4)),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7) (@Eq.{(0 + 1)}
  (@Option.{0} (@Bool)) (@_v15 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))))),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(let _v45 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun
  (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v45))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v46 _v45) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v4 _v16 _v7))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun (_v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v3) _v47) _v7) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)))))))))) (@And (∀ (_v47 :
  (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))) _v10) (∀ (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45) _v49) (@_v15
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49)))))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))
  (@PhysicalCallerClosure.rowsDone _v0)))))) (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47
  _v45)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_body_entry_mirror

-- Complete literal proposition for PhysicalCallerClosure.reset_body_entry_mirror; original proof reused.
theorem PartACanonical.Surface.m0338 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
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
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(@Nat))),
(∀ (_v15 : (∀ (_v15 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Fin _v4)),
(@Bool))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v17) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v19)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v14 _v18) (@_v14 _v19))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v19 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 (@_v14 _v19)) (@Option.none.{0} (@Bool)))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 _v20) _v21)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v25 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v21) (@Option.some.{0} (@Bool) _v25)))))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))
  _v10)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Or (@Eq.{(0
  + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Or (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v24 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))),
(@Eq.{(0 + 1)} (@Nat) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v14 _v24) _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v25) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@_v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  _v12)))))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v26) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@_v14 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  _v13)))))))),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v11)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v13 _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v9)),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v6) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v9) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 _v8) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v9)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v6)),
(∀ (_v37 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v38 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v42 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v39) (@Option.some.{0} (@Bool) _v42)))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v6)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v43 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v40) (@Option.some.{0} (@Bool) _v43)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v15 _v41) (@Option.some.{0} (@Bool) (@_v16 (@Fin.mk _v4 _v41 _v43)))))))),
(∀ (_v42 : (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7))),
(∀ (_v43 : (∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v4)),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7) (@Eq.{(0 + 1)}
  (@Option.{0} (@Bool)) (@_v15 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))))),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(let _v45 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun
  (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v45))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v46 _v45) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v4 _v16 _v7))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v6 _v44) (fun (_v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v3) _v47) _v7) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v7) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) _v4)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) _v12))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)
  (@_v14 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v13))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Nat.decLt (@_v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v47) (@_v14 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v15 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v47)))))))))) (@And (∀ (_v47 :
  (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))) _v10) (∀ (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45) _v49) (@_v15
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v49)))))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47 _v45))
  (@PhysicalCallerClosure.rowsDone _v0)))))) (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v47
  _v45)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_body_entry_mirror

-- Independent literal expected type for PhysicalCallerClosure.reset_clear_prefix.
noncomputable def PartACanonical.Types.p0575 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(@Nat))),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 _v10) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v12 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v8 _v11) (@_v8 _v12))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v12 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@_v8 _v12)) (@Option.none.{0} (@Bool)))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 _v13) _v14)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v18 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v14) (@Option.some.{0} (@Bool) _v18)))))))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Nat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) _v7)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v21)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) _v21 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v21) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v22) (@Option.none.{0} (@Bool))))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v4 _v23) (fun
  (_v25 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v25))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v26 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v26 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v26 _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetCopyEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) (@_v8
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v24) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27))
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27))))))))) (@And (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v26)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25))) _v7) (∀ (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v29))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25) _v29) (@_v9
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v29)))))))) (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v26)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25))
  (@PhysicalCallerClosure.rowsDone _v0))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_clear_prefix

-- Complete literal proposition for PhysicalCallerClosure.reset_clear_prefix; original proof reused.
theorem PartACanonical.Surface.m0339 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(@Nat))),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 _v10) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v12 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v8 _v11) (@_v8 _v12))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v12 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@_v8 _v12)) (@Option.none.{0} (@Bool)))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 _v13) _v14)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v18 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v14) (@Option.some.{0} (@Bool) _v18)))))))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Nat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) _v7)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v21)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) _v21 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v21) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v22) (@Option.none.{0} (@Bool))))))),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(let _v25 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v4 _v23) (fun
  (_v25 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v25))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v26 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v26 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v26 _v25) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@PhysicalCallerClosure.resetCopyEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) (@_v8
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v24) (fun (_v27 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27))
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Nat.decLt (@_v8 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v3) _v27) (@_v8 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v27))))))))) (@And (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v26)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25))) _v7) (∀ (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3))),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v29))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25) _v29) (@_v9
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v3) _v29)))))))) (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v26)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v3 _v27 _v25))
  (@PhysicalCallerClosure.rowsDone _v0))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_clear_prefix

-- Independent literal expected type for PhysicalCallerClosure.reset_then_body.
noncomputable def PartACanonical.Types.p0576 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
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
(∀ (_v12 : (∀ (_v12 : (@Fin _v4)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Fin _v6)),
(@Bool))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (@Nat)),
(∀ (_v17 : (@Nat)),
(∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v4)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v3)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v7)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v7)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v6) _v7)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) _v7)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v11)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v27) (@Option.some.{0} (@Bool) (@_v12 (@Fin.mk _v4 _v27 _v29)))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v29) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (∀ (_v31 : (@Fin _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Fin.val _v6 _v31)))
  (@Option.some.{0} (@Bool) (@_v13 _v31))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v11) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3))
  (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v40 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v37) (@Option.some.{0} (@Bool) _v40)))))))),
(∀ (_v38 : (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v10))),
(∀ (_v39 : (∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v4)),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v10) (@Eq.{(0 + 1)}
  (@Option.{0} (@Bool)) (@_v14 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))))),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))),
(let _v42 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3);
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (@SerializedBody.image _v14 _v42 _v7 _v6 _v8 _v9 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) _v15 _v16 _v17 _v18);
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v41) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))) =>
(@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) _v44))));
(let _v45 : (@List.{0} (@Bool)) := (@SerializedBody.window _v4 _v12 _v10 _v9);
(let _v46 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v6)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v6 (@Pnp4.Frontier.ContractExpansion.bitLength _v6) _v45) (fun
  (_v46 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v6) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.reset_then_body.match_1.{(0 + 1)} _v6 (fun (_v47 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v6)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v46 (fun (_v47 : (@Pnp3.Models.Circuit
  _v6)) =>
(fun (_v48 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v6 _v47) _v8) (@Nat.decLe (@Pnp3.Models.Circuit.size _v6 _v47) _v8)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v6 _v47)
  (@Pnp3.Models.Circuit.eval _v6 _v47 _v13)) _v48)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v47 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v48 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v47 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@SerializedBody.delimiter _v42 _v7 _v6 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@And (@LE.le.{0} (@Nat)
  (@instLENat) _v48 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v49 : (@Nat)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v49 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v47 _v48))),
(∀ (_v51 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))
  _v51) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v3 _v2 _v49 _v44)) (@PhysicalCallerClosure.evalState _v0 _v51))))))
  (@PhysicalCallerClosure.reset_then_body.match_3.{(0 + 1)} (fun (_v49 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v46 (fun (_v49 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v3 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v47 _v48) _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2 (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v41) (fun (_v50 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))) =>
(@SerializedBody.image _v14 _v42 _v7 _v6 _v8 _v9 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) _v50)))))) (fun (_v49 : (@Nat)) =>
(fun (_v50 : (@Bool)) =>
(fun (_v51 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v52 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v52 _v9) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v51 (@List.drop.{0} (@Bool)
  _v52 _v45)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v3 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v47 _v48) _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done _v50))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v41) (fun (_v53 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))) =>
(@SerializedBody.image _v14 _v42 _v7 _v6 _v8 _v9 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) _v49 _v52 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v52) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2)
  _v53))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_then_body

-- Complete literal proposition for PhysicalCallerClosure.reset_then_body; original proof reused.
theorem PartACanonical.Surface.m0340 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
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
(∀ (_v12 : (∀ (_v12 : (@Fin _v4)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Fin _v6)),
(@Bool))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (@Nat)),
(∀ (_v17 : (@Nat)),
(∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v4)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v3)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v7)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v7)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v6) _v7)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) _v7)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v11)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v27) (@Option.some.{0} (@Bool) (@_v12 (@Fin.mk _v4 _v27 _v29)))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v29) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (∀ (_v31 : (@Fin _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Fin.val _v6 _v31)))
  (@Option.some.{0} (@Bool) (@_v13 _v31))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v11) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3))
  (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v40 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v14 _v37) (@Option.some.{0} (@Bool) _v40)))))))),
(∀ (_v38 : (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v10))),
(∀ (_v39 : (∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v4)),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v10) (@Eq.{(0 + 1)}
  (@Option.{0} (@Bool)) (@_v14 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))))),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3) _v7 _v6
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))),
(let _v42 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v3);
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (@SerializedBody.image _v14 _v42 _v7 _v6 _v8 _v9 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) _v15 _v16 _v17 _v18);
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2
  (@PhysicalCallerClosure.resetEntry _v0 _v1) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v41) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))) =>
(@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) _v44))));
(let _v45 : (@List.{0} (@Bool)) := (@SerializedBody.window _v4 _v12 _v10 _v9);
(let _v46 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v6)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v6 (@Pnp4.Frontier.ContractExpansion.bitLength _v6) _v45) (fun
  (_v46 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v6) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.reset_then_body.match_1.{(0 + 1)} _v6 (fun (_v47 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v6)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v46 (fun (_v47 : (@Pnp3.Models.Circuit
  _v6)) =>
(fun (_v48 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v6 _v47) _v8) (@Nat.decLe (@Pnp3.Models.Circuit.size _v6 _v47) _v8)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v6 _v47)
  (@Pnp3.Models.Circuit.eval _v6 _v47 _v13)) _v48)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v47 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v48 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v47 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@SerializedBody.delimiter _v42 _v7 _v6 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@And (@LE.le.{0} (@Nat)
  (@instLENat) _v48 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v49 : (@Nat)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v49 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v47 _v48))),
(∀ (_v51 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))
  _v51) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v3 _v2 _v49 _v44)) (@PhysicalCallerClosure.evalState _v0 _v51))))))
  (@PhysicalCallerClosure.reset_then_body.match_3.{(0 + 1)} (fun (_v49 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v46 (fun (_v49 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v3 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v47 _v48) _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2 (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v41) (fun (_v50 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))) =>
(@SerializedBody.image _v14 _v42 _v7 _v6 _v8 _v9 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) _v50)))))) (fun (_v49 : (@Nat)) =>
(fun (_v50 : (@Bool)) =>
(fun (_v51 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v52 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v52 _v9) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v51 (@List.drop.{0} (@Bool)
  _v52 _v45)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v3 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v47 _v48) _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v3 _v2 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done _v50))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) _v6) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v41) (fun (_v53 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2))) =>
(@SerializedBody.image _v14 _v42 _v7 _v6 _v8 _v9 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v10 _v4)) _v49 _v52 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v52) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v3 _v2)
  _v53))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.reset_then_body

-- Independent literal expected type for PhysicalCallerClosure.rowsDone.
noncomputable def PartACanonical.Types.p0577 :
(∀ (_v0 : (@Nat)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))) := by
  exact @PhysicalCallerClosure.rowsDone

-- Independent literal expected type for Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown.loopTape.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0578 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown.loopTape _v0 _v1 _v2
  _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion.finishTape _v0 _v1 _v2 _v3 _v4 _v5 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v5)) (@Nat.decLe (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v5)) (@Option.some.{0} (@Bool) (@Nat.testBit _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v2) _v8)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) _v7))) (@instDecidableAnd (@LE.le.{0} (@Nat)
  (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8))
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5)
  _v7)) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8))
  (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) _v7))) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Option.none.{0} (@Bool)))))))))))))))))
end
-- Complete literal proposition for Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown.loopTape.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0341 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown.loopTape _v0 _v1 _v2
  _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion.finishTape _v0 _v1 _v2 _v3 _v4 _v5 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v5)) (@Nat.decLe (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v5)) (@Option.some.{0} (@Bool) (@Nat.testBit _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v2) _v8)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) _v7))) (@instDecidableAnd (@LE.le.{0} (@Nat)
  (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8))
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5)
  _v7)) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v8))
  (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1) _v2) _v8) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) _v7))) (@Option.some.{0} (@Bool) (@Bool.true))
  (@Option.none.{0} (@Bool)))))))))))))))))
end
-- Independent literal expected type for Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft.eq_1.
noncomputable def PartACanonical.Types.p0579 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(@Eq.{(0 + 1)} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft _v0 _v1 _v2) (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)
  _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft._proof_1 _v0 _v1 _v2)))))) := by
  exact @Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft.eq_1

-- Complete literal proposition for Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft.eq_1; original proof reused.
theorem PartACanonical.Surface.m0342 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(@Eq.{(0 + 1)} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft _v0 _v1 _v2) (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)
  _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft._proof_1 _v0 _v1 _v2)))))) := by
  exact @Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft.eq_1

-- Independent literal expected type for Pnp3.Models.Circuit.eval.eq_1.
noncomputable def PartACanonical.Types.p0580 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin _v0)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.input _v0 _v1)) (fun (_v2 : (@Pnp3.Core.BitVec _v0)) =>
(@_v2 _v1))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_1

-- Complete literal proposition for Pnp3.Models.Circuit.eval.eq_1; original proof reused.
theorem PartACanonical.Surface.m0343 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin _v0)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.input _v0 _v1)) (fun (_v2 : (@Pnp3.Core.BitVec _v0)) =>
(@_v2 _v1))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_1

-- Independent literal expected type for Pnp3.Models.Circuit.eval.eq_2.
noncomputable def PartACanonical.Types.p0581 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Bool)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.const _v0 _v1)) (fun (_v2 : (@Pnp3.Core.BitVec _v0)) =>
_v1)))) := by
  exact @Pnp3.Models.Circuit.eval.eq_2

-- Complete literal proposition for Pnp3.Models.Circuit.eval.eq_2; original proof reused.
theorem PartACanonical.Surface.m0344 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Bool)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.const _v0 _v1)) (fun (_v2 : (@Pnp3.Core.BitVec _v0)) =>
_v1)))) := by
  exact @Pnp3.Models.Circuit.eval.eq_2

-- Independent literal expected type for Pnp3.Models.Circuit.eval.eq_3.
noncomputable def PartACanonical.Types.p0582 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Pnp3.Models.Circuit _v0)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.not _v0 _v1)) (fun (_v2 : (@Pnp3.Core.BitVec _v0)) =>
(@Bool.not (@Pnp3.Models.Circuit.eval _v0 _v1 _v2)))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_3

-- Complete literal proposition for Pnp3.Models.Circuit.eval.eq_3; original proof reused.
theorem PartACanonical.Surface.m0345 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Pnp3.Models.Circuit _v0)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.not _v0 _v1)) (fun (_v2 : (@Pnp3.Core.BitVec _v0)) =>
(@Bool.not (@Pnp3.Models.Circuit.eval _v0 _v1 _v2)))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_3

-- Independent literal expected type for Pnp3.Models.Circuit.eval.eq_4.
noncomputable def PartACanonical.Types.p0583 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Pnp3.Models.Circuit _v0)),
(∀ (_v2 : (@Pnp3.Models.Circuit _v0)),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.and _v0 _v1 _v2)) (fun (_v3 : (@Pnp3.Core.BitVec _v0)) =>
(@Bool.and (@Pnp3.Models.Circuit.eval _v0 _v1 _v3) (@Pnp3.Models.Circuit.eval _v0 _v2 _v3))))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_4

-- Complete literal proposition for Pnp3.Models.Circuit.eval.eq_4; original proof reused.
theorem PartACanonical.Surface.m0346 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Pnp3.Models.Circuit _v0)),
(∀ (_v2 : (@Pnp3.Models.Circuit _v0)),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.and _v0 _v1 _v2)) (fun (_v3 : (@Pnp3.Core.BitVec _v0)) =>
(@Bool.and (@Pnp3.Models.Circuit.eval _v0 _v1 _v3) (@Pnp3.Models.Circuit.eval _v0 _v2 _v3))))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_4

-- Independent literal expected type for Pnp3.Models.Circuit.eval.eq_5.
noncomputable def PartACanonical.Types.p0584 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Pnp3.Models.Circuit _v0)),
(∀ (_v2 : (@Pnp3.Models.Circuit _v0)),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.or _v0 _v1 _v2)) (fun (_v3 : (@Pnp3.Core.BitVec _v0)) =>
(@Bool.or (@Pnp3.Models.Circuit.eval _v0 _v1 _v3) (@Pnp3.Models.Circuit.eval _v0 _v2 _v3))))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_5

-- Complete literal proposition for Pnp3.Models.Circuit.eval.eq_5; original proof reused.
theorem PartACanonical.Surface.m0347 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Pnp3.Models.Circuit _v0)),
(∀ (_v2 : (@Pnp3.Models.Circuit _v0)),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Pnp3.Core.BitVec _v0)),
(@Bool)) (@Pnp3.Models.Circuit.eval _v0 (@Pnp3.Models.Circuit.or _v0 _v1 _v2)) (fun (_v3 : (@Pnp3.Core.BitVec _v0)) =>
(@Bool.or (@Pnp3.Models.Circuit.eval _v0 _v1 _v3) (@Pnp3.Models.Circuit.eval _v0 _v2 _v3))))))) := by
  exact @Pnp3.Models.Circuit.eval.eq_5

-- Independent literal expected type for Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation.eq_1.
noncomputable def PartACanonical.Types.p0585 :
(∀ {_v0 : (∀ (_v0 : (@Nat)),
(@Nat))},
(∀ (_v1 : (@Pnp4.Frontier.TreeCircuitWitnessCodec _v0)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation _v0 _v1 _v2 _v3 _v4 _v5)
  (@dite.{(0 + 1)} (@Bool) (@Eq.{(0 + 1)} (@Nat) _v3 (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v3 (@Pnp3.ComplexityInterfaces.certificateLength _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (fun (_v6 : (@Eq.{(0 + 1)} (@Nat) _v3
  (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.concatV1ToPrefixBitVec _v2
  (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4
  (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) _v3 (fun (_v7 : (@Nat)) =>
(fun (_v8 : (@Eq.{(0 + 1)} (@Nat) _v3 _v7)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v7))) _v5 (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v6)))) (fun (_v6 : (@Not (@Eq.{(0 + 1)} (@Nat) _v3
  (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) =>
(@Bool.false)))))))))) := by
  exact @Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation.eq_1

-- Complete literal proposition for Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation.eq_1; original proof reused.
theorem PartACanonical.Surface.m0348 :
(∀ {_v0 : (∀ (_v0 : (@Nat)),
(@Nat))},
(∀ (_v1 : (@Pnp4.Frontier.TreeCircuitWitnessCodec _v0)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation _v0 _v1 _v2 _v3 _v4 _v5)
  (@dite.{(0 + 1)} (@Bool) (@Eq.{(0 + 1)} (@Nat) _v3 (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v3 (@Pnp3.ComplexityInterfaces.certificateLength _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (fun (_v6 : (@Eq.{(0 + 1)} (@Nat) _v3
  (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.concatV1ToPrefixBitVec _v2
  (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4
  (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) _v3 (fun (_v7 : (@Nat)) =>
(fun (_v8 : (@Eq.{(0 + 1)} (@Nat) _v3 _v7)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v7))) _v5 (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v6)))) (fun (_v6 : (@Not (@Eq.{(0 + 1)} (@Nat) _v3
  (@Pnp3.ComplexityInterfaces.certificateLength _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) =>
(@Bool.false)))))))))) := by
  exact @Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation.eq_1

-- Independent literal expected type for Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation.eq_1.
noncomputable def PartACanonical.Types.p0586 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation.eq_1

-- Complete literal proposition for Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation.eq_1; original proof reused.
theorem PartACanonical.Surface.m0349 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation.eq_1

-- Independent literal expected type for Pnp4.Frontier.ContractExpansion.gammaBit.eq_1.
noncomputable def PartACanonical.Types.p0587 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp4.Frontier.ContractExpansion.gammaLen _v0))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.gammaBit _v0 _v1) (@dite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt (@Fin.val
  (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (fun (_v2 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Bool.false)) (fun (_v2 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp4.Frontier.ContractExpansion.gammaLen
  _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) =>
(@Pnp4.Frontier.ContractExpansion.natBitBE (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Fin.mk
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp4.Frontier.ContractExpansion.gammaBit._proof_3 _v0 _v1 _v2)))))))) := by
  exact @Pnp4.Frontier.ContractExpansion.gammaBit.eq_1

-- Complete literal proposition for Pnp4.Frontier.ContractExpansion.gammaBit.eq_1; original proof reused.
theorem PartACanonical.Surface.m0350 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp4.Frontier.ContractExpansion.gammaLen _v0))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.gammaBit _v0 _v1) (@dite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt (@Fin.val
  (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (fun (_v2 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Bool.false)) (fun (_v2 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp4.Frontier.ContractExpansion.gammaLen
  _v0) _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) =>
(@Pnp4.Frontier.ContractExpansion.natBitBE (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Fin.mk
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Fin.val (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp4.Frontier.ContractExpansion.gammaBit._proof_3 _v0 _v1 _v2)))))))) := by
  exact @Pnp4.Frontier.ContractExpansion.gammaBit.eq_1

-- Independent literal expected type for Pnp4.Frontier.ContractExpansion.gammaLen.eq_1.
noncomputable def PartACanonical.Types.p0588 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.bitLength
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @Pnp4.Frontier.ContractExpansion.gammaLen.eq_1

-- Complete literal proposition for Pnp4.Frontier.ContractExpansion.gammaLen.eq_1; original proof reused.
theorem PartACanonical.Surface.m0351 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.gammaLen _v0) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.bitLength
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @Pnp4.Frontier.ContractExpansion.gammaLen.eq_1

-- Independent literal expected type for PostWeight.Target.Normal.
noncomputable def PartACanonical.Types.p0589 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @PostWeight.Target.Normal

-- Independent literal expected type for PostWeight.prepared_length.
noncomputable def PartACanonical.Types.p0590 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ (_v6 : (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) _v6))),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v8))),
(let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2);
(let _v12 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v11);
(let _v13 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v8) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v15 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v11);
(let _v16 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v13)) _v10);
(let _v17 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v16);
(let _v18 : (∀ (_v18 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v12
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v12 (@SmallIngress.prepared _v1 _v2
  _v12 _v3 _v4 _v8 _v13) _v14 _v13));
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v18 _v10 _v8 _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v13) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v13) (@Bool.false));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v19 _v15 _v17) _v14 _v13 _v15 _v17);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v20 _v14 _v13 _v15 _v17);
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v21 _v15 _v17 _v13);
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v10)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v13) _v17)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) (@Cursor.Target.W _v0 _v13) _v17)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v17)) _v13) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (524288 : Nat) (@instOfNatNat (524288 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11 _v12)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v11 _v12 _v27 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11 _v12 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 :
  Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v29 : (@Not
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)))) =>
(@PostWeight.prepared_length._proof_1 _v0 _v1 _v2 _v6 _v8 _v26 _v29)))) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@CappedWeight.Target.image _v22 _v14 _v13 _v15 _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v13 _v0) _v0) (@Cursor.Target.W
  _v0 _v13) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v29)))))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v28) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@CappedWeight.Target.image _v22 _v14 _v13 _v15 _v17 (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0
  _v13)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Cursor.Target.W _v0 _v13) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v29))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 _v27)),
(let _v31 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  _v11 _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine
  _v0)) _v11 _v12 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v31 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v11 _v12)))) =>
(@PostWeight.prepared_length._proof_1 _v0 _v1 _v2 _v6 _v8 _v26 _v31)))) (fun (_v31 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@CappedWeight.Target.image _v22 _v14 _v13 _v15 _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v13 _v0) _v0) (@Cursor.Target.W
  _v0 _v13) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v31))));
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v11 _v12 _v29 _v31))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@Cursor.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v11 _v12 _v29 _v31))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Cursor.machine _v0)))))))))))))))))))))))))))))))))))))))) := by
  exact @PostWeight.prepared_length

-- Complete literal proposition for PostWeight.prepared_length; original proof reused.
theorem PartACanonical.Surface.m0352 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ (_v6 : (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) _v6))),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v8))),
(let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2);
(let _v12 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v11);
(let _v13 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v8) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v15 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v11);
(let _v16 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v13)) _v10);
(let _v17 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v16);
(let _v18 : (∀ (_v18 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v12
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v12 (@SmallIngress.prepared _v1 _v2
  _v12 _v3 _v4 _v8 _v13) _v14 _v13));
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v18 _v10 _v8 _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v13) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v13) (@Bool.false));
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v19 _v15 _v17) _v14 _v13 _v15 _v17);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v20 _v14 _v13 _v15 _v17);
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v21 _v15 _v17 _v13);
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v10)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v13) _v17)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) (@Cursor.Target.W _v0 _v13) _v17)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v17)) _v13) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (524288 : Nat) (@instOfNatNat (524288 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11 _v12)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v11 _v12 _v27 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11 _v12 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 :
  Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v29 : (@Not
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)))) =>
(@PostWeight.prepared_length._proof_1 _v0 _v1 _v2 _v6 _v8 _v26 _v29)))) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@CappedWeight.Target.image _v22 _v14 _v13 _v15 _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v13 _v0) _v0) (@Cursor.Target.W
  _v0 _v13) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v29)))))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v28) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@CappedWeight.Target.image _v22 _v14 _v13 _v15 _v17 (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0
  _v13)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Cursor.Target.W _v0 _v13) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v29))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 _v27)),
(let _v31 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  _v11 _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine
  _v0)) _v11 _v12 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17) _v13)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v31 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v15 _v17) _v13) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v11 _v12)))) =>
(@PostWeight.prepared_length._proof_1 _v0 _v1 _v2 _v6 _v8 _v26 _v31)))) (fun (_v31 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@CappedWeight.Target.image _v22 _v14 _v13 _v15 _v17 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v13 _v0) _v0) (@Cursor.Target.W
  _v0 _v13) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v31))));
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v11 _v12 _v29 _v31))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@Cursor.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v11 _v12 _v29 _v31))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Cursor.machine _v0)))))))))))))))))))))))))))))))))))))))) := by
  exact @PostWeight.prepared_length

-- Independent literal expected type for PowerDriver.Target.RawPower.
noncomputable def PartACanonical.Types.p0591 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @PowerDriver.Target.RawPower

-- Independent literal expected type for PowerDriver.accepted_power.
noncomputable def PartACanonical.Types.p0592 :
(∀ (_v0 : (@Nat)),
(@PowerDriver.Target.RawPower _v0)) := by
  exact @PowerDriver.accepted_power

-- Complete literal proposition for PowerDriver.accepted_power; original proof reused.
theorem PartACanonical.Surface.m0353 :
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
(let _v14 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v10);
(let _v15 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12)) _v9);
(let _v16 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v15);
(let _v17 : (∀ (_v17 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@SmallIngress.prepared _v1 _v2
  _v11 _v3 _v4 _v7 _v12) _v13 _v12));
(let _v18 : (∀ (_v18 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v17 _v9 _v7 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v12) (@Bool.false));
(let _v19 : (∀ (_v19 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v18 _v14 _v16) _v13 _v12 _v14 _v16);
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v19 _v13 _v12 _v14 _v16);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v20 _v14 _v16 _v12);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v3 _v4));
(@And (∀ (_v23 : (@Eq.{(0 + 1)} (@Nat) _v15 _v9)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@PowerDriver.Target.RawPower._proof_4))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v8) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@_v18 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v25))))))))))) (∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v24 :
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v25 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v25 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v16
  (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@Cursor.Target.M _v0 _v12
  _v7)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v25 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v16 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v16 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (250 : Nat) (@instOfNatNat (250 : Nat))) (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@PowerDriver.Target.RawPower._proof_5 _v0 _v1 _v2 _v6 _v7 _v24)) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@_v20 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v26)))))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v16)
  (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v25 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (82 : Nat) (@instOfNatNat (82 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@PowerDriver.Target.RawPower._proof_6 _v0 _v1 _v2 _v6 _v7 _v24)) (fun
  (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@Pnp4.Frontier.ContractExpansion.bitLength _v12) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v10 _v11) _v26)))))) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v25)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v26 _v22))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat))) (@OfNat.ofNat.{0} (@Nat) (329 : Nat)
  (@instOfNatNat (329 : Nat)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (82 : Nat) (@instOfNatNat (82 : Nat))) _v0))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v26 :
  (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v26)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v12) (@And (@Eq.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v27 _v12) _v28)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@Cursor.Target.M _v0 _v12 _v7)) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v25 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (798 : Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@PowerDriver.Target.RawPower._proof_7 _v0 _v1 _v2 _v6 _v7 _v24)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@Pnp4.Frontier.ContractExpansion.bitLength _v12) (@HSub.hSub.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v26) _v27) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v29)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v25)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat))) (@OfNat.ofNat.{0} (@Nat) (329 : Nat)
  (@instOfNatNat (329 : Nat)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (82 : Nat) (@instOfNatNat (82 : Nat)))
  _v0))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PowerDriver.accepted_power

-- Independent literal expected type for RawCallerClosure.Target.Prelude.
noncomputable def PartACanonical.Types.p0593 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v3 : (@Nat)),
(Sort 0))))) := by
  exact @RawCallerClosure.Target.Prelude

-- Independent literal expected type for RawCallerClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0594 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RawCallerClosure.Target.Raw

-- Independent literal expected type for RawCallerClosure.Target.RowsResult.
noncomputable def PartACanonical.Types.p0595 :
(∀ (_v0 : (@Nat)),
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
(∀ (_v12 : (∀ (_v12 : (@Fin _v3)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v5) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v15 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v2 _v1)),
(∀ (_v16 : (@Nat)),
(Sort 0)))))))))))))))))) := by
  exact @RawCallerClosure.Target.RowsResult

-- Independent literal expected type for RawCallerClosure.allocation.
noncomputable def PartACanonical.Types.p0596 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @RawCallerClosure.allocation

-- Independent literal expected type for RawCallerClosure.callerConfig.
noncomputable def PartACanonical.Types.p0597 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))
  _v1 _v2))))) := by
  exact @RawCallerClosure.callerConfig

-- Independent literal expected type for RawCallerClosure.callerConfig.eq_1.
noncomputable def PartACanonical.Types.p0598 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v2) (@RawCallerClosure.callerConfig _v0 _v1 _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@RawCallerClosure.callerState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))))))) := by
  exact @RawCallerClosure.callerConfig.eq_1

-- Complete literal proposition for RawCallerClosure.callerConfig.eq_1; original proof reused.
theorem PartACanonical.Surface.m0354 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v2) (@RawCallerClosure.callerConfig _v0 _v1 _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@RawCallerClosure.callerState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))))))) := by
  exact @RawCallerClosure.callerConfig.eq_1

-- Independent literal expected type for RawCallerClosure.callerConfig_equation_mirror.
noncomputable def PartACanonical.Types.p0599 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v2) (@RawCallerClosure.callerConfig _v0 _v1 _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@RawCallerClosure.callerState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))))))) := by
  exact @RawCallerClosure.callerConfig_equation_mirror

-- Complete literal proposition for RawCallerClosure.callerConfig_equation_mirror; original proof reused.
theorem PartACanonical.Surface.m0355 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v2) (@RawCallerClosure.callerConfig _v0 _v1 _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@RawCallerClosure.callerState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2 _v3))))))) := by
  exact @RawCallerClosure.callerConfig_equation_mirror

-- Independent literal expected type for RawCallerClosure.callerState.
noncomputable def PartACanonical.Types.p0600 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))))) := by
  exact @RawCallerClosure.callerState

-- Independent literal expected type for RawCallerClosure.callerState.eq_1.
noncomputable def PartACanonical.Types.p0601 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@RawCallerClosure.callerState _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0) _v1)))))) := by
  exact @RawCallerClosure.callerState.eq_1

-- Complete literal proposition for RawCallerClosure.callerState.eq_1; original proof reused.
theorem PartACanonical.Surface.m0356 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@RawCallerClosure.callerState _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0) _v1)))))) := by
  exact @RawCallerClosure.callerState.eq_1

-- Independent literal expected type for RawCallerClosure.callerState_equation_mirror.
noncomputable def PartACanonical.Types.p0602 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@RawCallerClosure.callerState _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0) _v1)))))) := by
  exact @RawCallerClosure.callerState_equation_mirror

-- Complete literal proposition for RawCallerClosure.callerState_equation_mirror; original proof reused.
theorem PartACanonical.Surface.m0357 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@RawCallerClosure.callerState _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0) _v1)))))) := by
  exact @RawCallerClosure.callerState_equation_mirror

-- Independent literal expected type for RawCallerClosure.deadline.
noncomputable def PartACanonical.Types.p0603 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @RawCallerClosure.deadline

-- Independent literal expected type for RawCallerClosure.machine.
noncomputable def PartACanonical.Types.p0604 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @RawCallerClosure.machine

-- Independent literal expected type for RawCallerClosure.machine.eq_1.
noncomputable def PartACanonical.Types.p0605 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@RawCallerClosure.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))))) := by
  exact @RawCallerClosure.machine.eq_1

-- Complete literal proposition for RawCallerClosure.machine.eq_1; original proof reused.
theorem PartACanonical.Surface.m0358 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@RawCallerClosure.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))))) := by
  exact @RawCallerClosure.machine.eq_1

-- Independent literal expected type for RawCallerClosure.machine_equation_mirror.
noncomputable def PartACanonical.Types.p0606 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@RawCallerClosure.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))))) := by
  exact @RawCallerClosure.machine_equation_mirror

-- Complete literal proposition for RawCallerClosure.machine_equation_mirror; original proof reused.
theorem PartACanonical.Surface.m0359 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@RawCallerClosure.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@CertificateGuardClosure.guard) (@Pnp3.Complexity.Uniform.V1.UniformTM.seq
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.machine) (@PhysicalCallerClosure.callerMachine _v0)))))) := by
  exact @RawCallerClosure.machine_equation_mirror

-- Independent literal expected type for RawCallerClosure.old.
noncomputable def PartACanonical.Types.p0607 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))))) := by
  exact @RawCallerClosure.old

-- Independent literal expected type for RawCallerClosure.oldConfig.
noncomputable def PartACanonical.Types.p0608 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CertificateGuardClosure.machine _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))
  _v1 _v2))))) := by
  exact @RawCallerClosure.oldConfig

-- Independent literal expected type for RawCallerClosure.raw.
noncomputable def PartACanonical.Types.p0609 :
(∀ (_v0 : (@Nat)),
(@RawCallerClosure.Target.Raw _v0)) := by
  exact @RawCallerClosure.raw

-- Complete literal proposition for RawCallerClosure.raw; original proof reused.
theorem PartACanonical.Surface.m0360 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0)
  _v1 _v3 _v2);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v7 : (∀ (_v7 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0)))) := (fun (_v7 :
  (@Bool)) =>
(@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 _v7))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (let _v10 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v11 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v12 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v13 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v11 _v1 _v10 _v2);
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v10) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v12 _v1 _v10 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v8)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v10)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1 _v10 _v15 _v13))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v8)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1
  _v10 _v15 _v13)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v11)))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v8)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1 _v10 _v15 _v13)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v11)) (@And (∀ (_v17 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1
  _v10 _v15 _v13)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v17))))))) (∀ (_v17 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1
  _v10 _v15 _v13)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0
  (@SerializedBody.entry _v17)))))))))) (@Or (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2)
  (@Option.none.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v8
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1
  _v10 _v8 _v13) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v11) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v10)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@RawCallerClosure.Target.Prelude._proof_1 _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10 _v13)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v15) (fun (_v17 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v15)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v16) (fun (_v18 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v16)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) _v1) (fun (_v19 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Sigma.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Sigma.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20)) _v15 _v17) (@Sigma.mk.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20)) _v16 _v18)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) (fun (_v20 :
  (@Nat)) =>
(fun (_v21 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) _v20)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v15 _v16 _v17 _v18)
  _v1 _v19)) (@And (@Ne.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And (@LE.le.{0} (@Nat)
  (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1 _v10 _v8 _v13) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v11)
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v10) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@RawCallerClosure.Target.Prelude._proof_1 _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10 _v13))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v15 _v16 _v17 _v18)
  (@Bool.false))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v15) (fun (_v17 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v15)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v16) (fun (_v18 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v16)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) _v1) (fun (_v19 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Sigma.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Sigma.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20)) _v15 _v17) (@Sigma.mk.{0, 0} (@Nat) (fun (_v20 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20)) _v16 _v18)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) (fun (_v20 :
  (@Nat)) =>
(fun (_v21 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v15 _v16) _v20)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v20))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v15 _v16 _v17 _v18)
  _v1 _v19)) (@And (@Eq.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v20
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v21 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v20
  _v21)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v20)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11)
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1 _v10 _v22 _v13))) (@OfNat.ofNat.{0} (@Nat) (77 : Nat) (@instOfNatNat
  (77 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1
  _v10 _v20 _v13) (@CertificateGuardClosure.config _v0 _v1 _v10 _v14)) (@And (∀ (_v22 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1 _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v20 _v22) _v13) (@CertificateGuardClosure.config _v0 _v1 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v10 _v22 _v14)))) (@And (let _v22 : (@Nat) :=
  (@TotalIngressClosure.allocation _v0 _v1);
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v24 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v25 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v26 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v24 _v1 _v22 _v2);
(let _v27 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v25 _v1 _v23 _v2);
(let _v28 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v22) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v25 _v1 _v22 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v21 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 _v21)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1 _v22 _v29 _v26))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 _v21)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1
  _v22 _v29 _v26)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v24)))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v21)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1 _v22 _v29 _v26)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v24)) (@And (∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1
  _v22 _v29 _v26)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v31)))))) (∀ (_v31 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1
  _v22 _v29 _v26)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v31))))))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v21
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1
  _v22 _v21 _v26) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v24) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v22)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@CertificateGuardClosure.Target.Frontier._proof_1 _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22 _v26)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v29) (fun (_v31 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v29)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v30) (fun (_v32 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v30)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v29 _v30) _v1) (fun (_v33 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v29 _v30) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v34 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34))) (@Sigma.{0, 0} (@Nat) (fun (_v34 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v34 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34))) (@Sigma.{0, 0} (@Nat) (fun (_v34 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v34 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34)) _v29 _v31) (@Sigma.mk.{0, 0} (@Nat) (fun (_v34 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34)) _v30 _v32)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v29 _v30) (fun (_v34 :
  (@Nat)) =>
(fun (_v35 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v29 _v30) _v34)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v34))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v29 _v30 _v31 _v32)
  _v1 _v33)) (@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v21 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v34)) (@And (∀ (_v35 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1 _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v35) _v26) (@TotalIngressClosure.config
  _v0 _v1 _v22 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v22 _v35 _v28)))) (@Exists.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v23 _v22) (fun (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v22)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v25) _v1 _v23 _v22 _v35 _v27 _v28) (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v36 _v34)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v36 (@Pnp3.Complexity.Uniform.V1.initialConfig _v25 _v1 _v23
  _v2)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 :
  Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v34)),
(let _v38 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v36 (@Pnp3.Complexity.Uniform.V1.initialConfig _v25 _v1 _v23
  _v2));
(∀ (_v39 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v25
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 _v38)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 _v38
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 _v38)))))
  (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 _v38)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)))))) (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v36 _v34)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1
  _v23 _v22 _v35 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v36 (@Pnp3.Complexity.Uniform.V1.initialConfig
  _v25 _v1 _v23 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v22 _v36
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v25 _v1 _v22 _v2))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v24) _v1 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v24 _v1 _v22 _v21 _v26) (@TotalIngressClosure.config _v0 _v1 _v22
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v23
  _v22 _v35 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v34 _v27)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1
  _v23 _v34 _v27)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v25)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v29 _v30 _v31 _v32) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v36 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v37 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v29 _v30) _v37) _v36) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)) (fun (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30) _v37) _v36) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30) (@Fin.append.{(0 + 1)} _v29 _v30 (@Bool) _v31 _v32))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30) (@Fin.append.{(0 + 1)} _v29 _v30 (@Bool) _v31 _v32)) (@Option.some.{0}
  (@Nat) _v37)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v29 _v30) (@Fin.append.{(0 + 1)} _v29 _v30 (@Bool) _v31 _v32)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v37) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v39 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30);
(let _v40 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v39 _v37) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v41 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v42 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v36);
(let _v43 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v37)) _v42) _v39);
(let _v44 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v39 _v43);
(let _v45 : (@Nat) := (@Cursor.Target.W _v0 _v36);
(let _v46 : (@Nat) := (@Cursor.Target.M _v0 _v36 _v37);
(let _v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v23) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v39 _v37) _v36) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v38);
(let _v48 : (∀ (_v48 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v29 _v30) _v23
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v29 _v30) _v23 (@SmallIngress.prepared _v29
  _v30 _v23 _v31 _v32 _v37 _v36) _v40 _v36));
(let _v49 : (∀ (_v49 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v48 _v39 _v37 _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v37)) _v42 _v42 (@Bool.false));
(let _v50 : (∀ (_v50 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v49 _v41 _v44) _v40 _v36 _v41 _v44);
(let _v51 : (∀ (_v51 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v50 _v40 _v36 _v41 _v44);
(let _v52 : (∀ (_v52 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v51 _v41 _v44 _v36);
(let _v53 : (∀ (_v53 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v52 _v40 _v36 _v41 _v44
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v36 _v0) _v0) _v45 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v41 _v44 _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v45)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v45);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v36 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v29 _v30 _v37))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23) _v47) _v42) _v41) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v43 _v39) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v36) _v44) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v45 _v44) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v41 _v44
  _v36 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23))
  (@And (∀ (_v54 : (@Nat)),
(∀ (_v55 : (@LE.le.{0} (@Nat) (@instLENat) _v46 _v54)),
(∀ (_v56 : (@LT.lt.{0} (@Nat) (@instLTNat) _v54 _v39)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v53 _v54) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v29 _v30 (@Bool)
  _v31 _v32 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30) _v54
  _v56))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25)
  _v1 _v23) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v34 _v27) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30)
  (@Fin.append.{(0 + 1)} _v29 _v30 (@Bool) _v31 _v32) _v46))) _v47 (fun (_v54 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23))) =>
(@SerializedBody.prepared _v53 _v39 _v46 _v41 _v44 _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v36 _v0) _v0) _v45 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23) _v54))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v36) (fun
  (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v36)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v39 _v46) (@And (∀ (_v55 : (@Fin _v45)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v29 _v30) (@Fin.append.{(0 + 1)} _v29 _v30 (@Bool) _v31 _v32) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v46 (@Fin.val _v45 _v55))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v36)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v36 (fun (_v55 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v36)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v36) (@Pnp3.Models.Circuit.input _v36 (@Fin.mk _v36
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v54)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v43 _v39)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v34 _v27) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v47 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)) (fun (_v55 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v23))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)) (fun (_v55 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23))) =>
(@_v49 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23) _v55))) _v47 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v43 _v39) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v44
  (@Pnp4.Frontier.ContractExpansion.bitLength _v36)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v36) _v44) (@Exists.{(0 + 1)} (@Nat) (fun (_v55 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v56 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v57 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v58 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v59 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v60 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v61 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v62 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v60 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v61 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v60)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v62 _v36) (@And (@Eq.{(0 + 1)} (@Nat) _v44 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v61 _v36) _v62)) (@And (@Eq.{(0 + 1)} (@Nat) _v55 (@Pnp4.Frontier.ContractExpansion.bitLength _v36)) (@And (@Eq.{(0 +
  1)} (@Nat) _v56 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v60) _v61) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v57 _v44) (@And (@Eq.{(0 + 1)} (@Nat) _v58 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v59 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v62 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v60 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v60 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v0) _v60) _v44) (@And (@Eq.{(0 + 1)} (@Nat) _v55
  (@Pnp4.Frontier.ContractExpansion.bitLength _v36)) (@And (@Eq.{(0 + 1)} (@Nat) _v56 _v44) (@And (@Eq.{(0 + 1)} (@Nat)
  _v57 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v58 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v59 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v60 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v60 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v36) _v60) _v44) (@And (@Eq.{(0 + 1)} (@Nat) _v55 _v44) (@And (@Eq.{(0 +
  1)} (@Nat) _v56 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v57 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v58 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v59 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v60 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v61 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v60 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v36) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v61 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v36 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v44 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v60 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v0) _v0)) _v61)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v55 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v36) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v60) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v56 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v36 _v0) _v0) _v61) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v57 _v44) (@And (@Eq.{(0 + 1)} (@Nat) _v58 _v61) (@Eq.{(0 + 1)} (@Nat) _v59
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v25 _v1 _v23 _v34 _v27) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v25) _v1 _v23 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v47 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)) (fun (_v55 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v23))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23)) (fun (_v55 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23))) =>
(@Cursor.Target.image _v49 _v0 _v39 _v36 _v37 _v41 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v23) _v55)))
  _v47 (@Option.some.{0} (@Bool) (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v11) _v1 _v10)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v11 _v1 _v10 _v8 _v13) (@CertificateGuardClosure.config _v0 _v1 _v10
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v10 _v21 _v14))))))))))))))))))))))))))))))))))))) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v8 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@RawCallerClosure.deadline _v0 _v1))
  (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v8)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v10 _v4) (@RawCallerClosure.oldConfig _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v10
  _v6))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@RawCallerClosure.machine _v0))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))) (∀ (_v12 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@RawCallerClosure.old _v0 (@_v7 _v12)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4) (@RawCallerClosure.oldConfig
  _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v8 _v6))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v10 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v8 _v6)) (@_v7 _v10)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4) (@RawCallerClosure.oldConfig
  _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v8 _v6))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v10 :
  (@Nat)) =>
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
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v17 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v21 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15);
(let _v22 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v21) _v17);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 _v22);
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v15);
(let _v25 : (@Nat) := (@Cursor.Target.M _v0 _v15 _v16);
(let _v26 : (∀ (_v26 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v20
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v20 (@SmallIngress.prepared _v10
  _v11 _v20 _v12 _v13 _v16 _v15) _v18 _v15));
(let _v27 : (∀ (_v27 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v26 _v17 _v16 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v16)) _v21 _v21 (@Bool.false));
(let _v28 : (∀ (_v28 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v27 _v19 _v23) _v18 _v15 _v19 _v23);
(let _v29 : (∀ (_v29 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v28 _v18 _v15 _v19 _v23);
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v29 _v19 _v23 _v15);
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v30 _v18 _v15 _v19 _v23
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v19 _v23 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v24)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v24);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v17) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24 _v23) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v10 _v11 _v16)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v21) _v19) (@Exists.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v32 : (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v8 _v4) (@RawCallerClosure.callerConfig _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v3
  (@PhysicalCallerClosure.oldState _v0 (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10
  _v11 (@Bool) _v12 _v13) _v25)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v32) (fun (_v33 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@SerializedBody.prepared _v31 _v17 _v25 _v19 _v23 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v15 _v0) _v0) _v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33)))))) (let _v33
  : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v34 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v17 (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13) _v25
  _v24);
(@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v36 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v36 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@RawCallerClosure.machine _v0))))) (@And (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v36 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v36 _v4))
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))))))
  (@RawCallerClosure.Target.RowsResult.match_1.{(0 + 1)} _v15 (fun (_v36 : (@Option.{0} (@Prod.{0, 0}
  (@Pnp3.Models.Circuit _v15) (@List.{0} (@Bool))))) =>
(Sort 0)) (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v15 (@Pnp4.Frontier.ContractExpansion.bitLength _v15)
  _v35) (fun (_v36 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v4) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33 _v32) (fun (_v37 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v31 _v17 _v16 _v15 _v34 _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 _v25 _v21 (@Pnp3.Core.vecOfNat _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v37)))))) (fun (_v36 : (@Pnp3.Models.Circuit _v15)) =>
(fun (_v37 : (@List.{0} (@Bool))) =>
(@Or (@And (@Not (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v15 _v36) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))
  _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33 _v32) (fun (_v38 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v31 _v17 _v16 _v15 _v34 _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 _v25 _v21 (@Pnp3.Core.vecOfNat _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v38)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Circuit.size _v15 _v36) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v15 _v0) _v0)) (let _v38 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v24 (@List.length.{0} (@Bool) _v37));
(let _v39 : (∀ (_v39 : (@Nat)),
(Sort 0)) := (fun (_v39 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v17 (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12
  _v13) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) _v39)) (@Pnp3.Models.Circuit.eval _v15 _v36 (@Pnp3.Core.vecOfNat _v15 _v39))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 _v24) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v37 (@List.drop.{0} (@Bool)
  _v38 _v35)) (@And (@Exists.{(0 + 1)} (∀ (_v40 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(@Nat)) (fun (_v40 : (∀ (_v40 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(@Nat))) =>
(@And (∀ (_v41 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v42 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41))),
(@_v39 _v42)))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v40 _v41) _v9) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 (@_v40 _v41) _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v17 (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13) _v25)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33 _v32) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(let _v44 : (@Nat) := (@SerializedBody.delimiter _v34 _v23 _v15 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))));
(let _v45 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) (@Fin.val
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)
  _v21) _v41))) (@Nat.decLe _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) (@Fin.val (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41))));
(let _v46 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v17 (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12
  _v13) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41)));
(let _v47 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v17 _v25) (@Nat.decLe _v17 _v25));
(let _v48 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v17 (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12
  _v13) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v45) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.some.{0} (@Bool) _v46) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) _v47)
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) _v25
  _v17) (@Nat.decLt _v25 _v17) _v48 (@Bool.false))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v44 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) (@Fin.val (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41))) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v17)) (@instDecidableAnd (@Eq.{(0
  + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) (@Fin.val (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)
  _v21) _v41))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v17)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) (@Fin.val
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)
  _v21) _v41))) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v17)) (@Option.none.{0}
  (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v17) (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v17) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v25 _v17)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v25) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v17)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v25) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v17) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v25) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43) _v17)) (@Option.none.{0} (@Bool))
  (@PhysicalCallerClosure.callerImage _v31 _v17 _v16 _v15 _v34 _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 _v25 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v21 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41))) (@Pnp3.Core.vecOfNat _v15 (@Fin.val (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v43))))))))))))))))))))) (∀ (_v41 : (@Fin (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(∀ (_v42 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v15) _v21))),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v41) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v42))),
(∀ (_v44 : (∀ (_v44 : (@Nat)),
(∀ (_v45 : (@LT.lt.{0} (@Nat) (@instLTNat) _v44 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v42))),
(@_v39 _v44)))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v40 _v41) (@_v40 _v42))))))))) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15))),
(@_v39 _v40))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v4) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33 _v32) (fun (_v40 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v31 _v17 _v16 _v15 _v34 _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 _v25 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v21 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)))
  (@Pnp3.Core.vecOfNat _v15 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Models.Circuit.size _v15
  _v36) _v38 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v38) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40))))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v40 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21)) (@And (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v40)),
(@_v39 _v41))) (@And (@Not (@_v39 _v40)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33 _v32) (fun (_v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v31 _v17 _v16 _v15 _v34 _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 _v25 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v21 _v40)) (@Pnp3.Core.vecOfNat _v15 _v40) (@Pnp3.Models.Circuit.size _v15 _v36) _v38
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v38) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v41)))))))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15))
  (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v21)),
(@_v39 _v40))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v4) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33 _v32) (fun (_v40 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v31 _v17 _v16 _v15 _v34 _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Pnp3.Core.vecOfNat _v15 _v21) (@Pnp3.Models.Circuit.size _v15 _v36) _v38 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v38) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v40))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @RawCallerClosure.raw

-- Independent literal expected type for RawCallerClosure.raw_mirror.
noncomputable def PartACanonical.Types.p0610 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0)
  _v1 _v3 _v2);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v7 : (∀ (_v7 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0)))) := (fun (_v7 :
  (@Bool)) =>
(@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 _v7))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (let _v10 : (@Nat) := _v8;
(let _v11 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v12 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v13 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v12 _v1 _v11 _v2);
(let _v15 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v13) _v1 _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v13 _v1 _v11 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v10)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v16 _v14))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v10)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v16 _v14)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v12)))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v16 _v14)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v12)) (@And (∀ (_v18 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v16 _v14)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v18))))))) (∀ (_v18 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v16 _v14)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0
  (@SerializedBody.entry _v18)))))))))) (@Or (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2)
  (@Option.none.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v10
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v10 _v14) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v12) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v16
  _v17))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v16 : (@Nat)) =>
(fun (_v17 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v17))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v16 _v17))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v11))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v16 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v11)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 _v14)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v16) (fun (_v18 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v16)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v17) (fun (_v19 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v17)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1) (fun (_v20 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v16 _v18) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v17 _v19)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) (fun (_v21 :
  (@Nat)) =>
(fun (_v22 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v21)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v16 _v17 _v18 _v19)
  _v1 _v20)) (@And (@Ne.{(0 + 1)} (@Nat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v16 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And (@LE.le.{0} (@Nat)
  (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v10 _v14) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v12)
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat)
  (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@True)
  (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)) (@instLTNat)
  (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))) (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder) (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(fun (_v22 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v21
  _v22))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(fun (_v22 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v22))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v21 : (@Nat)) =>
(fun (_v22 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v21 _v22))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v11))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v21 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v11)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 _v14)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v16 _v17
  _v18 _v19) (@Bool.false))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v16) (fun (_v18 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v16)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v17) (fun (_v19 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v17)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1) (fun (_v20 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v16 _v18) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v17 _v19)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) (fun (_v21 :
  (@Nat)) =>
(fun (_v22 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v21)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v16 _v17 _v18 _v19)
  _v1 _v20)) (@And (@Eq.{(0 + 1)} (@Nat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v16 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v21
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v22 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21
  _v22)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v21 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v21)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v23 _v14))) (@OfNat.ofNat.{0} (@Nat) (77 : Nat) (@instOfNatNat
  (77 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v21 _v14) (@CertificateGuardClosure.config _v0 _v1 _v11 _v15)) (@And (∀ (_v23 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v21 _v23) _v14) (@CertificateGuardClosure.config _v0 _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v13 _v1 _v11 _v23 _v15)))) (@And (let _v23 : (@Nat) := _v22;
(let _v24 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v25 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v26 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v27 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v28 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v26 _v1 _v24 _v2);
(let _v29 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v25 _v2);
(let _v30 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v24) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v24 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v23 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v31 _v23)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v24)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 _v31 _v28))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v31 _v23)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v31 _v28)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v26)))) (@And (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v23)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 _v31 _v28)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v26)) (@And (∀ (_v33 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v31 _v28)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v33)))))) (∀ (_v33 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v31 _v28)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v33))))))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v23
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v23 _v28) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v26) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v24)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v31 : (@Nat)) =>
(fun (_v32 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v31
  _v32))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v31 : (@Nat)) =>
(fun (_v32 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v32))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v31 : (@Nat)) =>
(fun (_v32 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v31 _v32))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v24)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v24)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v24))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v31 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v24))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v24)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 _v28)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v31) (fun (_v33 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v31)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v32) (fun (_v34 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v32)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v1) (fun (_v35 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Sigma.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Sigma.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36)) _v31 _v33) (@Sigma.mk.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36)) _v32 _v34)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) (fun (_v36 :
  (@Nat)) =>
(fun (_v37 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v36)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v31 _v32 _v33 _v34)
  _v1 _v35)) (@Exists.{(0 + 1)} (@Nat) (fun (_v36 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v36)) (@And (∀ (_v37 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v37) _v28) (@TotalIngressClosure.config
  _v0 _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v24 _v37 _v30)))) (@Exists.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v25 _v24) (fun (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v25 _v24)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v27) _v1 _v25 _v24 _v37 _v29 _v30) (@And (@IngressAllocation.Footprint _v27 _v1 _v25 _v2 _v36 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@IngressAllocation.MoveRoom _v27 _v1 _v25 _v2 _v36) (@And (@IngressAllocation.Trace _v27 _v1 _v25 _v24
  _v37 _v2 _v36) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v23 _v28) (@TotalIngressClosure.config _v0 _v1 _v24 (@IngressAllocation.extendConfig
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v25 _v24 _v37
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1
  _v25 _v36 _v29)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v27)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v31 _v32 _v33 _v34) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v31 _v32) _v39) _v38) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) _v39) _v38) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34)) (@Option.some.{0}
  (@Nat) _v39)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v39) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v41 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32);
(let _v42 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v41 _v39) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v43 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v44 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v38);
(let _v45 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v39)) _v44) _v41);
(let _v46 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 _v45);
(let _v47 : (@Nat) := (@Cursor.Target.W _v0 _v38);
(let _v48 : (@Nat) := (@Cursor.Target.M _v0 _v38 _v39);
(let _v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v25) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v41 _v39) _v38) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v40);
(let _v50 : (∀ (_v50 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v25
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v25 (@SmallIngress.prepared _v31
  _v32 _v25 _v33 _v34 _v39 _v38) _v42 _v38));
(let _v51 : (∀ (_v51 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v50 _v41 _v39 _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v39)) _v44 _v44 (@Bool.false));
(let _v52 : (∀ (_v52 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v51 _v43 _v46) _v42 _v38 _v43 _v46);
(let _v53 : (∀ (_v53 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v52 _v42 _v38 _v43 _v46);
(let _v54 : (∀ (_v54 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v53 _v43 _v46 _v38);
(let _v55 : (∀ (_v55 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v54 _v42 _v38 _v43 _v46
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0) _v47 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v43 _v46 _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v47)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v47);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v38 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v31 _v32 _v39))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v49) _v44) _v43) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v45 _v41) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v38) _v46) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v43 _v46
  _v38 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))
  (@And (∀ (_v56 : (@Nat)),
(∀ (_v57 : (@LE.le.{0} (@Nat) (@instLENat) _v48 _v56)),
(∀ (_v58 : (@LT.lt.{0} (@Nat) (@instLTNat) _v56 _v41)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v55 _v56) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool)
  _v33 _v34 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) _v56
  _v58))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27)
  _v1 _v25) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32)
  (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34) _v48))) _v49 (fun (_v56 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@SerializedBody.prepared _v55 _v41 _v48 _v43 _v46 _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v38 _v0) _v0) _v47 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v56))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v38) (fun
  (_v56 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v38)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v41 _v48) (@And (∀ (_v57 : (@Fin _v47)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v48 (@Fin.val _v47 _v57))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v38)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v38 (fun (_v57 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v38)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v38) (@Pnp3.Models.Circuit.input _v38 (@Fin.mk _v38
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v56)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v45 _v41)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v49 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v25))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@_v51 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v57))) _v49 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v45 _v41) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v46
  (@Pnp4.Frontier.ContractExpansion.bitLength _v38)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v38) _v46) (@Exists.{(0 + 1)} (@Nat) (fun (_v57 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v58 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v59 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v60 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v61 : (@Nat)) =>
(@CappedWeight.Target.Cap _v0 _v38 _v46 _v57 _v58 _v59 _v60 _v61))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v49 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v25))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@Cursor.Target.image _v51 _v0 _v41 _v38 _v39 _v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v57)))
  _v49 (@Option.some.{0} (@Bool) (@Bool.false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v10 _v14) (@CertificateGuardClosure.config _v0 _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v13 _v1 _v11 _v22 _v15)))))))))))))))))))))))))))))))))))))) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v8 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@RawCallerClosure.deadline _v0 _v1))
  (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v8)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v10 _v4) (@RawCallerClosure.oldConfig _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v10
  _v6))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@RawCallerClosure.machine _v0))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))) (∀ (_v12 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@RawCallerClosure.old _v0 (@_v7 _v12)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4) (@RawCallerClosure.oldConfig
  _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v8 _v6))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v10 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v8 _v6)) (@_v7 _v10)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4) (@RawCallerClosure.oldConfig
  _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v8 _v6))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v10 :
  (@Nat)) =>
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
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v17 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v21 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15);
(let _v22 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v21) _v17);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 _v22);
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v15);
(let _v25 : (@Nat) := (@Cursor.Target.M _v0 _v15 _v16);
(let _v26 : (∀ (_v26 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v20
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v20 (@SmallIngress.prepared _v10
  _v11 _v20 _v12 _v13 _v16 _v15) _v18 _v15));
(let _v27 : (∀ (_v27 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v26 _v17 _v16 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v16)) _v21 _v21 (@Bool.false));
(let _v28 : (∀ (_v28 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v27 _v19 _v23) _v18 _v15 _v19 _v23);
(let _v29 : (∀ (_v29 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v28 _v18 _v15 _v19 _v23);
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v29 _v19 _v23 _v15);
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v30 _v18 _v15 _v19 _v23
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v19 _v23 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v24)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v24);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v17) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24 _v23) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v10 _v11 _v16)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v21) _v19) (@Exists.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v32 : (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v8 _v4) (@RawCallerClosure.callerConfig _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v3
  (@PhysicalCallerClosure.oldState _v0 (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10
  _v11 (@Bool) _v12 _v13) _v25)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v32) (fun (_v33 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@SerializedBody.prepared _v31 _v17 _v25 _v19 _v23 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v15 _v0) _v0) _v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33)))))) (let _v33
  : (@Nat) := _v1;
(let _v34 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0);
(let _v35 : (@Nat) := _v25;
(let _v36 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16));
(let _v37 : (∀ (_v37 : (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  _v11))),
(@Bool)) := (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13);
(let _v38 : (∀ (_v38 : (@Nat)),
(@Option.{0} (@Bool))) := _v31;
(let _v39 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) := _v4;
(let _v40 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v41 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v33);
(let _v42 : (@List.{0} (@Bool)) := (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v10 _v11) _v37 _v35 _v24);
(@And (∀ (_v43 : (@Nat)),
(∀ (_v44 : (@LE.le.{0} (@Nat) (@instLENat) _v43 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v43 _v39))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@RawCallerClosure.machine _v0))))) (@And (∀ (_v43 : (@Nat)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v43 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v43 _v39))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v43 _v39))
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0)))))) (@RawCallerClosure.raw_mirror.match_1.{(0
  + 1)} _v15 (fun (_v43 : (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v15) (@List.{0} (@Bool))))) =>
(Sort 0)) (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v15 (@Pnp4.Frontier.ContractExpansion.bitLength _v15)
  _v42) (fun (_v43 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v39) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 _v21 (@Pnp3.Core.vecOfNat _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v44)))))) (fun (_v43 : (@Pnp3.Models.Circuit _v15)) =>
(fun (_v44 : (@List.{0} (@Bool))) =>
(@Or (@And (@Not (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v15 _v43) _v34)) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))
  _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v39)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 _v21 (@Pnp3.Core.vecOfNat _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v45)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Circuit.size _v15 _v43) _v34) (let _v45 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v24 (@List.length.{0} (@Bool) _v44));
(let _v46 : (∀ (_v46 : (@Nat)),
(Sort 0)) := (fun (_v46 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v37 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 _v46)) (@Pnp3.Models.Circuit.eval _v15 _v43 (@Pnp3.Core.vecOfNat _v15 _v46))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 _v24) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v44 (@List.drop.{0} (@Bool)
  _v45 _v42)) (@And (@Exists.{(0 + 1)} (∀ (_v47 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(@Nat)) (fun (_v47 : (∀ (_v47 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(@Nat))) =>
(@And (∀ (_v48 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21))),
(∀ (_v49 : (∀ (_v49 : (@Nat)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v49 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))),
(@_v46 _v49)))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v47 _v48) _v9) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 (@_v47 _v48) _v39)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11)
  _v37 _v35)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v50 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(let _v51 : (@Nat) := (@SerializedBody.delimiter _v41 _v23 _v15 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))));
(let _v52 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@Nat.decLe _v17 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))));
(let _v53 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v37 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48)));
(let _v54 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v17 _v35) (@Nat.decLe _v17 _v35));
(let _v55 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v52) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.some.{0} (@Bool) _v53) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) _v54)
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) _v35
  _v17) (@Nat.decLt _v35 _v17) _v55 (@Bool.false))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50) _v17)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v35
  _v17) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v17) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v35 _v17)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v35) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17)) (@Option.none.{0} (@Bool))
  (@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@Max.max.{0} (@Nat)
  (@Nat.instMax_mathlib) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@Pnp3.Core.vecOfNat _v15 (@Fin.val
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)
  _v21) _v48)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v24 _v34 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50))))))))))))))))))))) (∀ (_v48 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(∀ (_v49 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v15) _v21))),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v49))),
(∀ (_v51 : (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v49))),
(@_v46 _v51)))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v47 _v48) (@_v47 _v49))))))))) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15))),
(@_v46 _v47))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v39) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v47 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@Max.max.{0} (@Nat)
  (@Nat.instMax_mathlib) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15))) (@Pnp3.Core.vecOfNat _v15 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Models.Circuit.size _v15 _v43) _v45 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v24 _v45) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v47))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v47 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v47 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21)) (@And (∀ (_v48 : (@Nat)),
(∀ (_v49 : (@LT.lt.{0} (@Nat) (@instLTNat) _v48 _v47)),
(@_v46 _v48))) (@And (@Not (@_v46 _v47)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v39)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v48 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@Max.max.{0} (@Nat)
  (@Nat.instMax_mathlib) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 _v47)) (@Pnp3.Core.vecOfNat _v15 _v47) (@Pnp3.Models.Circuit.size _v15
  _v43) _v45 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v45) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v48))))))))))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15))
  (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v21)),
(@_v46 _v47))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v39) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v47 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Pnp3.Core.vecOfNat _v15 _v21) (@Pnp3.Models.Circuit.size _v15 _v43) _v45 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v45) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v47)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @RawCallerClosure.raw_mirror

-- Complete literal proposition for RawCallerClosure.raw_mirror; original proof reused.
theorem PartACanonical.Surface.m0361 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0)
  _v1 _v3 _v2);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v7 : (∀ (_v7 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0)))) := (fun (_v7 :
  (@Bool)) =>
(@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 _v7))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (let _v10 : (@Nat) := _v8;
(let _v11 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v12 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v13 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v12 _v1 _v11 _v2);
(let _v15 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v13) _v1 _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v13 _v1 _v11 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v10)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v16 _v14))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v10)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v16 _v14)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v12)))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v16 _v14)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v12)) (@And (∀ (_v18 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v16 _v14)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v18))))))) (∀ (_v18 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v16 _v14)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0
  (@SerializedBody.entry _v18)))))))))) (@Or (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2)
  (@Option.none.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v10
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v10 _v14) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v12) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v16
  _v17))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v16 : (@Nat)) =>
(fun (_v17 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v17))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v16 : (@Nat)) =>
(fun (_v17 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v16 _v17))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v11))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v16 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v11)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 _v14)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v16) (fun (_v18 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v16)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v17) (fun (_v19 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v17)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1) (fun (_v20 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v16 _v18) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v17 _v19)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) (fun (_v21 :
  (@Nat)) =>
(fun (_v22 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v21)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v16 _v17 _v18 _v19)
  _v1 _v20)) (@And (@Ne.{(0 + 1)} (@Nat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v16 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And (@LE.le.{0} (@Nat)
  (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v10 _v14) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v12)
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat)
  (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@True)
  (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)) (@instLTNat)
  (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))) (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder) (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(fun (_v22 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v21
  _v22))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(fun (_v22 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v22))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v21 : (@Nat)) =>
(fun (_v22 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v21 _v22))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v11)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v11) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v11))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v21 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v11))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v11)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v11))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11 _v14)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v16 _v17
  _v18 _v19) (@Bool.false))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v16) (fun (_v18 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v16)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v17) (fun (_v19 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v17)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1) (fun (_v20 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v16 _v18) (@Sigma.mk.{0, 0} (@Nat) (fun (_v21 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21)) _v17 _v19)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) (fun (_v21 :
  (@Nat)) =>
(fun (_v22 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v16 _v17) _v21)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v21))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v16 _v17 _v18 _v19)
  _v1 _v20)) (@And (@Eq.{(0 + 1)} (@Nat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v16 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v21
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v22 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21
  _v22)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v21 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v21)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12)
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v23 _v14))) (@OfNat.ofNat.{0} (@Nat) (77 : Nat) (@instOfNatNat
  (77 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1
  _v11 _v21 _v14) (@CertificateGuardClosure.config _v0 _v1 _v11 _v15)) (@And (∀ (_v23 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v21 _v23) _v14) (@CertificateGuardClosure.config _v0 _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v13 _v1 _v11 _v23 _v15)))) (@And (let _v23 : (@Nat) := _v22;
(let _v24 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v25 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v26 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v27 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v28 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v26 _v1 _v24 _v2);
(let _v29 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v25 _v2);
(let _v30 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v24) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v24 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v23 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v31 _v23)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v24)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 _v31 _v28))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v31 _v23)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v31 _v28)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v26)))) (@And (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v23)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 _v31 _v28)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v26)) (@And (∀ (_v33 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v31 _v28)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v33)))))) (∀ (_v33 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v31 _v28)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v33))))))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v23
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1
  _v24 _v23 _v28) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v26) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v24)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v31 : (@Nat)) =>
(fun (_v32 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v31
  _v32))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v31 : (@Nat)) =>
(fun (_v32 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v32))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v31 : (@Nat)) =>
(fun (_v32 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v31 _v32))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v24) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v24)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v24)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v24))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v31 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v24))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v24)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v24))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24 _v28)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v31) (fun (_v33 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v31)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v32) (fun (_v34 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v32)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v1) (fun (_v35 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Sigma.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Sigma.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36)) _v31 _v33) (@Sigma.mk.{0, 0} (@Nat) (fun (_v36 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36)) _v32 _v34)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) (fun (_v36 :
  (@Nat)) =>
(fun (_v37 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v36)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v36))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v31 _v32 _v33 _v34)
  _v1 _v35)) (@Exists.{(0 + 1)} (@Nat) (fun (_v36 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v36)) (@And (∀ (_v37 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v37) _v28) (@TotalIngressClosure.config
  _v0 _v1 _v24 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v24 _v37 _v30)))) (@Exists.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v25 _v24) (fun (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v25 _v24)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v27) _v1 _v25 _v24 _v37 _v29 _v30) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LE.le.{0} (@Nat) (@instLENat) _v38 _v36)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v38 (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v25
  _v2)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 :
  Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 _v36)),
(let _v40 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v38 (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v25
  _v2));
(∀ (_v41 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v27
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 _v40)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 _v40
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 _v40)))))
  (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 _v40)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)))))) (@And (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LE.le.{0} (@Nat) (@instLENat) _v38 _v36)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1
  _v25 _v24 _v37 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v38 (@Pnp3.Complexity.Uniform.V1.initialConfig
  _v27 _v1 _v25 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v24 _v38
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v27 _v1 _v24 _v2))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v26) _v1 _v24)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v26 _v1 _v24 _v23 _v28) (@TotalIngressClosure.config _v0 _v1 _v24
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v25
  _v24 _v37 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1
  _v25 _v36 _v29)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v27)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v31 _v32 _v33 _v34) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v31 _v32) _v39) _v38) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) _v39) _v38) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34)) (@Option.some.{0}
  (@Nat) _v39)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v39) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v41 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32);
(let _v42 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v41 _v39) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v43 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v44 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v38);
(let _v45 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v39)) _v44) _v41);
(let _v46 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 _v45);
(let _v47 : (@Nat) := (@Cursor.Target.W _v0 _v38);
(let _v48 : (@Nat) := (@Cursor.Target.M _v0 _v38 _v39);
(let _v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v25) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v41 _v39) _v38) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v40);
(let _v50 : (∀ (_v50 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v25
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v31 _v32) _v25 (@SmallIngress.prepared _v31
  _v32 _v25 _v33 _v34 _v39 _v38) _v42 _v38));
(let _v51 : (∀ (_v51 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v50 _v41 _v39 _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v39)) _v44 _v44 (@Bool.false));
(let _v52 : (∀ (_v52 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v51 _v43 _v46) _v42 _v38 _v43 _v46);
(let _v53 : (∀ (_v53 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v52 _v42 _v38 _v43 _v46);
(let _v54 : (∀ (_v54 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v53 _v43 _v46 _v38);
(let _v55 : (∀ (_v55 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v54 _v42 _v38 _v43 _v46
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0) _v47 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v43 _v46 _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v47)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v47);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v38 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v31 _v32 _v39))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v49) _v44) _v43) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v45 _v41) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v38) _v46) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v43 _v46
  _v38 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))
  (@And (∀ (_v56 : (@Nat)),
(∀ (_v57 : (@LE.le.{0} (@Nat) (@instLENat) _v48 _v56)),
(∀ (_v58 : (@LT.lt.{0} (@Nat) (@instLTNat) _v56 _v41)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v55 _v56) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool)
  _v33 _v34 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) _v56
  _v58))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27)
  _v1 _v25) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32)
  (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34) _v48))) _v49 (fun (_v56 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@SerializedBody.prepared _v55 _v41 _v48 _v43 _v46 _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v38 _v0) _v0) _v47 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v56))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v38) (fun
  (_v56 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v38)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v41 _v48) (@And (∀ (_v57 : (@Fin _v47)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v31 _v32) (@Fin.append.{(0 + 1)} _v31 _v32 (@Bool) _v33 _v34) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v48 (@Fin.val _v47 _v57))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v38)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v38 (fun (_v57 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v38)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v38) (@Pnp3.Models.Circuit.input _v38 (@Fin.mk _v38
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v56)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v45 _v41)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v49 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v25))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@_v51 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v57))) _v49 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v45 _v41) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v46
  (@Pnp4.Frontier.ContractExpansion.bitLength _v38)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v38) _v46) (@Exists.{(0 + 1)} (@Nat) (fun (_v57 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v58 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v59 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v60 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v61 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v62 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v63 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v64 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v62 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v63 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v62)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v64 _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v46 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v63 _v38) _v64)) (@And (@Eq.{(0 + 1)} (@Nat) _v57 (@Pnp4.Frontier.ContractExpansion.bitLength _v38)) (@And (@Eq.{(0 +
  1)} (@Nat) _v58 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v62) _v63) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v59 _v46) (@And (@Eq.{(0 + 1)} (@Nat) _v60 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v61 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v64 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v62 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v62 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v0) _v62) _v46) (@And (@Eq.{(0 + 1)} (@Nat) _v57
  (@Pnp4.Frontier.ContractExpansion.bitLength _v38)) (@And (@Eq.{(0 + 1)} (@Nat) _v58 _v46) (@And (@Eq.{(0 + 1)} (@Nat)
  _v59 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v60 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v61 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v62 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v62 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v38) _v62) _v46) (@And (@Eq.{(0 + 1)} (@Nat) _v57 _v46) (@And (@Eq.{(0 +
  1)} (@Nat) _v58 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v59 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v60 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v61 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v62 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v63 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v62 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v38) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v63 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v38 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v46 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v62 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0)) _v63)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v57 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v38) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v62) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v58 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v38 _v0) _v0) _v63) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v59 _v46) (@And (@Eq.{(0 + 1)} (@Nat) _v60 _v63) (@Eq.{(0 + 1)} (@Nat) _v61
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v27 _v1 _v25 _v36 _v29) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v27) _v1 _v25 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v49 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v25))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25)) (fun (_v57 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25))) =>
(@Cursor.Target.image _v51 _v0 _v41 _v38 _v39 _v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v25) _v57)))
  _v49 (@Option.some.{0} (@Bool) (@Bool.false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v12 _v1 _v11 _v10 _v14) (@CertificateGuardClosure.config _v0 _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v13 _v1 _v11 _v22 _v15)))))))))))))))))))))))))))))))))))))) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v8 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@RawCallerClosure.deadline _v0 _v1))
  (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v8)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v10 _v4) (@RawCallerClosure.oldConfig _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v10
  _v6))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@RawCallerClosure.machine _v0))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))) (∀ (_v12 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v10 _v4))
  (@RawCallerClosure.old _v0 (@_v7 _v12)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4) (@RawCallerClosure.oldConfig
  _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v8 _v6))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v10 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v8 _v6)) (@_v7 _v10)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v4) (@RawCallerClosure.oldConfig
  _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v8 _v6))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v10 :
  (@Nat)) =>
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
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v17 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11);
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v21 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15);
(let _v22 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v21) _v17);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 _v22);
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v15);
(let _v25 : (@Nat) := (@Cursor.Target.M _v0 _v15 _v16);
(let _v26 : (∀ (_v26 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v20
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v10 _v11) _v20 (@SmallIngress.prepared _v10
  _v11 _v20 _v12 _v13 _v16 _v15) _v18 _v15));
(let _v27 : (∀ (_v27 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v26 _v17 _v16 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v16)) _v21 _v21 (@Bool.false));
(let _v28 : (∀ (_v28 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v27 _v19 _v23) _v18 _v15 _v19 _v23);
(let _v29 : (∀ (_v29 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v28 _v18 _v15 _v19 _v23);
(let _v30 : (∀ (_v30 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v29 _v19 _v23 _v15);
(let _v31 : (∀ (_v31 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v30 _v18 _v15 _v19 _v23
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v24 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v19 _v23 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v24)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v24);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v17) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24 _v23) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v10 _v11 _v16)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v21) _v19) (@Exists.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v32 : (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v8 _v4) (@RawCallerClosure.callerConfig _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v3
  (@PhysicalCallerClosure.oldState _v0 (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10
  _v11 (@Bool) _v12 _v13) _v25)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v32) (fun (_v33 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@SerializedBody.prepared _v31 _v17 _v25 _v19 _v23 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v15 _v0) _v0) _v24 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v33)))))) (let _v33
  : (@Nat) := _v1;
(let _v34 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0);
(let _v35 : (@Nat) := _v25;
(let _v36 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16));
(let _v37 : (∀ (_v37 : (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  _v11))),
(@Bool)) := (@Fin.append.{(0 + 1)} _v10 _v11 (@Bool) _v12 _v13);
(let _v38 : (∀ (_v38 : (@Nat)),
(@Option.{0} (@Bool))) := _v31;
(let _v39 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) := _v4;
(let _v40 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v15) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v41 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v33);
(let _v42 : (@List.{0} (@Bool)) := (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v10 _v11) _v37 _v35 _v24);
(@And (∀ (_v43 : (@Nat)),
(∀ (_v44 : (@LE.le.{0} (@Nat) (@instLENat) _v43 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v43 _v39))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@RawCallerClosure.machine _v0))))) (@And (∀ (_v43 : (@Nat)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) _v43 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v43 _v39))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v43 _v39))
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0)))))) (@RawCallerClosure.raw_mirror.match_1.{(0
  + 1)} _v15 (fun (_v43 : (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v15) (@List.{0} (@Bool))))) =>
(Sort 0)) (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v15 (@Pnp4.Frontier.ContractExpansion.bitLength _v15)
  _v42) (fun (_v43 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v39) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 _v21 (@Pnp3.Core.vecOfNat _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v44)))))) (fun (_v43 : (@Pnp3.Models.Circuit _v15)) =>
(fun (_v44 : (@List.{0} (@Bool))) =>
(@Or (@And (@Not (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v15 _v43) _v34)) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))
  _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v39)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 _v21 (@Pnp3.Core.vecOfNat _v15
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v45)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Circuit.size _v15 _v43) _v34) (let _v45 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v24 (@List.length.{0} (@Bool) _v44));
(let _v46 : (∀ (_v46 : (@Nat)),
(Sort 0)) := (fun (_v46 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v37 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 _v46)) (@Pnp3.Models.Circuit.eval _v15 _v43 (@Pnp3.Core.vecOfNat _v15 _v46))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 _v24) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v44 (@List.drop.{0} (@Bool)
  _v45 _v42)) (@And (@Exists.{(0 + 1)} (∀ (_v47 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(@Nat)) (fun (_v47 : (∀ (_v47 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(@Nat))) =>
(@And (∀ (_v48 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21))),
(∀ (_v49 : (∀ (_v49 : (@Nat)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v49 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))),
(@_v46 _v49)))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v47 _v48) _v9) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 (@_v47 _v48) _v39)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11)
  _v37 _v35)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v50 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(let _v51 : (@Nat) := (@SerializedBody.delimiter _v41 _v23 _v15 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))));
(let _v52 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v17 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@Nat.decLe _v17 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))));
(let _v53 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v37 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48)));
(let _v54 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v17 _v35) (@Nat.decLe _v17 _v35));
(let _v55 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) _v37 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v52) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.some.{0} (@Bool) _v53) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) _v54)
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) _v35
  _v17) (@Nat.decLt _v35 _v17) _v55 (@Bool.false))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v51 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v36 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50) _v17)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v35
  _v17) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v17) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v35 _v17)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v35) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v35) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v50) _v17)) (@Option.none.{0} (@Bool))
  (@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@Max.max.{0} (@Nat)
  (@Nat.instMax_mathlib) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48))) (@Pnp3.Core.vecOfNat _v15 (@Fin.val
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)
  _v21) _v48)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v24 _v34 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v50))))))))))))))))))))) (∀ (_v48 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21))),
(∀ (_v49 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v15) _v21))),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v48) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v49))),
(∀ (_v51 : (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) _v49))),
(@_v46 _v51)))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v47 _v48) (@_v47 _v49))))))))) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15))),
(@_v46 _v47))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v39) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v47 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@Max.max.{0} (@Nat)
  (@Nat.instMax_mathlib) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15))) (@Pnp3.Core.vecOfNat _v15 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Models.Circuit.size _v15 _v43) _v45 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v24 _v45) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v47))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v47 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v47 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v15) _v21)) (@And (∀ (_v48 : (@Nat)),
(∀ (_v49 : (@LT.lt.{0} (@Nat) (@instLTNat) _v48 _v47)),
(@_v46 _v48))) (@And (@Not (@_v46 _v47)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v3 _v9 _v39)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v48 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@Max.max.{0} (@Nat)
  (@Nat.instMax_mathlib) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 _v47)) (@Pnp3.Core.vecOfNat _v15 _v47) (@Pnp3.Models.Circuit.size _v15
  _v43) _v45 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v45) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v48))))))))))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15))
  (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v21)),
(@_v46 _v47))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v3 _v9 _v39) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@RawCallerClosure.machine _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v40 _v32) (fun (_v47 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@PhysicalCallerClosure.callerImage _v38 _v17 _v16 _v15 _v41 _v23 _v34 _v24 _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Pnp3.Core.vecOfNat _v15 _v21) (@Pnp3.Models.Circuit.size _v15 _v43) _v45 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v24 _v45) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  _v47)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @RawCallerClosure.raw_mirror

-- Independent literal expected type for RawFrontier.Audit.check_capacity_reject.
noncomputable def PartACanonical.Types.p0611 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Nat) _v3))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v3 _v10)) (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.decBit _v1 _v2 _v5 _v6 _v3
  (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.borrow _v1 _v2 _v5 _v6 _v3) _v10))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v11)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 _v11) (@Bool.false))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3) _v4)),
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v5 _v6));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v5 _v6) (@Bool.false))
  (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14)))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Eq.{(0 + 1)} (∀ (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2 _v13 _v5 _v6 _v3 (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2
  _v3)))))))))))))))))))))))))) := by
  exact @RawFrontier.Audit.check_capacity_reject

-- Complete literal proposition for RawFrontier.Audit.check_capacity_reject; original proof reused.
theorem PartACanonical.Surface.m0362 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Nat) _v3))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v3 _v10)) (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.decBit _v1 _v2 _v5 _v6 _v3
  (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.borrow _v1 _v2 _v5 _v6 _v3) _v10))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v11)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 _v11) (@Bool.false))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3) _v4)),
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v5 _v6));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v5 _v6) (@Bool.false))
  (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14)))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Eq.{(0 + 1)} (∀ (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2 _v13 _v5 _v6 _v3 (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2
  _v3)))))))))))))))))))))))))) := by
  exact @RawFrontier.Audit.check_capacity_reject

-- Independent literal expected type for RawFrontier.Audit.check_early_reject_sound.
noncomputable def PartACanonical.Types.p0612 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v5)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))) := by
  exact @RawFrontier.Audit.check_early_reject_sound

-- Complete literal proposition for RawFrontier.Audit.check_early_reject_sound; original proof reused.
theorem PartACanonical.Surface.m0363 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v5)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))) := by
  exact @RawFrontier.Audit.check_early_reject_sound

-- Independent literal expected type for RawFrontier.Audit.check_frontier_impossible.
noncomputable def PartACanonical.Types.p0613 :
(∀ (_v0 : (@Nat)),
(@Not (∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v6 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (16777216 : Nat) (@instOfNatNat (16777216 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v6)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (∀ (_v7 : (@Eq.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))))))))) := by
  exact @RawFrontier.Audit.check_frontier_impossible

-- Complete literal proposition for RawFrontier.Audit.check_frontier_impossible; original proof reused.
theorem PartACanonical.Surface.m0364 :
(∀ (_v0 : (@Nat)),
(@Not (∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v6 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (16777216 : Nat) (@instOfNatNat (16777216 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v6)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (∀ (_v7 : (@Eq.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))))))))) := by
  exact @RawFrontier.Audit.check_frontier_impossible

-- Independent literal expected type for RawFrontier.Audit.check_producer_reject_frontier.
noncomputable def PartACanonical.Types.p0614 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SmallIngress.producer)))),
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false))))))))))))))))) := by
  exact @RawFrontier.Audit.check_producer_reject_frontier

-- Complete literal proposition for RawFrontier.Audit.check_producer_reject_frontier; original proof reused.
theorem PartACanonical.Surface.m0365 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SmallIngress.producer)))),
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false))))))))))))))))) := by
  exact @RawFrontier.Audit.check_producer_reject_frontier

-- Independent literal expected type for RawFrontier.Audit.check_raw_stalls.
noncomputable def PartACanonical.Types.p0615 :
(∀ (_v0 : (@Nat)),
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))));
(let _v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))));
(@And (∀ (_v3 : (@Nat)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))))) (@Exists.{(0
  + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@OfNat.ofNat.{0} (@Nat) (73752 : Nat) (@instOfNatNat (73752 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine
  _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool)
  (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat)
  (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (15 : Nat) (@instOfNatNat
  (15 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)))))))))))) := by
  exact @RawFrontier.Audit.check_raw_stalls

-- Complete literal proposition for RawFrontier.Audit.check_raw_stalls; original proof reused.
theorem PartACanonical.Surface.m0366 :
(∀ (_v0 : (@Nat)),
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))));
(let _v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))));
(@And (∀ (_v3 : (@Nat)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))))) (@Exists.{(0
  + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@OfNat.ofNat.{0} (@Nat) (73752 : Nat) (@instOfNatNat (73752 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine
  _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool)
  (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat)
  (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (15 : Nat) (@instOfNatNat
  (15 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)))))))))))) := by
  exact @RawFrontier.Audit.check_raw_stalls

-- Independent literal expected type for RawFrontier.Audit.check_sample_relation_false.
noncomputable def PartACanonical.Types.p0616 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))))) (@Fin.elim0.{(0 +
  1)} (@Bool))) (@Bool.false))) := by
  exact @RawFrontier.Audit.check_sample_relation_false

-- Complete literal proposition for RawFrontier.Audit.check_sample_relation_false; original proof reused.
theorem PartACanonical.Surface.m0367 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))))) (@Fin.elim0.{(0 +
  1)} (@Bool))) (@Bool.false))) := by
  exact @RawFrontier.Audit.check_sample_relation_false

-- Independent literal expected type for RawFrontier.Audit.check_syntactic_reject.
noncomputable def PartACanonical.Types.p0617 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Or (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.false)) (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.none.{0} (@Nat))))),
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v7)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v7)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)}
  (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)) (@And (@Eq.{(0 + 1)} (∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4)) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))))))))))))))))) := by
  exact @RawFrontier.Audit.check_syntactic_reject

-- Complete literal proposition for RawFrontier.Audit.check_syntactic_reject; original proof reused.
theorem PartACanonical.Surface.m0368 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Or (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.false)) (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.none.{0} (@Nat))))),
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v7)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v7)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)}
  (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)) (@And (@Eq.{(0 + 1)} (∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4)) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))))))))))))))))) := by
  exact @RawFrontier.Audit.check_syntactic_reject

-- Independent literal expected type for RawFrontier.Audit.pin_Frontier.
noncomputable def PartACanonical.Types.p0618 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RawFrontier.Audit.pin_Frontier

-- Independent literal expected type for RawFrontier.Fixtures.check_negative_words.
noncomputable def PartACanonical.Types.p0619 :
(∀ (_v0 : (@Nat)),
(@And (@Exists.{(0 + 1)} (@Nat) (fun (_v1 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v1 (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) _v1 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool)) (@Fin.elim0.{(0 +
  1)} (@Bool)))))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool))
  (@Fin.elim0.{(0 + 1)} (@Bool))) (@Bool.false)))))) (@And (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (16 :
  Nat) (@instOfNatNat (16 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1))) (@Bool.false)));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (147968 : Nat) (@instOfNatNat (147968 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat)
  (@instOfNatNat (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat
  (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (16 : Nat)
  (@instOfNatNat (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false))))))) (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0}
  (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (346112 : Nat) (@instOfNatNat (346112 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat)
  (@instOfNatNat (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat
  (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false)))))))))) := by
  exact @RawFrontier.Fixtures.check_negative_words

-- Complete literal proposition for RawFrontier.Fixtures.check_negative_words; original proof reused.
theorem PartACanonical.Surface.m0369 :
(∀ (_v0 : (@Nat)),
(@And (@Exists.{(0 + 1)} (@Nat) (fun (_v1 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v1 (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) _v1 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool)) (@Fin.elim0.{(0 +
  1)} (@Bool)))))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool))
  (@Fin.elim0.{(0 + 1)} (@Bool))) (@Bool.false)))))) (@And (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (16 :
  Nat) (@instOfNatNat (16 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1))) (@Bool.false)));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (147968 : Nat) (@instOfNatNat (147968 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat)
  (@instOfNatNat (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat
  (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (16 : Nat)
  (@instOfNatNat (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false))))))) (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0}
  (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (346112 : Nat) (@instOfNatNat (346112 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat)
  (@instOfNatNat (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat
  (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false)))))))))) := by
  exact @RawFrontier.Fixtures.check_negative_words

-- Independent literal expected type for RawFrontier.Fixtures.negative_words.
noncomputable def PartACanonical.Types.p0620 :
(∀ (_v0 : (@Nat)),
(@And (@Exists.{(0 + 1)} (@Nat) (fun (_v1 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v1 (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) _v1 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool)) (@Fin.elim0.{(0 +
  1)} (@Bool)))))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool))
  (@Fin.elim0.{(0 + 1)} (@Bool))) (@Bool.false)))))) (@And (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (16 :
  Nat) (@instOfNatNat (16 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1))) (@Bool.false)));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (147968 : Nat) (@instOfNatNat (147968 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat)
  (@instOfNatNat (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat
  (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (16 : Nat)
  (@instOfNatNat (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false))))))) (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0}
  (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (346112 : Nat) (@instOfNatNat (346112 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat)
  (@instOfNatNat (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat
  (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false)))))))))) := by
  exact @RawFrontier.Fixtures.negative_words

-- Complete literal proposition for RawFrontier.Fixtures.negative_words; original proof reused.
theorem PartACanonical.Surface.m0370 :
(∀ (_v0 : (@Nat)),
(@And (@Exists.{(0 + 1)} (@Nat) (fun (_v1 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v1 (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) _v1 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool)) (@Fin.elim0.{(0 +
  1)} (@Bool)))))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.elim0.{(0 + 1)} (@Bool))
  (@Fin.elim0.{(0 + 1)} (@Bool))) (@Bool.false)))))) (@And (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (16 :
  Nat) (@instOfNatNat (16 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) _v1))) (@Bool.false)));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (147968 : Nat) (@instOfNatNat (147968 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat)
  (@instOfNatNat (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (18496 : Nat) (@instOfNatNat
  (18496 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat
  (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (16 : Nat)
  (@instOfNatNat (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false))))))) (let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) := (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) =>
(@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25
  : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Nat.testBit (@OfNat.ofNat.{0} (@Nat) (178 : Nat) (@instOfNatNat (178 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0}
  (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) _v1)
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@OfNat.ofNat.{0} (@Nat) (346112 : Nat) (@instOfNatNat (346112 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat)
  (@instOfNatNat (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) _v2 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (43264 : Nat) (@instOfNatNat
  (43264 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat
  (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)}
  (@Bool))) (@Bool.false)))))))))) := by
  exact @RawFrontier.Fixtures.negative_words

-- Independent literal expected type for RawFrontier.Target.Frontier.
noncomputable def PartACanonical.Types.p0621 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @RawFrontier.Target.Frontier

-- Independent literal expected type for RawFrontier.capacity_reject.
noncomputable def PartACanonical.Types.p0622 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Nat) _v3))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v3 _v10)) (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.decBit _v1 _v2 _v5 _v6 _v3
  (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.borrow _v1 _v2 _v5 _v6 _v3) _v10))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v11)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 _v11) (@Bool.false))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3) _v4)),
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v5 _v6));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v5 _v6) (@Bool.false))
  (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14)))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Eq.{(0 + 1)} (∀ (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2 _v13 _v5 _v6 _v3 (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2
  _v3)))))))))))))))))))))))))) := by
  exact @RawFrontier.capacity_reject

-- Complete literal proposition for RawFrontier.capacity_reject; original proof reused.
theorem PartACanonical.Surface.m0371 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Nat) _v3))),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  _v3 _v10)) (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.decBit _v1 _v2 _v5 _v6 _v3
  (@Pnp3.Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement.borrow _v1 _v2 _v5 _v6 _v3) _v10))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v11)),
(@Eq.{(0 + 1)} (@Bool) (@Nat.testBit _v4 _v11) (@Bool.false))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3) _v4)),
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v5 _v6));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v16 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v5 _v6) (@Bool.false))
  (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14)))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Eq.{(0 + 1)} (∀ (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v13 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2 _v13 _v5 _v6 _v3 (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v4 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v3)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2
  _v3)))))))))))))))))))))))))) := by
  exact @RawFrontier.capacity_reject

-- Independent literal expected type for RawFrontier.early_reject_sound.
noncomputable def PartACanonical.Types.p0623 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v5)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))) := by
  exact @RawFrontier.early_reject_sound

-- Complete literal proposition for RawFrontier.early_reject_sound; original proof reused.
theorem PartACanonical.Surface.m0372 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v5)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))) := by
  exact @RawFrontier.early_reject_sound

-- Independent literal expected type for RawFrontier.frontier_impossible.
noncomputable def PartACanonical.Types.p0624 :
(∀ (_v0 : (@Nat)),
(@Not (@RawFrontier.Target.Frontier _v0))) := by
  exact @RawFrontier.frontier_impossible

-- Complete literal proposition for RawFrontier.frontier_impossible; original proof reused.
theorem PartACanonical.Surface.m0373 :
(∀ (_v0 : (@Nat)),
(@Not (∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v6 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (16777216 : Nat) (@instOfNatNat (16777216 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v6)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (∀ (_v7 : (@Eq.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0)))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Bool.false)))))))))))))))) := by
  exact @RawFrontier.frontier_impossible

-- Independent literal expected type for RawFrontier.producer_reject_frontier.
noncomputable def PartACanonical.Types.p0625 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SmallIngress.producer)))),
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false))))))))))))))))) := by
  exact @RawFrontier.producer_reject_frontier

-- Complete literal proposition for RawFrontier.producer_reject_frontier; original proof reused.
theorem PartACanonical.Surface.m0374 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SmallIngress.producer)))),
(let _v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 _v8)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false))))))))))))))))) := by
  exact @RawFrontier.producer_reject_frontier

-- Independent literal expected type for RawFrontier.raw_stalls.
noncomputable def PartACanonical.Types.p0626 :
(∀ (_v0 : (@Nat)),
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))));
(let _v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))));
(@And (∀ (_v3 : (@Nat)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))))) (@Exists.{(0
  + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@OfNat.ofNat.{0} (@Nat) (73752 : Nat) (@instOfNatNat (73752 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine
  _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool)
  (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat)
  (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (15 : Nat) (@instOfNatNat
  (15 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)))))))))))) := by
  exact @RawFrontier.raw_stalls

-- Complete literal proposition for RawFrontier.raw_stalls; original proof reused.
theorem PartACanonical.Surface.m0375 :
(∀ (_v0 : (@Nat)),
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))));
(let _v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))));
(@And (∀ (_v3 : (@Nat)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))))) (@Exists.{(0
  + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@OfNat.ofNat.{0} (@Nat) (73752 : Nat) (@instOfNatNat (73752 : Nat)))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine
  _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool)
  (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat)
  (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v1 (@Fin.elim0.{(0 + 1)} (@Bool))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (15 : Nat) (@instOfNatNat
  (15 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)) (∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 _v2)))))))))))) := by
  exact @RawFrontier.raw_stalls

-- Independent literal expected type for RawFrontier.sample_relation_false.
noncomputable def PartACanonical.Types.p0627 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))))) (@Fin.elim0.{(0 +
  1)} (@Bool))) (@Bool.false))) := by
  exact @RawFrontier.sample_relation_false

-- Complete literal proposition for RawFrontier.sample_relation_false; original proof reused.
theorem PartACanonical.Surface.m0376 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat))
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))))) (@Fin.elim0.{(0 +
  1)} (@Bool))) (@Bool.false))) := by
  exact @RawFrontier.sample_relation_false

-- Independent literal expected type for RawFrontier.syntactic_reject.
noncomputable def PartACanonical.Types.p0628 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Or (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.false)) (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.none.{0} (@Nat))))),
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v7)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v7)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)}
  (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)) (@And (@Eq.{(0 + 1)} (∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4)) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))))))))))))))))) := by
  exact @RawFrontier.syntactic_reject

-- Complete literal proposition for RawFrontier.syntactic_reject; original proof reused.
theorem PartACanonical.Surface.m0377 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Or (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.false)) (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.none.{0} (@Nat))))),
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v7)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@AllArityCursor.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))))))) (@And (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v7)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@AllArityCursor.machine _v0))))) (@And (@Eq.{(0 + 1)}
  (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)) (@And (@Eq.{(0 + 1)} (∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4)) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v7 _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))))))))))))))))) := by
  exact @RawFrontier.syntactic_reject
