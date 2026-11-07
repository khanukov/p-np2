import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for FullFinalClosure.CanonicalC1.full_endpoint_mirror.
noncomputable def PartACanonical.Types.l0001 :
(∀ (_v0 : (@Nat)),
(@And (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@FullFinalClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@VirtualFinalClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@FullFinalClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@FullFinalClosure.runtimeBound
  _v0 _v1)) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v8)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v10 _v6) (@FullFinalClosure.configA _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v10 _v7))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v8)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v10 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v10 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)) (∀
  (_v12 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v13 : (@Fin (@OfNat.ofNat.{0} (@Nat) (144 : Nat) (@instOfNatNat (144 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v10 _v7)) (@VirtualFinalClosure.control _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0
  (@BodyIngress.body _v0 (@SerializedBody.entry _v12)))) _v13)))))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v10 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v5))
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5))))) (@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v9)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  _v10 _v6))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v3)))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v9 _v6)) (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@instDecidableEqBool (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v5) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v5))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v7)) (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@instDecidableEqBool (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)))) (@Exists.{(0 +
  1)} (@Nat) (fun (_v10 : (@Nat)) =>
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
(let _v18 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v19 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v17 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v15)) _v17));
(let _v20 : (@Nat) := (@Cursor.Target.W _v0 _v15);
(let _v21 : (@Nat) := (@Cursor.Target.M _v0 _v15 _v16);
(let _v22 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) := (@SerializedBody.sourceMode
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v11) (@Fin.append.{(0 + 1)} _v10
  _v11 (@Bool) _v12 _v13) _v21);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v10 _v11 _v16))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v17 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15)) _v18) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v16)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v15))
  _v17) _v17) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v15) _v19) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v20 _v19) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) _v15)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun
  (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) _v15) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(let _v24 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@FullFinalClosure.entryB
  _v0 _v22) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v16) _v15) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v23) (fun (_v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)))
  =>
(@SerializedBody.prepared (@FullFinalClosure.normalBase _v0 _v1 _v10 _v11 _v12 _v13 _v16 _v15) _v17 _v21 _v18 _v19 _v15
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v15 _v0) _v0) _v20 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) _v24))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v7) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@FullFinalClosure.entryA _v0 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3 _v24) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 _v24))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) _v6) (@FullFinalClosure.configB _v0 _v1 _v3 _v24)) (@Exists.{(0 + 1)} (@Nat) (fun (_v25 :
  (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) _v25)) (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v26 _v25)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v26) _v6) (@FullFinalClosure.configB _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v26
  _v24))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (@And (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@FullFinalClosure.allocation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))))) (@And (∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@FullFinalClosure.allocation _v0 _v1) (@Pnp3.Complexity.Uniform.V1.polyClock
  (@FullFinalClosure.degree _v0) _v1))) (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@FullFinalClosure.runtimeBound _v0 _v1)) (@And (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@FullFinalClosure.allocation _v0 _v1) _v4)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0)) _v1 (@FullFinalClosure.allocation _v0 _v1) _v4 _v5
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@FullFinalClosure.machine _v0) _v1 (@FullFinalClosure.allocation _v0 _v1)
  _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@FullFinalClosure.machine _v0) _v1 (@FullFinalClosure.allocation _v0
  _v1) _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@FullFinalClosure.machine _v0) _v1 _v4 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@FullFinalClosure.machine _v0) _v1 _v4 _v2))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))
  _v1 (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) _v1))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@FullFinalClosure.machine _v0) _v1 (@Pnp3.Complexity.Uniform.V1.polyClock
  (@FullFinalClosure.degree _v0) _v1) (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) _v1)
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@FullFinalClosure.machine _v0) _v1 (@Pnp3.Complexity.Uniform.V1.polyClock
  (@FullFinalClosure.degree _v0) _v1) _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@FullFinalClosure.machine _v0) _v1
  (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) _v1) _v3
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@FullFinalClosure.machine _v0) _v1 (@Pnp3.Complexity.Uniform.V1.polyClock
  (@FullFinalClosure.degree _v0) _v1) _v2))) (@And (@Pnp3.Complexity.Uniform.V1.DecidesAt (@FullFinalClosure.machine _v0)
  _v1 (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) _v1) (@Pnp3.Complexity.Uniform.V1.polyClock
  (@FullFinalClosure.degree _v0) _v1) _v2 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2))
  (@Pnp3.Complexity.Uniform.V1.DecidesWithin (@FullFinalClosure.machine _v0) _v1 (@Pnp3.Complexity.Uniform.V1.polyClock
  (@FullFinalClosure.degree _v0) _v1) _v2 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)))))))))))) (@And
  (@Pnp3.Complexity.Uniform.V1.VerifiesRelation (@FullFinalClosure.machine _v0) (@FullFinalClosure.degree _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0)) (@And (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v1 _v2) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v3 :
  (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v3) (fun (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@Pnp3.Complexity.Uniform.V1.polyClock (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) _v1)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v3 _v2 _v4)
  (@Bool.true)))))))))) (@And (@Pnp3.Complexity.Uniform.V1.UniformNP
  (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@And
  (@UniformClassBridgeClosure.Ordinary.Verifies (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) (@Option.some.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))
  (@UniformClassBridgeClosure.Ordinary.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))))))))) := by
  exact @FullFinalClosure.CanonicalC1.full_endpoint_mirror

-- Independent literal expected type for FullFinalClosure.CanonicalC1.mirror_has_full_target.
noncomputable def PartACanonical.Types.l0002 :
(∀ (_v0 : (@Nat)),
(@FullFinalClosure.Target.Full _v0)) := by
  exact @FullFinalClosure.CanonicalC1.mirror_has_full_target

-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_AcceptedBody_clock_bound.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0003 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v0)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Body.iterClock (@List.replicate.{0} (@Bool) _v1 (@Bool.false)) _v2)) (@AcceptedBody.deadline _v0))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_AcceptedBody_concat_eq_append.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0004 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Eq.{(0 + 1)} (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1)) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.concatV1ToPrefixBitVec _v0 _v1 _v2 _v3)
  (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_AcceptedBody_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0005 :
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
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v8)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v8)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownDeadline (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2))) (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))))),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@Body.iterClock (@List.replicate.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) (@Bool.false)) _v10)) (@AcceptedBody.deadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (let _v12 : (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Body.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@Body.iterClock (@List.replicate.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) (@Bool.false)) _v10))
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@Body.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)));
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Body.machine) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Body.Target.Span (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@Body.iterBits
  (@List.replicate.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@Bool.false)) _v10)) (∀ (_v13 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (8 : Nat) (@instOfNatNat (8 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2))) _v13))),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v13) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 _v13) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4 (@Fin.mk (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v13) _v15))))))))))))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_AcceptedBody_strict_capacity.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0006 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v2))),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v0 _v1 _v2)))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_AcceptedBody_table_support.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0007 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec _v1)),
(∀ {_v3 : (@AcceptedBody.Parsed _v0)},
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v4 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v4))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v1 _v2) (@Option.some.{0} (@AcceptedBody.Parsed _v0) _v3))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v1 _v2) (@Bool.true))),
(@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))) _v3)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))) _v3))) _v1))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Edge_after.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0008 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Edge_before.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0009 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Edge_move.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0010 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest (@Body.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1) (@Body.Node.tape _v1 (@Body.Node.head
  _v1)))))) (@Body.Node.head _v2)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Edge_row.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0011 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))) (@Body.Node.state _v2)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Edge_tape.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0012 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.Node.tape _v2) (@Body.put (@Body.Node.tape _v1) (@Body.Node.head _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Path_append.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0013 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ {_v5 : (@Body.Node)},
(∀ (_v6 : (@Body.Path _v0 _v1 _v3 _v4)),
(∀ (_v7 : (@Body.Path _v0 _v2 _v4 _v5)),
(@Body.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3
  _v5))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Path_bounds.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0014 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (@Body.Node)},
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0) (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v3)
  _v0))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_Path_execute.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0015 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Body.Node)},
(∀ {_v5 : (@Body.Node)},
(∀ (_v6 : (@Body.Path _v2 _v3 _v4 _v5)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Body.machine) _v0 _v1 _v3 (@Body.embed _v0 _v1 _v4
  (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@Body.Node.head _v4) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) (@And.left (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v4) _v2) (@LE.le.{0} (@Nat) (@instLENat)
  (@Body.Node.head _v5) _v2) (@Body.Path.bounds _v2 _v3 _v4 _v5 _v6)) _v7))) (@Body.embed _v0 _v1 _v5 (@lt_of_le_of_lt.{0}
  (@Nat) (@Nat.instPreorder) (@Body.Node.head _v5) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@And.right
  (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v4) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v5) _v2)
  (@Body.Path.bounds _v2 _v3 _v4 _v5 _v6)) _v7))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_carry_frame.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0016 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Or (@LE.le.{0} (@Nat) (@instLENat) _v3 _v1) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.carryTape _v0 _v1 _v2 _v3) (@_v0 _v3))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_carry_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0017 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@List.{0} (@Bool))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) _v2) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v6 : (@Body.Reads _v0 _v1 _v3)),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) _v7)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) _v2) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v10 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v7) (@Option.some.{0} (@Bool) _v10)))))))),
(@Body.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Body.carryClock _v3 _v2) (@Body.Node.mk (@Body.q (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) _v0)
  (@Body.Node.mk (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)}
  (@Bool) (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3)) (@Bool.true)) (@instDecidableEqBool
  (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3)) (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@Body.machine)) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool)
  (@Body.inc _v3)) (@Bool.true)) (@instDecidableEqBool (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3))
  (@Bool.true)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) _v2) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Body.carryTape _v0 _v1 _v3))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_carry_reads.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0018 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Body.Reads _v0 _v1 _v2)),
(@Body.Reads (@Body.carryTape _v0 _v1 _v2) _v1 (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v2))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_clear_step.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0019 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.clear (@Body.put _v0 _v1 (@Option.some.{0} (@Bool) (@Bool.false))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) _v2) (@Body.clear _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_extend_read.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0020 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.extend _v0 _v1 _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v3)) (@_v2 _v3)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_first_accept_whole.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0021 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v4 _v3) _v5)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v5)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 _v4) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v3)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v3) _v5))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_good_of_lt.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0022 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Body.value _v0) _v1) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@List.length.{0} (@Bool) _v0)))),
(@Body.Good _v0 _v1)))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_hop.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0023 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v6 : (@Option.{0} (@Bool))),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Move)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v0)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v0)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Body.machine) _v1 (@_v5 _v3)) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v2 (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) _v6 _v7)))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) (@Body.dest _v3 _v7) _v4)),
(@Body.Path _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@Body.Node.mk _v1 _v3 _v5) (@Body.Node.mk
  _v2 _v4 (@Body.put _v5 _v3 _v6))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_inc_length.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0024 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Bool) (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0)))
  (@List.length.{0} (@Bool) _v0))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_inc_value.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0025 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Body.value
  (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool)
  (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0)) (@Bool.true)) (@instDecidableEqBool (@Prod.snd.{0, 0}
  (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0)) (@Bool.true)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@List.length.{0} (@Bool) _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Body.value _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_install_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0026 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0
  _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Body.machine)))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v4)) _v2)),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v2 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v2
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun
  (_v8 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartABodySurfaceTests.check_Body_install_exact._proof_1 _v0 _v1 _v2 _v3 _v4 _v7 _v8))))) (@Option.none.{0}
  (@Bool)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5)) (@Option.none.{0} (@Bool)))),
(∀ (_v10 : (∀ (_v10 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v10))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v10)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4 _v10) (@Option.some.{0} (@Bool)
  (@Bool.true))))))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Body.machine) _v0 _v1 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) _v4) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))
  _v0 _v1 (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5) (@Body.installedTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4)
  _v2 _v3))) (@Body.Target.Span _v0 _v1 (@Body.installedTape _v0 _v1 (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4) _v2 _v3) _v2 (@List.replicate.{0}
  (@Bool) _v3 (@Bool.false))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_install_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0027 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v4)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v4) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(@Body.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat)))) (@Body.Node.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Body.machine)) _v1 _v0)
  (@Body.Node.mk (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Body.clear _v0 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v2))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_iter_clock_le.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0028 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.iterClock _v0 _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@List.length.{0} (@Bool) _v0)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_iter_length.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0029 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Bool) (@Body.iterBits _v0 _v1)) (@List.length.{0} (@Bool) _v0)))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_put_same.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0030 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.put _v0 _v1 (@_v0 _v1)) _v0))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_raw_counter_parsed.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0031 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ {_v5 : (@Sigma.{0, 0} (@Nat) (fun (_v5 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v5))))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6)))) _v5))),
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
(let _v9 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v5)) (@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v10)) (∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v5))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v10))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9))
  (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v9))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownDeadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (let _v14 : (∀ (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9))),
(@Option.{0} (@Bool))) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2 _v9 _v3 _v4 _v10
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5)));
(let _v15 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2) _v9 (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) _v13) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v14
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5))));
(@And (@Body.Target.Span (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v15) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v10) (@List.replicate.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) (@Bool.false))) (@And (∀ (_v16 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9))),
(∀ (_v17 : (@Or (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) _v16) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v10)) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v9) _v16)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2) _v9 _v15 _v16) (@_v14 _v16)))) (∀ (_v16 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Body.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v16) (@Pnp3.Complexity.Uniform.V1.initialConfig (@Body.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v3 _v4))) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) (@Body.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Body.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v16 _v15))))))))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_raw_repeated_parsed.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0032 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ {_v5 : (@Sigma.{0, 0} (@Nat) (fun (_v5 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v5))))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6)))) _v5))),
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
(let _v9 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v10)) (∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v11 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v5))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v10))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownDeadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5))))),
(let _v15 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) := (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Body.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@Body.iterClock (@List.replicate.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5)) (@Bool.false)) _v13))
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@Body.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v9 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)));
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v15) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) (@Body.machine) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v15)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Body.Target.Span (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v15) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v10) (@Body.iterBits (@List.replicate.{0} (@Bool)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) (@Bool.false)) _v13)) (∀ (_v16 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9))),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (8 : Nat) (@instOfNatNat (8 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v9) _v16))),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) _v16) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v15 _v16) (@Option.some.{0} (@Bool) (@Fin.append.{(0
  + 1)} _v1 _v2 (@Bool) _v3 _v4 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v1 _v2) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v9) _v16) _v18))))))))))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_raw_source_after_header.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0033 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Nat)},
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Nat) _v3))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v0 _v1 _v3))),
(∀ (_v10 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (8 : Nat) (@instOfNatNat (8 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1) _v2) _v10))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v10) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1 _v2 _v5 _v6
  _v3 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4 _v10) (@Option.some.{0} (@Bool) (@Fin.append.{(0 +
  1)} _v0 _v1 (@Bool) _v5 _v6 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  _v1) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2) _v10) _v12))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_reads_cons.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0034 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Bool)),
(∀ (_v3 : (@List.{0} (@Bool))),
(@Iff (@Body.Reads _v0 _v1 (@List.cons.{0} (@Bool) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Body.Reads _v0 _v1 _v3))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_reads_put_outside.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0035 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Body.Reads _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Option.{0} (@Bool))),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) _v4)),
(@Body.Reads (@Body.put _v0 _v4 _v5) _v1 _v2)))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_repeated_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0036 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@List.{0} (@Bool))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0
  _v1)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@List.length.{0}
  (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v5) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v5)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@List.length.{0} (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v9 : (@Body.Target.Span _v0 _v1 (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v5) _v2 _v3)),
(∀ (_v10 : (@Body.Good _v3 _v4)),
(let _v11 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0
  _v1) := (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Body.machine) _v0 _v1 (@Body.iterClock _v3 _v4) _v5);
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v11) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v11)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@List.length.{0} (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Body.Target.Span _v0 _v1 (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine)) _v0 _v1 _v11) _v2 (@Body.iterBits _v3 _v4)) (∀ (_v12 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v1))),
(∀ (_v13 : (@Or (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v12) _v2)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@List.length.{0} (@Bool) _v3)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v12)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v11 _v12)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v5
  _v12))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_round_clock_le.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0037 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.roundClock _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@List.length.{0} (@Bool) _v0)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_round_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0038 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@List.{0} (@Bool))),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0
  _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@List.length.{0}
  (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v4) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v4)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@List.length.{0} (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v8 : (@Body.Target.Span _v0 _v1 (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4) _v2 _v3)),
(let _v9 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0
  _v1) := (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Body.machine) _v0 _v1 (@Body.roundClock _v3) _v4);
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1
  _v9) (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Eq.{(0 + 1)} (@Bool)
  (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3)) (@Bool.true)) (@instDecidableEqBool (@Prod.snd.{0, 0}
  (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3)) (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Body.machine)) (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v9)) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)}
  (@Bool) (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3)) (@Bool.true)) (@instDecidableEqBool
  (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v3)) (@Bool.true)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@List.length.{0} (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@And (@Body.Target.Span _v0 _v1 (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v9) _v2 (@Prod.fst.{0, 0} (@List.{0}
  (@Bool)) (@Bool) (@Body.inc _v3))) (∀ (_v10 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v11 : (@Or (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v10) _v2)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@List.length.{0} (@Bool) _v3)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v10)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v9 _v10)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine)) _v0 _v1 _v4
  _v10))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_round_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0039 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0}
  (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v5 : (@Body.Reads _v0 _v1 _v2)),
(@Body.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) (@Body.roundClock _v2) (@Body.Node.mk (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v0) (@Body.Node.mk (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) (@Prod.snd.{0, 0} (@List.{0}
  (@Bool)) (@Bool) (@Body.inc _v2)) (@Bool.true)) (@instDecidableEqBool (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool)
  (@Body.inc _v2)) (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@Body.machine)) (@Body.q (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Prod.snd.{0, 0} (@List.{0}
  (@Bool)) (@Bool) (@Body.inc _v2)) (@Bool.true)) (@instDecidableEqBool (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool)
  (@Body.inc _v2)) (@Bool.true)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@List.length.{0} (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Body.carryTape _v0 _v1
  _v2))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_seed_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0040 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v3) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2)) (@Option.none.{0} (@Bool)))),
(@Body.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Body.Node.mk (@Body.q (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1 _v0) (@Body.Node.mk
  (@Body.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Body.clear _v0 _v1 _v2)))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_sweep.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0041 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v6 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v3) (@Option.some.{0} (@Bool) _v6)))))))),
(@Body.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v2 (@Body.Node.mk
  (@Body.q (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v1 _v0) (@Body.Node.mk (@Body.q
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v0)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_value_lt.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0042 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Body.value _v0) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@List.length.{0} (@Bool) _v0)))))
end
-- Independent literal expected type for Pnp3.Tests.PartABodySurfaceTests.check_Body_zero_value.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0043 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.replicate.{0} (@Bool) _v0 (@Bool.false))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))))
end
-- Independent literal expected type for Pnp3.Tests.PartACanonicalApiSmoke.check_countdown_geometry.
noncomputable def PartACanonical.Types.l0044 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v3))),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v2)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v0 _v1 _v3))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2)))))))))))) := by
  exact @Pnp3.Tests.PartACanonicalApiSmoke.check_countdown_geometry

-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Edge_after.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0045 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Edge_before.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0046 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Edge_move.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0047 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest (@InputRead.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1
  (@InputRead.Node.head _v1)))))) (@InputRead.Node.head _v2)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Edge_row.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0048 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))) (@InputRead.Node.state _v2)))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Edge_tape.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0049 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.Node.tape _v2) (@InputRead.put (@InputRead.Node.tape _v1) (@InputRead.Node.head _v1)
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Path_append.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0050 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ {_v5 : (@InputRead.Node)},
(∀ (_v6 : (@InputRead.Path _v0 _v1 _v3 _v4)),
(∀ (_v7 : (@InputRead.Path _v0 _v2 _v4 _v5)),
(@InputRead.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3
  _v5))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Path_bounds.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0051 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (@InputRead.Node)},
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0) (@LE.le.{0} (@Nat) (@instLENat)
  (@InputRead.Node.head _v3) _v0))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_Path_execute.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0052 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@InputRead.Node)},
(∀ {_v5 : (@InputRead.Node)},
(∀ (_v6 : (@InputRead.Path _v2 _v3 _v4 _v5)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@InputRead.machine) _v0 _v1 _v3
  (@InputRead.embed _v0 _v1 _v4 (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@InputRead.Node.head _v4) _v2
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@And.left (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v4)
  _v2) (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v5) _v2) (@InputRead.Path.bounds _v2 _v3 _v4 _v5 _v6))
  _v7))) (@InputRead.embed _v0 _v1 _v5 (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@InputRead.Node.head _v5) _v2
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@And.right (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v4)
  _v2) (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v5) _v2) (@InputRead.Path.bounds _v2 _v3 _v4 _v5 _v6))
  _v7))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_accepted_cursor.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0053 :
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
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v8)) (∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Exists.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (fun (_v12 : (@Fin
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@InputRead.readClock (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8))))) (@InputRead.stageDeadline
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v12) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@And (∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Eq.{(0 + 1)} (@Bool) (@InputRead.result _v12) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4 (@Fin.mk (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) _v13)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@InputRead.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@InputRead.readClock (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8))))) (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@InputRead.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@InputRead.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@InputRead.ready _v12) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) _v11) (fun (_v13 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v13) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9
  : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v13) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9
  : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8))) (@Option.none.{0} (@Bool)) (@Body.installedTape
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v3 _v4 _v8 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) _v13))))))))))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0054 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))
  _v0 _v1)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v3)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0
  _v1 _v6) (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1
  _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))
  (@Nat.decLt (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v12 : (@Not (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact._proof_1 _v0 _v1 _v2 _v3 _v4 _v5 _v7 _v8 _v9
  _v12))))) (@Option.none.{0} (@Bool)))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))
  (@Nat.decLt (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v13 : (@Not (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact._proof_2 _v0 _v1 _v2 _v3 _v4 _v5 _v7 _v8 _v9
  _v13))))) (@Option.some.{0} (@Bool) (@Bool.true)))),
(∀ (_v14 : (∀ (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v14))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v14) _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 _v14) (@Option.some.{0} (@Bool)
  _v17)))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun
  (_v15 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact._proof_3 _v0 _v1 _v2 _v3 _v4 _v5 _v9 _v15)))))
  (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v16))),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v16)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 _v16) (@Option.some.{0} (@Bool)
  (@Bool.false))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))
  (fun (_v17 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact._proof_4 _v0 _v1 _v2 _v3 _v4 _v5 _v9 _v17)))))
  (@Option.none.{0} (@Bool)))),
(∀ (_v18 : (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v18))),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v18)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v21 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 _v18) (@Option.some.{0} (@Bool)
  _v21)))))))),
(∀ (_v19 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v9)) (@Option.none.{0} (@Bool)))),
(@Exists.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (fun (_v20 : (@Fin
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) =>
(@And (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v2 _v3)) (@And (∀ (_v21 :
  (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v2 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v2
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun
  (_v22 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact._proof_5 _v0 _v1 _v2 _v3 _v4 _v5 _v8 _v9 _v22)))))
  (@Option.some.{0} (@Bool) (@InputRead.result _v20)))) (let _v21 : (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@InputRead.machine) _v0 _v1 (@InputRead.readClock _v5 _v4 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v3 _v2)) _v6);
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0
  _v1 _v21) (@InputRead.ready _v20)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1
  _v21) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))
  _v0 _v1 _v6)) (@And (∀ (_v22 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v21 _v22) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v22) _v2)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v22) _v2) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1
  _v6 _v22)))) (∀ (_v22 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v22) _v2) (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)) (@instDecidableAnd
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v22) _v2) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v2 _v3) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v22) _v2)
  (@Nat.decLt _v2 _v3)) (@Option.some.{0} (@Bool) (@InputRead.result _v20)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v21 _v22))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1
  _v6 _v22))))))))))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_hop.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0055 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v6 : (@Option.{0} (@Bool))),
(∀ (_v7 : (@Pnp3.Complexity.Uniform.V1.Move)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v0)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v0)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) _v1 (@_v5 _v3)) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 :
  Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v2 (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) _v6 _v7)))),
(∀ (_v11 : (@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v3 _v7) _v4)),
(@InputRead.Path _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@InputRead.Node.mk _v1 _v3 _v5)
  (@InputRead.Node.mk _v2 _v4 (@InputRead.put _v5 _v3 _v6))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_install_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0056 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))
  _v0 _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0
  _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@InputRead.machine)))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1
  _v4)) _v2)),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v4 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v2 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v2
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun
  (_v8 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_install_exact._proof_1 _v0 _v1 _v2 _v3 _v4 _v7 _v8)))))
  (@Option.none.{0} (@Bool)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v4 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5)) (@Option.none.{0} (@Bool)))),
(∀ (_v10 : (∀ (_v10 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v10))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v10)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v4 _v10) (@Option.some.{0} (@Bool)
  (@Bool.true))))))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@InputRead.machine) _v0 _v1 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v4) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine)) _v0 _v1 (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5) (@Body.installedTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1
  _v4) _v2 _v3)))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_install_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0057 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v4)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v4) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(@InputRead.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@InputRead.Node.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.start
  (@InputRead.machine)) _v1 _v0) (@InputRead.Node.mk (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Body.clear _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v2))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_keep.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0058 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Move)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v0)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v0)),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) _v1 (@_v5 _v3)) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 :
  Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v2 (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@_v5 _v3) _v6)))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v3 _v6) _v4)),
(@InputRead.Path _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@InputRead.Node.mk _v1 _v3 _v5)
  (@InputRead.Node.mk _v2 _v4 _v5))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_put_same.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0059 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.put _v0 _v1 (@_v0 _v1)) _v0))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_raw_cursor_parsed.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0060 :
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
(let _v9 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2));
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v10)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v11
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownDeadline (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2))) (∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v12 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v5))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v1 _v2 _v10))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9))
  (fun (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v9))) =>
(@Exists.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (fun (_v15 : (@Fin
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) =>
(@And (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v15)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v10)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))) (@And (∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))),
(@Eq.{(0 + 1)} (@Bool) (@InputRead.result _v15) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4 (@Fin.mk (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v10)) _v16)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@InputRead.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@InputRead.readClock (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) _v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10))))) (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@InputRead.rawMachine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@InputRead.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 (@InputRead.ready _v15) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) _v14) (fun (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) _v16) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v10))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9) _v16) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v10))) (@Option.none.{0} (@Bool)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v9 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v1 _v2 _v9 _v3 _v4 _v10 (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v10) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) _v16))))))))))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_read_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0061 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.true)))),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v9)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v12 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v9) (@Option.some.{0} (@Bool) _v12)))))))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v11)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v11) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v13)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v16 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v13) (@Option.some.{0} (@Bool) _v16)))))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(@Exists.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (fun (_v15 : (@Fin
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) =>
(@And (@Iff (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v15)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v1 _v2)) (@And (∀ (_v16 :
  (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.some.{0} (@Bool) (@InputRead.result _v15)))) (@InputRead.Path
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.readClock _v4
  _v3 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v1)) (@InputRead.Node.mk
  (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v0) (@InputRead.Node.mk (@InputRead.ready _v15) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.put _v0 _v1 (@Option.none.{0}
  (@Bool)))))))))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_return_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0062 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v5) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v7)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v10 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v7) (@Option.some.{0} (@Bool) _v10)))))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(@InputRead.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.Node.mk
  (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v0) (@InputRead.Node.mk (@InputRead.ready _v4)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v0))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_return_rows.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0063 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@And (∀ (_v1 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v0)))) (@Option.some.{0} (@Bool) _v1)) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (8 : Nat) (@instOfNatNat (8 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.some.{0} (@Bool) _v1) (@Pnp3.Complexity.Uniform.V1.Move.right))))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.q
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 :
  Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@InputRead.q
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.q
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Option.some.{0} (@Bool) (@Bool.false))) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.some.{0} (@Bool) (@Bool.false)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (@Eq.{(0 + 1)} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.q
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 :
  Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@InputRead.q
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat)
  (@instOfNatNat (10 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v0)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.right)))) (@And (∀ (_v1 : (@Bool)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0)))) (@Option.some.{0} (@Bool) _v1)) (@Prod.mk.{0, 0}
  (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v1) (@Pnp3.Complexity.Uniform.V1.Move.right))))) (@Eq.{(0
  + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) (@InputRead.q (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0)))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@InputRead.ready _v0) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay)))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_seed_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0064 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v3) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2)) (@Option.none.{0} (@Bool)))),
(@InputRead.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@InputRead.Node.mk (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) _v1 _v0) (@InputRead.Node.mk (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Body.clear _v0 _v1
  _v2)))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_seek_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0065 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.true)))),
(∀ (_v9 : (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v9)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v12 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v9) (@Option.some.{0} (@Bool) _v12)))))))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v11)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v11) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v13)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v16 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v13) (@Option.some.{0} (@Bool) _v16)))))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(@InputRead.Path (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v3)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v1)) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@InputRead.Node.mk (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v0) (@InputRead.Node.mk
  (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) _v1 _v0))))))))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_stage_clock.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0066 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v0)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v0)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@InputRead.readClock _v1 _v2 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v3 _v4)))
  (@InputRead.stageDeadline _v0)))))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_sweepL.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0067 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v0)),
(∀ (_v6 : (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v6)),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) _v6 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) _v1 (@_v2 _v6)) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 :
  Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v1 (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@_v2 _v6) (@Pnp3.Complexity.Uniform.V1.Move.left)))))))),
(@InputRead.Path _v0 _v4 (@InputRead.Node.mk _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@InputRead.Node.mk _v1 _v3 _v2))))))))))
end
-- Independent literal expected type for Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_sweepR.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.l0068 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v0)),
(∀ (_v6 : (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v6)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@InputRead.machine) _v1 (@_v2 _v6)) (@Prod.mk.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 :
  Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v1 (@Prod.mk.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@_v2 _v6) (@Pnp3.Complexity.Uniform.V1.Move.right)))))))),
(@InputRead.Path _v0 _v4 (@InputRead.Node.mk _v1 _v3 _v2) (@InputRead.Node.mk _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2))))))))))
end
